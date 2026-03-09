#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Passes/OptimizationLevel.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <vector>

using namespace llvm;

namespace {

// Deterministic hashing is REQUIRED so the Web Worker .o caching works!
// (llvm::hash_value is randomized per-process and would break cache hits)
uint32_t hashStringNova(StringRef Str) {
  uint32_t Hash = 2166136261u;
  for (char C : Str) {
    Hash ^= (uint8_t)C;
    Hash *= 16777619u;
  }
  return Hash;
}

std::string deriveStepMapPath(StringRef sourceFile) {
  std::string name = sourceFile.str();
  if (name.empty())
    name = "unknown";

  std::string flat;
  for (char c : name) {
    flat += (c == '/') ? '_' : c;
  }
  if (!flat.empty() && flat[0] == '_')
    flat = flat.substr(1);

  auto pos = flat.rfind(".cpp");
  if (pos != std::string::npos) {
    flat = flat.substr(0, pos) + ".stepmap.json";
  } else {
    flat += ".stepmap.json";
  }
  return "/workspace/" + flat;
}

// Cleanly isolate platform-specific IDE exclusions
bool isNovaRuntime(StringRef Name) {
  return Name.starts_with("JS_") || Name == "clear_screen" ||
         Name == "draw_circle" || Name == "render_frame" || Name == "malloc" ||
         Name == "free" || Name == "__wrap_malloc" || Name == "__wrap_free";
}

bool isUserSourceFile(StringRef file) {
  return file.contains("workspace") || file.contains("main.cpp");
}

// Safely bypass all variable allocations to protect the WASM shadow stack
Instruction *getSafeInsertionPoint(BasicBlock &BB) {
  auto InsertPt = BB.getFirstInsertionPt();
  while (InsertPt != BB.end() &&
         (isa<AllocaInst>(&*InsertPt) || isa<DbgInfoIntrinsic>(&*InsertPt))) {
    ++InsertPt;
  }
  return InsertPt == BB.end() ? nullptr : &*InsertPt;
}

// Memory-safe struct to hold StepMap entries before streaming
struct StepMapEntry {
  uint32_t stepId;
  int line;
  std::string func;
  std::string file;
};

struct NovaDebugPass : public PassInfoMixin<NovaDebugPass> {
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
    LLVMContext &Ctx = M.getContext();
    auto *StepType =
        FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx)}, false);
    auto StepFn = M.getOrInsertFunction("JS_debug_step", StepType);

    auto *NotifyEnterType = FunctionType::get(Type::getVoidTy(Ctx), {}, false);
    auto NotifyEnterFn =
        M.getOrInsertFunction("JS_notify_enter", NotifyEnterType);

    auto *NotifyExitType = FunctionType::get(Type::getVoidTy(Ctx), {}, false);
    auto NotifyExitFn = M.getOrInsertFunction("JS_notify_exit", NotifyExitType);

    // Fast-Check: Skip modules that do not contain any user code
    bool hasUserCode = false;
    for (Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (const DebugLoc &DL = I.getDebugLoc()) {
            if (isUserSourceFile(DL->getFilename())) {
              hasUserCode = true;
              break;
            }
          }
        }
        if (hasUserCode)
          break;
      }
      if (hasUserCode)
        break;
    }

    if (!hasUserCode)
      return PreservedAnalyses::all();

    bool changed = false;
    std::vector<StepMapEntry> StepMap;

    // 14 bits for fileId (16,384 files), 17 bits for Instruction (131,072 per
    // file). This perfectly fits in 31 bits, guaranteeing it never hits the JS
    // Int32 sign bit!
    uint32_t fileId = hashStringNova(M.getSourceFileName()) & 0x3FFF;
    uint32_t instructionCounter = 0;

    for (Function &F : M) {
      StringRef FName = F.getName();

      if (F.isDeclaration() || isNovaRuntime(FName) ||
          (FName.starts_with("__") && FName != "__original_main"))
        continue;

      bool isUserFunc = false;
      DebugLoc FirstValidDL;

      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (const DebugLoc &DL = I.getDebugLoc()) {
            if (!FirstValidDL)
              FirstValidDL = DL;
            if (isUserSourceFile(DL->getFilename())) {
              isUserFunc = true;
            }
          }
        }
      }
      if (!isUserFunc)
        continue;

      // Use LLVM's native C++ demangler
      std::string cleanFuncName = FName.str();
      if (cleanFuncName == "__original_main") {
        cleanFuncName = "main";
      } else {
        std::string demangled = demangle(cleanFuncName);
        if (!demangled.empty()) {
          // Strip parameters for a cleaner UI (e.g.,
          // "Node::doubleValues(Node*)" -> "Node::doubleValues")
          auto parenPos = demangled.find('(');
          if (parenPos != std::string::npos) {
            cleanFuncName = demangled.substr(0, parenPos);
          } else {
            cleanFuncName = demangled;
          }
        }
      }

      DISubprogram *SP = F.getSubprogram();
      DebugLoc FuncDL;
      if (SP)
        FuncDL = DILocation::get(Ctx, SP->getLine(), 0, SP);

      // 1. INJECT ENTER HOOK (Safely skips alloca instructions)
      if (!F.empty()) {
        if (Instruction *SafeInsertPt =
                getSafeInsertionPoint(F.getEntryBlock())) {
          IRBuilder<> Builder(SafeInsertPt);

          if (SafeInsertPt->getDebugLoc())
            Builder.SetCurrentDebugLocation(SafeInsertPt->getDebugLoc());
          else if (FirstValidDL)
            Builder.SetCurrentDebugLocation(FirstValidDL);
          else if (FuncDL)
            Builder.SetCurrentDebugLocation(FuncDL);

          Builder.CreateCall(NotifyEnterFn);
          changed = true;
        }
      }

      DebugLoc LastValidDL = FirstValidDL ? FirstValidDL : FuncDL;

      for (BasicBlock &BB : F) {
        int lastLine = -1;
        for (auto it = BB.begin(); it != BB.end();) {
          Instruction &I = *it++;

          if (I.getDebugLoc())
            LastValidDL = I.getDebugLoc();

          // Skip AllocaInst to protect the WebAssembly shadow stack
          if (isa<PHINode>(&I) || I.isEHPad() || isa<AllocaInst>(&I))
            continue;

          // 2. INJECT STEP HOOK
          if (const DebugLoc &DL = I.getDebugLoc()) {
            int line = DL.getLine();
            StringRef file = DL->getFilename();

            if (line > 0 && line != lastLine && isUserSourceFile(file)) {
              lastLine = line;
              instructionCounter++;

              std::string filePath = file.str();
              if (filePath.find("/workspace/") != 0 &&
                  filePath.find("./") == 0) {
                filePath = "/workspace/" + filePath.substr(2);
              } else if (filePath.find("/workspace/") != 0) {
                filePath = "/workspace/" + filePath;
              }

              uint32_t stepId = (fileId << 17) | (instructionCounter & 0x1FFFF);

              IRBuilder<> StepBuilder(&I);
              StepBuilder.SetCurrentDebugLocation(DL);
              StepBuilder.CreateCall(StepFn, {StepBuilder.getInt32(stepId)});
              changed = true;

              // Store locally to safely emit JSON later
              StepMap.push_back({stepId, line, cleanFuncName, filePath});
            }
          }

          // 3. INJECT EXIT HOOK (Handles Returns AND Exception Unwinding)
          if (isa<ReturnInst>(&I) || isa<ResumeInst>(&I)) {
            Instruction *InsertPt = &I;

            // Prevent Verifier abort on MustTail calls
            if (auto *Prev = I.getPrevNode()) {
              if (auto *CB = dyn_cast<CallBase>(Prev)) {
                if (CB->isMustTailCall())
                  InsertPt = Prev;
              }
            }

            IRBuilder<> ExitBuilder(InsertPt);
            if (InsertPt->getDebugLoc())
              ExitBuilder.SetCurrentDebugLocation(InsertPt->getDebugLoc());
            else if (LastValidDL)
              ExitBuilder.SetCurrentDebugLocation(LastValidDL);

            ExitBuilder.CreateCall(NotifyExitFn);
            changed = true;
          }
        }
      }
    }

    // Native LLVM JSON Streaming
    std::string stepMapPath = deriveStepMapPath(M.getSourceFileName());
    std::error_code EC;
    raw_fd_ostream OS(stepMapPath, EC, sys::fs::OF_None);

    if (EC) {
      errs() << "NovaDebugPass Error: Failed to open step map for writing: "
             << EC.message() << "\n";
    } else {
      llvm::json::OStream J(OS);
      J.object([&] {
        for (const auto &Entry : StepMap) {
          J.attributeObject(std::to_string(Entry.stepId), [&] {
            J.attribute("line", Entry.line);
            J.attribute("func", Entry.func);
            J.attribute("file", Entry.file);
          });
        }
      });

      OS.flush();

      // Acknowledge WASI file closure errors so the WebWorker doesn't crash
      if (OS.has_error()) {
        errs() << "NovaDebugPass Warning: WASI encountered a flush error on "
               << stepMapPath << "\n";
        OS.clear_error();
      }
    }

    return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};
} // namespace

// ── Static Registration ──────────────────────────────────────────────
extern "C" ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "NovaDebugPass", "v1", [](PassBuilder &PB) {
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                  // NATIVE TOGGLE: Only inject the debugger hooks if
                  // optimizations are disabled (-O0). This ensures Release mode
                  // (-O2) runs at full native speed without debugger overhead!
                  if (Level == OptimizationLevel::O0) {
                    MPM.addPass(NovaDebugPass());
                  }
                });
          }};
}
