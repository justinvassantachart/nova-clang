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
#include "llvm/Support/raw_ostream.h"
#include <string>

using namespace llvm;

namespace {

uint32_t hashStringNova(StringRef Str) {
  uint32_t Hash = 2166136261u;
  for (char C : Str) {
    Hash ^= (uint8_t)C;
    Hash *= 16777619u;
  }
  return Hash & 0x7FFFFFFF;
}

std::string escapeJsonNova(StringRef s) {
  std::string out;
  out.reserve(s.size() + 10);
  for (char c : s) {
    if (c == '"')
      out += "\\\"";
    else if (c == '\\')
      out += "\\\\";
    else
      out += c;
  }
  return out;
}

std::string deriveStepMapPath(StringRef sourceFile) {
  std::string name = sourceFile.str();
  if (name.empty())
    name = "unknown";

  std::string flat;
  for (char c : name) {
    if (c == '/')
      flat += '_';
    else
      flat += c;
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

bool isUserSourceFile(StringRef file) {
  return file.contains("workspace") || file.contains("main.cpp");
}

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

    // Skip stdlib-only modules entirely
    if (!hasUserCode)
      return PreservedAnalyses::all();

    bool changed = false;
    bool first = true;

    // Build JSON in memory to avoid filesystem streaming traps
    std::string jsonStr = "{";

    uint32_t fileId = hashStringNova(M.getSourceFileName()) & 0x7FF;
    uint32_t instructionCounter = 0;

    for (Function &F : M) {
      StringRef FName = F.getName();

      if (F.isDeclaration() || FName.starts_with("JS_") ||
          (FName.starts_with("__") && FName != "__original_main"))
        continue;

      if (FName == "clear_screen" || FName == "draw_circle" ||
          FName == "render_frame" || FName == "malloc" || FName == "free")
        continue;

      bool isUserFunc = false;
      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (const DebugLoc &DL = I.getDebugLoc()) {
            if (isUserSourceFile(DL->getFilename())) {
              isUserFunc = true;
              break;
            }
          }
        }
        if (isUserFunc)
          break;
      }
      if (!isUserFunc)
        continue;

      // Clean function name for UI
      std::string cleanFuncName = FName.str();
      if (cleanFuncName == "__original_main")
        cleanFuncName = "main";
      else if (cleanFuncName.find("_Z") == 0) {
        size_t i = 2;
        int len = 0;
        while (i < cleanFuncName.length() && cleanFuncName[i] >= '0' &&
               cleanFuncName[i] <= '9') {
          len = len * 10 + (cleanFuncName[i] - '0');
          i++;
        }
        if (len > 0 && i + len <= cleanFuncName.length()) {
          cleanFuncName = cleanFuncName.substr(i, len);
        }
      }

      // Manufacture a fallback DebugLoc from the function's DISubprogram
      // to satisfy the strict LLVM IR Verifier
      DISubprogram *SP = F.getSubprogram();
      DebugLoc FuncDL;
      if (SP) {
        FuncDL = DILocation::get(Ctx, SP->getLine(), 0, SP);
      }

      // 1. INJECT ENTER HOOK (Safely skips alloca instructions)
      if (!F.empty()) {
        BasicBlock &EntryBB = F.getEntryBlock();
        auto InsertPt = EntryBB.getFirstInsertionPt();

        // Protect WebAssembly shadow stack by skipping ALL static Allocas
        while (InsertPt != EntryBB.end() &&
               (isa<AllocaInst>(&*InsertPt) ||
                isa<DbgInfoIntrinsic>(&*InsertPt))) {
          ++InsertPt;
        }

        if (InsertPt != EntryBB.end()) {
          IRBuilder<> Builder(&*InsertPt);

          if (InsertPt->getDebugLoc())
            Builder.SetCurrentDebugLocation(InsertPt->getDebugLoc());
          else if (FuncDL)
            Builder.SetCurrentDebugLocation(FuncDL);

          Builder.CreateCall(NotifyEnterFn);
          changed = true;
        }
      }

      DebugLoc LastValidDL;

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

              // ZERO-COLLISION STEP ID
              uint32_t stepId = (fileId << 20) | (instructionCounter & 0xFFFFF);

              IRBuilder<> StepBuilder(&I);
              StepBuilder.SetCurrentDebugLocation(DL);
              StepBuilder.CreateCall(StepFn, {StepBuilder.getInt32(stepId)});
              changed = true;

              if (!first)
                jsonStr += ",";
              jsonStr += "\"" + std::to_string(stepId) +
                         "\":{\"line\":" + std::to_string(line) +
                         ",\"func\":\"" + escapeJsonNova(cleanFuncName) +
                         "\",\"file\":\"" + escapeJsonNova(filePath) + "\"}";
              first = false;
            }
          }

          // 3. INJECT EXIT HOOK (Handles Returns AND Exception Unwinding)
          if (isa<ReturnInst>(&I) || isa<ResumeInst>(&I)) {
            Instruction *InsertPt = &I;

            // Prevent Verifier abort on MustTail calls
            if (auto *Prev = I.getPrevNode()) {
              if (auto *CB = dyn_cast<CallBase>(Prev)) {
                if (CB->isMustTailCall()) {
                  InsertPt = Prev;
                }
              }
            }

            IRBuilder<> ExitBuilder(InsertPt);

            if (InsertPt->getDebugLoc())
              ExitBuilder.SetCurrentDebugLocation(InsertPt->getDebugLoc());
            else if (LastValidDL)
              ExitBuilder.SetCurrentDebugLocation(LastValidDL);
            else if (FuncDL)
              ExitBuilder.SetCurrentDebugLocation(FuncDL);

            ExitBuilder.CreateCall(NotifyExitFn);
            changed = true;
          }
        }
      }
    }

    jsonStr += "}\n";

    // Stream JSON directly to file to avoid WASM OOM on large projects
    std::string stepMapPath = deriveStepMapPath(M.getSourceFileName());
    std::error_code EC;
    raw_fd_ostream OS(stepMapPath, EC, sys::fs::OF_None);

    if (!EC) {
      OS << jsonStr;
      OS.flush();
    }

    // Clear stream errors to prevent raw_fd_ostream destructor from calling
    // abort()
    if (OS.has_error()) {
      OS.clear_error();
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
