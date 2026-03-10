#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Passes/OptimizationLevel.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <vector>

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
    else if (c == '\n')
      out += "\\n";
    else if (c == '\r')
      out += "\\r";
    else if (c == '\t')
      out += "\\t";
    else if (c >= 0 && c < 32)
      continue;
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
  for (char c : name)
    flat += (c == '/') ? '_' : c;
  if (!flat.empty() && flat[0] == '_')
    flat = flat.substr(1);
  auto pos = flat.rfind(".cpp");
  if (pos != std::string::npos)
    flat = flat.substr(0, pos) + ".stepmap.json";
  else
    flat += ".stepmap.json";
  return "/workspace/" + flat;
}

bool isUserSourceFile(StringRef file) {
  return file.contains("workspace") || file.contains("main.cpp");
}

bool isNovaRuntime(StringRef Name) {
  return Name.starts_with("JS_") || Name == "clear_screen" ||
         Name == "draw_circle" || Name == "render_frame" || Name == "malloc" ||
         Name == "free" || Name == "__wrap_malloc" || Name == "__wrap_free";
}

Instruction *getSafeInsertionPoint(BasicBlock &BB) {
  auto InsertPt = BB.getFirstInsertionPt();
  while (InsertPt != BB.end() &&
         (isa<AllocaInst>(&*InsertPt) || isa<DbgInfoIntrinsic>(&*InsertPt) ||
          isa<PHINode>(&*InsertPt))) {
    ++InsertPt;
  }
  if (InsertPt == BB.end())
    return BB.getTerminator();
  return &*InsertPt;
}

// Per-hook structs prevent DebugLoc bleeding from Phase 1 → Phase 2
struct StepHook {
  Instruction *InsertPt;
  uint32_t stepId;
  DebugLoc DL;
};

struct ExitHook {
  Instruction *InsertPt;
  DebugLoc DL;
};

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
    FunctionCallee StepFn = M.getOrInsertFunction("JS_debug_step", StepType);

    auto *NotifyEnterType = FunctionType::get(Type::getVoidTy(Ctx), {}, false);
    FunctionCallee NotifyEnterFn =
        M.getOrInsertFunction("JS_notify_enter", NotifyEnterType);

    auto *NotifyExitType = FunctionType::get(Type::getVoidTy(Ctx), {}, false);
    FunctionCallee NotifyExitFn =
        M.getOrInsertFunction("JS_notify_exit", NotifyExitType);

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

    uint32_t fileId = hashStringNova(M.getSourceFileName()) & 0x3FFF;
    uint32_t instructionCounter = 0;

    for (Function &F : M) {
      StringRef FName = F.getName();
      if (F.isDeclaration() || isNovaRuntime(FName) ||
          (FName.starts_with("__") && FName != "__original_main"))
        continue;

      // Skip naked functions and any function containing musttail calls
      bool skipFunc = F.hasFnAttribute(Attribute::Naked);
      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (auto *CB = dyn_cast<CallBase>(&I)) {
            if (CB->isMustTailCall()) {
              skipFunc = true;
              break;
            }
          }
        }
        if (skipFunc)
          break;
      }
      if (skipFunc)
        continue;

      bool isUserFunc = false;
      DebugLoc FirstValidDL;
      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (const DebugLoc &DL = I.getDebugLoc()) {
            if (!FirstValidDL)
              FirstValidDL = DL;
            if (isUserSourceFile(DL->getFilename()))
              isUserFunc = true;
          }
        }
      }

      if (!isUserFunc)
        continue;

      // Robust demangling: DWARF metadata holds pristine source names
      DISubprogram *SP = F.getSubprogram();
      std::string cleanFuncName;
      if (SP && !SP->getName().empty()) {
        cleanFuncName = SP->getName().str();
      } else if (FName == "__original_main") {
        cleanFuncName = "main";
      } else {
        cleanFuncName = FName.str();
      }

      DebugLoc FuncDL;
      if (SP)
        FuncDL = DILocation::get(Ctx, SP->getLine(), 0, SP);

      // ----------------------------------------------------------------------
      // PHASE 1: COLLECTION (Prevents WebAssembly Iterator Invalidation Traps)
      // ----------------------------------------------------------------------
      Instruction *EnterHookPt = nullptr;
      std::vector<StepHook> StepHooks;
      std::vector<ExitHook> ExitHooks;

      if (!F.empty()) {
        EnterHookPt = getSafeInsertionPoint(F.getEntryBlock());
      }

      // FIX: Hoist tracking variables OUT of the BasicBlock loop so that
      // duplicate hooks for the same source line across block boundaries
      // (e.g. delete, loop conditions) are correctly deduplicated.
      int lastLine = -1;
      StringRef lastFile = "";

      for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
          if (isa<PHINode>(&I) || I.isEHPad() || isa<AllocaInst>(&I))
            continue;

          if (const DebugLoc &DL = I.getDebugLoc()) {
            int line = DL.getLine();
            StringRef file = DL->getFilename();

            // Deduplicate across sequential BasicBlocks by tracking both
            // line AND file — prevents double-stepping on delete/loops
            if (line > 0 && (line != lastLine || file != lastFile) &&
                isUserSourceFile(file)) {
              lastLine = line;
              lastFile = file;
              instructionCounter++;

              std::string filePath = file.str();
              if (filePath.find("/workspace/") != 0 && filePath.find("./") == 0)
                filePath = "/workspace/" + filePath.substr(2);
              else if (filePath.find("/workspace/") != 0)
                filePath = "/workspace/" + filePath;

              uint32_t stepId = (fileId << 17) | (instructionCounter & 0x1FFFF);

              // Store the DebugLoc per-hook to prevent Phase 2 bleeding
              StepHooks.push_back({&I, stepId, DL});
              StepMap.push_back({stepId, line, cleanFuncName, filePath});
            }
          }

          if (isa<ReturnInst>(&I) || isa<ResumeInst>(&I) ||
              isa<CleanupReturnInst>(&I) || isa<CatchReturnInst>(&I)) {
            ExitHooks.push_back({&I, I.getDebugLoc()});
          }
        }
      }

      // ----------------------------------------------------------------------
      // PHASE 2: INJECTION (Safe to execute outside the iteration loops)
      // ----------------------------------------------------------------------
      if (EnterHookPt) {
        IRBuilder<> Builder(EnterHookPt);
        if (EnterHookPt->getDebugLoc())
          Builder.SetCurrentDebugLocation(EnterHookPt->getDebugLoc());
        else if (FirstValidDL)
          Builder.SetCurrentDebugLocation(FirstValidDL);
        else if (FuncDL)
          Builder.SetCurrentDebugLocation(FuncDL);
        Builder.CreateCall(NotifyEnterFn);
        changed = true;
      }

      for (auto &Hook : StepHooks) {
        IRBuilder<> StepBuilder(Hook.InsertPt);
        // Use the per-hook DL, not a global that bled to the last instruction
        if (Hook.DL)
          StepBuilder.SetCurrentDebugLocation(Hook.DL);
        else if (FirstValidDL)
          StepBuilder.SetCurrentDebugLocation(FirstValidDL);
        StepBuilder.CreateCall(StepFn, {StepBuilder.getInt32(Hook.stepId)});
        changed = true;
      }

      for (auto &Hook : ExitHooks) {
        IRBuilder<> ExitBuilder(Hook.InsertPt);
        if (Hook.DL)
          ExitBuilder.SetCurrentDebugLocation(Hook.DL);
        else if (FirstValidDL)
          ExitBuilder.SetCurrentDebugLocation(FirstValidDL);
        else if (FuncDL)
          ExitBuilder.SetCurrentDebugLocation(FuncDL);
        ExitBuilder.CreateCall(NotifyExitFn);
        changed = true;
      }
    }

    std::string stepMapPath = deriveStepMapPath(M.getSourceFileName());
    std::error_code EC;
    raw_fd_ostream OS(stepMapPath, EC, sys::fs::OF_None);

    if (EC) {
      OS.clear_error();
    } else {
      OS << "{";
      bool first = true;
      for (const auto &Entry : StepMap) {
        if (!first)
          OS << ",\n";
        first = false;
        OS << "\"" << Entry.stepId << "\":{\"line\":" << Entry.line
           << ",\"func\":\"" << escapeJsonNova(Entry.func) << "\",\"file\":\""
           << escapeJsonNova(Entry.file) << "\"}";
      }
      OS << "}\n";
      OS.flush();
      OS.close();
      if (OS.has_error())
        OS.clear_error();
    }

    return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};

} // namespace

// =========================================================================
// DIRECT STATIC C++ INJECTION
// (Completely bypasses WASM PassPlugin ABI Traps)
// =========================================================================
void injectNovaDebugPass(PassBuilder &PB) {
  PB.registerPipelineStartEPCallback(
      [](ModulePassManager &MPM, OptimizationLevel Level) {
        if (Level == OptimizationLevel::O0) {
          MPM.addPass(NovaDebugPass());
        }
      });
}
