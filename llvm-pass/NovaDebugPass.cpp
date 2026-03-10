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

Instruction *adjustForMustTail(Instruction *I) {
  Instruction *Scan = I;
  while (Scan) {
    if (auto *CB = dyn_cast<CallBase>(Scan)) {
      if (CB->isMustTailCall())
        return Scan;
    }
    if (isa<ReturnInst>(Scan) || isa<BitCastInst>(Scan) ||
        isa<IntToPtrInst>(Scan) || isa<ExtractValueInst>(Scan) ||
        isa<DbgInfoIntrinsic>(Scan)) {
      Scan = Scan->getPrevNode();
      continue;
    }
    break;
  }
  return I;
}

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

      DISubprogram *SP = F.getSubprogram();
      DebugLoc FuncDL;
      if (SP)
        FuncDL = DILocation::get(Ctx, SP->getLine(), 0, SP);
      DebugLoc LastValidDL = FuncDL ? FuncDL : FirstValidDL;

      // ----------------------------------------------------------------------
      // PHASE 1: COLLECTION (Prevents WebAssembly Iterator Invalidation Traps)
      // ----------------------------------------------------------------------
      Instruction *EnterHookPt = nullptr;
      std::vector<std::pair<Instruction *, uint32_t>> StepHooks;
      std::vector<Instruction *> ExitHooks;

      if (!F.empty()) {
        EnterHookPt = getSafeInsertionPoint(F.getEntryBlock());
      }

      for (BasicBlock &BB : F) {
        int lastLine = -1;
        for (Instruction &I : BB) {
          if (I.getDebugLoc())
            LastValidDL = I.getDebugLoc();
          if (isa<PHINode>(&I) || I.isEHPad() || isa<AllocaInst>(&I))
            continue;

          if (const DebugLoc &DL = I.getDebugLoc()) {
            int line = DL.getLine();
            StringRef file = DL->getFilename();

            if (line > 0 && line != lastLine && isUserSourceFile(file)) {
              lastLine = line;
              instructionCounter++;
              std::string filePath = file.str();
              if (filePath.find("/workspace/") != 0 && filePath.find("./") == 0)
                filePath = "/workspace/" + filePath.substr(2);
              else if (filePath.find("/workspace/") != 0)
                filePath = "/workspace/" + filePath;

              uint32_t stepId = (fileId << 17) | (instructionCounter & 0x1FFFF);
              Instruction *InsertPt = adjustForMustTail(&I);
              if (InsertPt) {
                StepHooks.push_back({InsertPt, stepId});
                StepMap.push_back({stepId, line, cleanFuncName, filePath});
              }
            }
          }

          if (isa<ReturnInst>(&I) || isa<ResumeInst>(&I) ||
              isa<CleanupReturnInst>(&I) || isa<CatchReturnInst>(&I)) {
            Instruction *InsertPt = adjustForMustTail(&I);
            if (InsertPt)
              ExitHooks.push_back(InsertPt);
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
        IRBuilder<> StepBuilder(Hook.first);
        if (Hook.first->getDebugLoc())
          StepBuilder.SetCurrentDebugLocation(Hook.first->getDebugLoc());
        else if (LastValidDL)
          StepBuilder.SetCurrentDebugLocation(LastValidDL);
        StepBuilder.CreateCall(StepFn, {StepBuilder.getInt32(Hook.second)});
        changed = true;
      }

      for (auto *InsertPt : ExitHooks) {
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
