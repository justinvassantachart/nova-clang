#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Passes/OptimizationLevel.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>

using namespace llvm;

// NO cl::opt FLAGS! LTO strips them in the WASM build.
// This pass is ALWAYS active since this is the Nova fork.
// The stepmap path is derived from the source filename.

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

// Derive stepmap path: /workspace/main.cpp ->
// /workspace/_workspace_main.stepmap.json
std::string deriveStepMapPath(StringRef sourceFile) {
  std::string name = sourceFile.str();
  // Replace / with _ and .cpp with .stepmap.json
  std::string flat;
  for (char c : name) {
    if (c == '/')
      flat += '_';
    else
      flat += c;
  }
  // Remove leading underscore if present
  if (!flat.empty() && flat[0] == '_')
    flat = flat.substr(1);
  // Replace .cpp with .stepmap.json
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

    // Check if this module has any user code at all
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

    // Derive stepmap path from module source filename
    std::string stepMapPath = deriveStepMapPath(M.getSourceFileName());

    std::error_code EC;
    std::unique_ptr<raw_fd_ostream> OS;
    OS = std::make_unique<raw_fd_ostream>(stepMapPath, EC, sys::fs::OF_None);
    if (!EC)
      *OS << "{";

    uint32_t fileId = hashStringNova(M.getSourceFileName()) & 0xFFF;
    uint32_t instructionCounter = 0;

    for (Function &F : M) {
      StringRef FName = F.getName();

      if (F.isDeclaration() || FName.starts_with("JS_") ||
          FName.starts_with("__"))
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
        while (i < cleanFuncName.length() && cleanFuncName[i] >= '0' &&
               cleanFuncName[i] <= '9')
          i++;
        if (i > 2) {
          int len = std::stoi(cleanFuncName.substr(2, i - 2));
          cleanFuncName = cleanFuncName.substr(i, len);
        }
      }

      // 1. INJECT ENTER HOOK
      if (!F.empty()) {
        BasicBlock &EntryBB = F.getEntryBlock();
        auto InsertPt = EntryBB.getFirstInsertionPt();
        if (InsertPt != EntryBB.end()) {
          IRBuilder<> Builder(&*InsertPt);
          Builder.CreateCall(NotifyEnterFn);
          changed = true;
        }
      }

      for (BasicBlock &BB : F) {
        int lastLine = -1;

        for (auto it = BB.begin(); it != BB.end();) {
          Instruction &I = *it++;
          if (isa<PHINode>(&I) || I.isEHPad())
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

              uint32_t stepId = (fileId << 20) | (instructionCounter & 0xFFFFF);

              IRBuilder<> StepBuilder(&I);
              StepBuilder.CreateCall(StepFn, {StepBuilder.getInt32(stepId)});
              changed = true;

              if (OS && !EC) {
                if (!first)
                  *OS << ",";
                *OS << "\"" << stepId << "\":{\"line\":" << line
                    << ",\"func\":\"" << escapeJsonNova(cleanFuncName)
                    << "\",\"file\":\"" << escapeJsonNova(filePath) << "\"}";
                first = false;
              }
            }
          }

          // 3. INJECT EXIT HOOK
          if (isa<ReturnInst>(&I) || isa<ResumeInst>(&I)) {
            IRBuilder<> ExitBuilder(&I);
            ExitBuilder.CreateCall(NotifyExitFn);
            changed = true;
          }
        }
      }
    }

    if (OS && !EC) {
      *OS << "}\n";
    }

    return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};
} // namespace

// Static registration - called from PassBuilder constructor
extern "C" ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "NovaDebugPass", "v1", [](PassBuilder &PB) {
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                  MPM.addPass(NovaDebugPass());
                });
          }};
}
