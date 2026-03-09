#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/OptimizationLevel.h"
#include <memory>
#include <string>

using namespace llvm;

static cl::opt<bool> EnableNovaDebug("enable-nova-debug", cl::Hidden, cl::desc("Enable Nova IDE debug instrumentation"));
static cl::opt<std::string> NovaStepMap("nova-stepmap", cl::desc("Path to write Nova step map"), cl::Hidden);

namespace {

// FNV-1a Hash for deterministic file IDs
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
        if (c == '"') out += "\\\"";
        else if (c == '\\') out += "\\\\";
        else out += c;
    }
    return out;
}

struct NovaDebugPass : public PassInfoMixin<NovaDebugPass> {
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
        if (!EnableNovaDebug) return PreservedAnalyses::all();

        LLVMContext &Ctx = M.getContext();
        auto *StepType = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx)}, false);
        auto StepFn = M.getOrInsertFunction("JS_debug_step", StepType);

        auto *NotifyEnterType = FunctionType::get(Type::getVoidTy(Ctx), {}, false);
        auto NotifyEnterFn = M.getOrInsertFunction("JS_notify_enter", NotifyEnterType);

        auto *NotifyExitType = FunctionType::get(Type::getVoidTy(Ctx), {}, false);
        auto NotifyExitFn = M.getOrInsertFunction("JS_notify_exit", NotifyExitType);

        bool changed = false;
        bool first = true;

        // OPTIMIZATION: Stream JSON directly to file to avoid WASM OOM on large projects
        std::error_code EC;
        std::unique_ptr<raw_fd_ostream> OS;
        if (!NovaStepMap.empty()) {
            OS = std::make_unique<raw_fd_ostream>(NovaStepMap, EC, sys::fs::OF_None);
            if (!EC) *OS << "{";
        }

        // Ensure deterministic File ID and guarantee JS integer safety
        uint32_t fileId = hashStringNova(M.getSourceFileName()) & 0xFFF;
        uint32_t instructionCounter = 0;

        for (Function &F : M) {
            StringRef FName = F.getName();
            
            if (F.isDeclaration() || FName.starts_with("JS_") || FName.starts_with("__")) continue;
            if (FName == "clear_screen" || FName == "draw_circle" || FName == "render_frame" || FName == "malloc" || FName == "free") continue;

            bool isUserCode = false;
            for (BasicBlock &BB : F) {
                for (Instruction &I : BB) {
                    if (const DebugLoc &DL = I.getDebugLoc()) {
                        StringRef file = DL->getFilename();
                        if (file.contains("workspace") || file.contains("main.cpp")) {
                            isUserCode = true; break;
                        }
                    }
                }
                if (isUserCode) break;
            }

            if (!isUserCode) continue;

            // Clean function name for UI
            std::string cleanFuncName = FName.str();
            if (cleanFuncName == "__original_main") cleanFuncName = "main";
            else if (cleanFuncName.find("_Z") == 0) { 
                size_t i = 2;
                while (i < cleanFuncName.length() && cleanFuncName[i] >= '0' && cleanFuncName[i] <= '9') i++;
                if (i > 2) {
                    int len = std::stoi(cleanFuncName.substr(2, i - 2));
                    cleanFuncName = cleanFuncName.substr(i, len);
                }
            }

            // 1. INJECT ENTER HOOK (Safely skips alloca instructions!)
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
                
                for (auto it = BB.begin(); it != BB.end(); ) {
                    Instruction &I = *it++;
                    if (isa<PHINode>(&I) || I.isEHPad()) continue;

                    // 2. INJECT STEP HOOK FIRST
                    // (Ensures the debugger pauses before the Exit Hook pops the call stack)
                    if (const DebugLoc &DL = I.getDebugLoc()) {
                        int line = DL.getLine();
                        StringRef file = DL->getFilename();

                        if (line > 0 && line != lastLine && (file.contains("workspace") || file.contains("main.cpp"))) {
                            lastLine = line;
                            instructionCounter++;

                            std::string filePath = file.str();
                            if (filePath.find("/workspace/") != 0 && filePath.find("./") == 0) {
                                filePath = "/workspace/" + filePath.substr(2);
                            } else if (filePath.find("/workspace/") != 0) {
                                filePath = "/workspace/" + filePath;
                            }

                            // ZERO-COLLISION STEP ID (File Hash + Instruction Counter)
                            uint32_t stepId = (fileId << 20) | (instructionCounter & 0xFFFFF);

                            IRBuilder<> StepBuilder(&I);
                            StepBuilder.CreateCall(StepFn, {StepBuilder.getInt32(stepId)});
                            changed = true;

                            if (OS && !EC) {
                                if (!first) *OS << ",";
                                *OS << "\"" << stepId << "\":{\"line\":" << line 
                                    << ",\"func\":\"" << escapeJsonNova(cleanFuncName) 
                                    << "\",\"file\":\"" << escapeJsonNova(filePath) << "\"}";
                                first = false;
                            }
                        }
                    }

                    // 3. INJECT EXIT HOOK (Handles Returns AND Exception Unwinding)
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

// Official LLVM Extension Point Registration
extern "C" ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "NovaDebugPass", "v1",
        [](PassBuilder &PB) {
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                    MPM.addPass(NovaDebugPass());
                });
        }
    };
}
