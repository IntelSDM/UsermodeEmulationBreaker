#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct AntiEmuNanoPass : llvm::PassInfoMixin<AntiEmuNanoPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunAntiEmuNano(llvm::Module& m);

extern llvm::cl::opt<bool> AntiEmuNanoEnable;