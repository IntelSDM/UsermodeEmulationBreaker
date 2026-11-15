#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"


#include "AntiEmuNanoPass.h"
#include "llvm/IR/InlineAsm.h"

#include <ctime>
#include <cstdlib>

using namespace llvm;


struct ObfuscationPass : PassInfoMixin<ObfuscationPass>
{
    PreservedAnalyses run(Module& m, ModuleAnalysisManager&)
    {
        return PreservedAnalyses::none();
    }
};

llvm::PassPluginLibraryInfo GetPassPluginInfo()
{
    return
    {
        LLVM_PLUGIN_API_VERSION,
        "EmulationBreaker",
        LLVM_VERSION_STRING,
        [](PassBuilder& pb)
        {
            pb.registerOptimizerLastEPCallback([](ModulePassManager& pm, OptimizationLevel)
            {
               

pm.addPass(AntiEmuNanoPass());
            });
        }
    };
}
#ifndef LLVM_BYE_LINK_INTO_TOOLS
extern "C"
__declspec(dllexport) LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
#ifdef _WIN32
#endif
    srand(time(0));
    return GetPassPluginInfo();
}
#endif