#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"
#include <set>
#include <vector>

using namespace llvm;


#define DEBUG_TYPE "modPass"

STATISTIC(NumPromoted, "Number of alloca's promoted");

static bool promoteMemoryToRegister(Function &F, DominatorTree &DT, AssumptionCache &AC);
PreservedAnalyses PromotePass::run(Function &F, FunctionAnalysisManager &AM) {
  auto &DT = AM.getResult<DominatorTreeAnalysis>(F);
  auto &AC = AM.getResult<AssumptionAnalysis>(F);
  if (!promoteMemoryToRegister(F, DT, AC))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}


namespace {

struct modPass : public FunctionPass {
  // Pass identification, replacement for typeid
  static char ID;

  modPass() : FunctionPass(ID) {
    //initializePromoteLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  // runOnFunction - To run this pass, first we calculate the alloca
  // instructions that are safe for promotion, then we promote each one.
  bool runOnFunction(Function &F) override {
    if (skipFunction(F))
      return false;

    DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    AssumptionCache &AC =
        getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
    bool toPromote = promoteMemoryToRegister(F, DT, AC);

    // Adding for the constant prop.

    std::set<Instruction*> WorkList;
    for (Instruction &I: instructions(&F))
      WorkList.insert(&I);

    bool Changed = false;
    const DataLayout &DL = F.getParent()->getDataLayout();
    TargetLibraryInfo *TLI =
        &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();

    while (!WorkList.empty()) {
      Instruction *I = *WorkList.begin();
      WorkList.erase(WorkList.begin());    // Get an element from the worklist...

      if (!I->use_empty())                 // Don't muck with dead instructions...
        if (Constant *C = ConstantFoldInstruction(I, DL, TLI)) {
          // Add all of the users of this instruction to the worklist, they might
          // be constant propagatable now...
          for (User *U : I->users())
            WorkList.insert(cast<Instruction>(U));

          // Replace all of the uses of a variable with uses of the constant.
          I->replaceAllUsesWith(C);

          // Remove the dead instruction.
          WorkList.erase(I);
          if (isInstructionTriviallyDead(I, TLI)) {
            I->eraseFromParent();
            //++NumInstKilled;
          }

          // We made a change to the function...
          Changed = true;
        }
    }
    return changed && toPromote ; // change this
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.setPreservesCFG();
  }
};

} //end namespace


static bool promoteMemoryToRegister(Function &F, DominatorTree &DT, AssumptionCache &AC){
  std::vector<AllocaInst *> Allocas;
  BasicBlock &BB = F.getEntryBlock(); // Get the entry node for the function
  bool Changed = false;

  while (true) {
    Allocas.clear();

    // Find allocas that are safe to promote, by looking at all instructions in
    // the entry node
    for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I)
      if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) // Is it an alloca?
        if (isAllocaPromotable(AI))
          Allocas.push_back(AI);

    if (Allocas.empty())
      break;

    PromoteMemToReg(Allocas, DT, &AC);
    NumPromoted += Allocas.size();
    Changed = true;
  }
  return Changed;
}


char modPass::ID = 0;

INITIALIZE_PASS_BEGIN(modPass, "modPass", "Promote Memory to Register", false, false)
INITIALIZE_PASS_DEPENDENCY(AssumptionCacheTracker)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(modPass, "modPass", "Promote Memory to Register", false, false)

// createPromoteMemoryToRegister - Provide an entry point to create this pass.
static RegisterPass<modPass> X("modPass", "Constant Propagation with mem2reg",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
