/* Homework 10 - CS6960
 * Author: Guannan Wei
 * This pass looks for intrinsic overflow instructions and try to simplify 
 * then to regualr instructions, only if they actually won't overflow in any cases.
 */

/* For example, this pass will eliminate overflow intrinsic instruction in the following program:

define i64 @f(i64, i64, i64, i64, i64, i64) {
entry:
  %result = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 1, i64 2)
  %fst = extractvalue { i64, i1 } %result, 0
  %snd = extractvalue { i64, i1 } %result, 1
  br i1 %snd, label %of, label %normal

of:                                               ; preds = %entry
  call void @overflow_fail(i32 6)
  br label %normal

normal:                                           ; preds = %of, %entry
  %result3 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 3, i64 %fst)
  %fst4 = extractvalue { i64, i1 } %result3, 0
  %snd5 = extractvalue { i64, i1 } %result3, 1
  br i1 %snd5, label %of1, label %normal2

of1:                                              ; preds = %normal
  call void @overflow_fail(i32 1)
  br label %normal2

normal2:                                          ; preds = %of1, %normal
  ret i64 %fst4
}

to this:

define i64 @f(i64, i64, i64, i64, i64, i64) {
entry:
  %res = add i64 1, 2
    br label %normal
    
normal:                                           ; preds = %entry
  %res1 = add i64 3, %res
    br label %normal2
    
normal2:                                          ; preds = %normal
  ret i64 %res1
}
*/

#include <llvm/Pass.h>
#include <llvm/IR/ConstantRange.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/IR/Dominators.h>
#include <llvm/ADT/APInt.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#define DEBUG_TYPE "simplifyoverflow"

using namespace llvm;

namespace {

struct OverflowSimplify : public FunctionPass {
  static char ID;
  OverflowSimplify() : FunctionPass(ID) {} 

  void getAnalysisUsage(AnalysisUsage& AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
  }

  Value* createOp(Intrinsic::ID ID, Value* l, Value* r) {
    switch (ID) {
      case Intrinsic::sadd_with_overflow:
      case Intrinsic::uadd_with_overflow:
        return Builder->CreateAdd(l, r, "res");
      case Intrinsic::ssub_with_overflow:
      case Intrinsic::usub_with_overflow:
        return Builder->CreateSub(l, r, "res");
      case Intrinsic::smul_with_overflow:
      case Intrinsic::umul_with_overflow:
        return Builder->CreateMul(l, r, "res");
      default: break;
    }
  }

  bool rewrite(Intrinsic::ID ID,
               inst_iterator iter, 
               IntrinsicInst* inst) {
    inst_iterator extract_fst_iter = ++iter;
    ExtractValueInst* extract_fst = dyn_cast<ExtractValueInst>(&*(extract_fst_iter));
    
    Value* v = extract_fst->getAggregateOperand();
    ArrayRef<unsigned> indices = extract_fst->getIndices();
    if (v != inst) return false;
    if (indices.size() != 1) return false;
    if (indices.front() != 0) return false;
  
    inst_iterator extract_snd_iter = ++iter;
    ExtractValueInst* extract_snd = dyn_cast<ExtractValueInst>(&*(extract_snd_iter));
    v = extract_snd->getAggregateOperand();
    indices = extract_snd->getIndices();
    if (v != inst) return false;
    if (indices.size() != 1) return false;
    if (indices.front() != 1) return false;
    
    inst_iterator br_iter = ++iter;
    BranchInst* br = dyn_cast<BranchInst>(&*(br_iter));
    if (br->getNumSuccessors() != 2) return false;
    if (br->getCondition() != extract_snd) return false;
    
    BasicBlock* of = br->getSuccessor(0);
    BasicBlock* normal = br->getSuccessor(1);

    BranchInst* newBr = Builder->CreateBr(normal);
    ReplaceInstWithInst(br, newBr);

    of->eraseFromParent();

    extract_snd->eraseFromParent();
    
    Value* res = createOp(ID, inst->getArgOperand(0), inst->getArgOperand(1));
    ReplaceInstWithInst(extract_fst, (Instruction*)res);

    inst->eraseFromParent();
    
    return true;
  }

  bool runOnFunction(Function& F) override {
    //errs() << "Running overflow simplification on function: " << F.getName() << '\n';
    BuilderTy TheBuilder(F.getContext());
    Builder = &TheBuilder;
    DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    AC = &getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
    DL = &F.getParent()->getDataLayout();
    return iterOverInst(F);
  }

  bool iterOverInst(Function& F) {
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; i++) {
      IntrinsicInst* inst = dyn_cast<IntrinsicInst>(&*i);

      if (!inst || inst->getNumArgOperands() != 2) continue;

      Value* lhs = inst->getArgOperand(0);
      Value* rhs = inst->getArgOperand(1);
      Intrinsic::ID ID = inst->getIntrinsicID();
      if (!willOverflow(ID, inst, lhs, rhs)) {
        if (rewrite(ID, i, inst))
          return iterOverInst(F) || true;
      }
    }
    return false;
  }

  bool willOverflow(Intrinsic::ID ID, Instruction* inst, Value* l, Value* r) {
    //errs() << l->getValueID() << " " << r->getValueID() << "\n";
    OverflowResult res = OverflowResult::MayOverflow;
    switch (ID) {
      case Intrinsic::sadd_with_overflow:
        res = computeOverflowForSignedAdd(&*l, &*r, *DL, &*AC, &*inst, &*DT);
        break;
      case Intrinsic::uadd_with_overflow:
        res = computeOverflowForUnsignedAdd(&*l, &*r, *DL, &*AC, &*inst, &*DT);
        break;
      case Intrinsic::ssub_with_overflow:
        //res = computeOverflowForSignedAdd(&*l, &*r, *DL, &*AC, &*inst, &*DT);
        break;
      case Intrinsic::usub_with_overflow:
        //res = computeOverflowForUnsignedAdd(&*l, &*r, *DL, &*AC, &*inst, &*DT);
        break;
      case Intrinsic::smul_with_overflow:
        break;
      case Intrinsic::umul_with_overflow:
        res = computeOverflowForUnsignedMul(&*l, &*r, *DL, &*AC, &*inst, &*DT);
        break;
      default: break; 
    }
    
    /*
    if (res == OverflowResult::AlwaysOverflows) {
      errs() << "always\n";
    }
    else if (res == OverflowResult::MayOverflow) {
      errs() << "may\n";
    }
    else if (res == OverflowResult::NeverOverflows) {
      errs() << "never\n";
    }
    */
    return (res != OverflowResult::NeverOverflows);
  }

private:
  typedef IRBuilder<NoFolder> BuilderTy;
  BuilderTy* Builder;
  DominatorTree* DT;
  AssumptionCache* AC;
  const DataLayout* DL;
};

}

char OverflowSimplify::ID = 0;
static RegisterPass<OverflowSimplify> X("overflowsimplify", "Overflow simplify pass", false, false);
