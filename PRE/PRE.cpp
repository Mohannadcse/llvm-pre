#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/CFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <map>
#include "Expression.h"
#include "InstrUtils.h"
#include <set>
#include <utility>
#include <iostream>
#include <queue>
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

namespace {

    struct PRE : public FunctionPass {
        static char ID;
        PRE() : FunctionPass(ID) {}

        virtual bool runOnFunction(Function &function);

        struct PREInfoNode {
            BitVector usedBeforeFirstChange;
            BitVector changed;
            BitVector notUsedAfterLastChange;
            BitVector used;

            BitVector earliest;
            BitVector latest;

            BitVector anticipated[2];
            BitVector available[2];
            BitVector postponable[2];
            BitVector toBeUsed[2];

            BasicBlock *blockPtr;
        };

    private:
        //Function &function;
        std::set<int> expFullSet;
        BitVector expFullSetVector;
        BitVector expEmptySetVector;

        std::map<Expression, int> exp2Int;
        std::vector<Expression*> exps;
        std::map<Instruction*, Expression*> ins2Exp;

        std::map<Value*, BitVector> var2RelatedExpSet; // calc upon the first access

        std::map<BasicBlock*, PREInfoNode> PREInfoNodeMap;
        std::set<BasicBlock*> exitBBSet;
        void preprocess(Function &function);
        void updateExpSet(Expression *expPtr);
        int getExpIndex(Expression *expPtr);
        BitVector* getVarRelatedExpSet(Value* dest);

        void workList(Function &function, void (*init)(Function &function, PRE *pre), bool (*update)(PREInfoNode &cur, std::vector<PREInfoNode*> &backNodes, PRE *pre),
                std::vector<PREInfoNode*>& (*getBackNodes)(BasicBlock &cur, PRE *pre), std::vector<PREInfoNode*>& (*getForwardNodes)(BasicBlock &cur, PRE *pre));

        static void initAnticipated(Function &function, PRE *pre);
        static void initEarliest(Function &function, PRE *pre);
        static void initPostponable(Function &function, PRE *pre);
        static void initToBeUsed(Function &function, PRE *pre);
        static bool updateAnticipated(PREInfoNode &cur, std::vector<PREInfoNode*> &backNodes, PRE *pre);
        static bool updateEarliest(PREInfoNode &cur, std::vector<PREInfoNode*> &backNodes, PRE *pre);
        static bool updatePostponable(PREInfoNode &cur, std::vector<PREInfoNode*> &backNodes, PRE *pre);
        static bool updateToBeUsed(PREInfoNode &cur, std::vector<PREInfoNode*> &backNodes, PRE *pre);
        static std::vector<PREInfoNode*>& getPreds(BasicBlock &cur, PRE *pre);
        static std::vector<PREInfoNode*>& getSuccs(BasicBlock &cur, PRE *pre);

        void transformCFG();

    // Function* function;
    };
}

char PRE::ID = 0;

bool PRE::runOnFunction(Function &function) {

    errs() << "runOnFunction starts" << "\n";

    preprocess(function); // calc used, kill
    workList(function, initAnticipated, updateAnticipated, getSuccs, getPreds);
    workList(function, initEarliest, updateEarliest, getPreds, getSuccs);
    for (auto ele : PREInfoNodeMap) {
        ele.second.earliest = ele.second.anticipated[0];
        ele.second.earliest.reset(ele.second.available[0]);
    }

    workList(function, initPostponable, updatePostponable, getPreds, getSuccs);
    for (auto ele : PREInfoNodeMap) {
        PREInfoNode &curNode = ele.second;
        curNode.latest = curNode.earliest;
        curNode.latest |= curNode.postponable[0];

        std::vector<PREInfoNode*> &succNodes = getSuccs(*ele.first, this);

        BitVector tmp = succNodes.size() > 0 ? expFullSetVector : expEmptySetVector;
        for (auto node : succNodes) {
            BitVector tmp2 = node->earliest;
            tmp2 |= node->postponable[0];
            tmp &= tmp2;
        }
        tmp.flip();
        tmp |= curNode.used;

        curNode.latest &= tmp;
    }

    workList(function, initToBeUsed, updateToBeUsed, getSuccs, getPreds);
    transformCFG();

    errs() << "runOnFunction finishes" << "\n";
    return true;
}

// add a new block between each block with multiple preds and its predcessors,
// find all expressions, map them to integers
// calc usedBeforeFirstChange, changed, notUsedAfterLastChange, and used
void PRE::preprocess(Function &function) {

    // Step 0: split blocks into single-instruction blocks
    for (auto& block : function) {
        if (block.size() > 1) { //TODO: might be a always-true condition
            for (int i = block.size() - 1; i > 0; --i) {
                SplitBlock(&block, &block.back());
            }
        }
    }

    // Step 1: a new block between each block with multiple preds and its predcessors
    // find all expressions, map them to integers
    //TODO: assuming no duplicate edges
    std::set<std::pair<BasicBlock*, BasicBlock*>> splitPairs;

    for (auto& block : function) {
        if (block.hasNPredecessorsOrMore(2)) {
            for (auto pred : predecessors(&block)) {
                splitPairs.insert(std::make_pair(pred, &block));
            }
        }
    }
    for (auto pr : splitPairs) {
        SplitEdge(pr.first, pr.second);
    }

    // Step 2: find all expressions and map them to integers;
    for (auto &block : function) {
        for (auto &instr : block) {
            Expression* expPtr = nullptr;
            if (instr.isTerminator()) {}
            else if (instr.isUnaryOp()) {}
            else if (InstrUtils::isConvertOp(instr)) {}
            else if (InstrUtils::isMemoryOp(instr)) {}
            else if (InstrUtils::isBadMiscOp(instr)) {}
            else if (instr.isBinaryOp() ||
                    InstrUtils::isLogicalOp(instr) ||
                    InstrUtils::isGoodMiscOp(instr)) {
                expPtr = Expression::getExpression(instr);
            } else {
                std::cerr << "found unhandled instr : " << instr.getOpcode() << " during preprocess Step 2" << std::endl;
            }

            if (expPtr != nullptr) {
                updateExpSet(expPtr);
            }
        }
    }

    // Step 2: calc usedBeforeFirstChange, changed, notUsedAfterLastChange, and used for each block
    for (auto& block : function) {
        PREInfoNode &curPREInfoNode = PREInfoNodeMap[&block];
        std::set<int> usedSoFar;
        curPREInfoNode.notUsedAfterLastChange = BitVector(expFullSet.size(), true); // default: all exps are not used
        curPREInfoNode.changed = BitVector(expFullSet.size());
        curPREInfoNode.usedBeforeFirstChange = BitVector(expFullSet.size());
        curPREInfoNode.used = BitVector(expFullSet.size());
        curPREInfoNode.blockPtr = &block;

        for (auto& instr : block) {
            Value* dest = nullptr;
            Expression *expPtr = nullptr;
            if (instr.isTerminator()) {
                exitBBSet.insert(&block);
            } else if (instr.isUnaryOp() ||
                InstrUtils::isConvertOp(instr) ||
                InstrUtils::isMemoryOp(instr) ||
                InstrUtils::isBadMiscOp(instr)) {}
            else if (instr.isBinaryOp() ||
                     InstrUtils::isLogicalOp(instr) ||
                     InstrUtils::isGoodMiscOp(instr)) {
                expPtr = Expression::getExpression(instr);
                ins2Exp[&instr] = expPtr;
            }
            else {
                std::cerr << "found unhandled instr : " << instr.getOpcode() << " during preprocess Step 3" << std::endl;
            }


            if (expPtr != nullptr) {
                int index = getExpIndex(expPtr);


                // notUsedAfterLastChange
                // remove index
                curPREInfoNode.notUsedAfterLastChange[index] = false;

                // usedBeforeFirstChange
                // if not changed then add to this set
                if (!curPREInfoNode.changed[index]) {
                    curPREInfoNode.usedBeforeFirstChange[index] = true;
                }

                // used
                curPREInfoNode.used[index] = true;
            }
            BitVector &relatedExpSet = *getVarRelatedExpSet(dest);

            // notUsedAfterLastChange
            // set related to true
            curPREInfoNode.notUsedAfterLastChange |= relatedExpSet;

            // changed
            // change all related exps
            curPREInfoNode.changed |= relatedExpSet;

            // usedBeforeFirstChange
            // no need

            // used
            // no need
        }
    }

    expFullSetVector = BitVector(expFullSet.size(), true);
    expEmptySetVector = BitVector(expFullSet.size());
}

void PRE::workList(Function &function, void (*init)(Function &function, PRE *pre), bool (*update)(PREInfoNode &cur, std::vector<PREInfoNode*> &backNodes, PRE *pre),
              std::vector<PREInfoNode*>& (*getBackNodes)(BasicBlock &cur, PRE *pre), std::vector<PREInfoNode*>& (*getForwardNodes)(BasicBlock &cur, PRE *pre)) {

    init(function, this);
    std::queue<BasicBlock*> q;
    std::set<BasicBlock*> ed;
    for (auto &block : function) {
        q.push(&block);
        ed.insert(&block);
    }
    while (q.size() > 0) {
        BasicBlock &cur = *(q.front());
        q.pop();
        ed.erase(&cur);

        PREInfoNode &curNode = PREInfoNodeMap[&cur];
        std::vector<PREInfoNode*> &backNodes = getBackNodes(cur, this);
        if (update(curNode, backNodes, this)) {
            std::vector<PREInfoNode*> &forwardNodes = getForwardNodes(cur, this);
            for (PREInfoNode* neibor : forwardNodes) {
                if (ed.find(neibor->blockPtr) == ed.end()) {
                    ed.insert(neibor->blockPtr);
                    q.push(neibor->blockPtr);
                }
            }
        }
    }
}

void PRE::transformCFG() {
    // insert evaluation for each expression at (latest inter tobeused[1])
    // assign new variable names without conflicts
    // update: in LLVM IR maybe it is not necessary to assign a value a name
    // replace each usage of expression with new names

    // collect and insert all new exp evaluations
    std::map<Expression, Value*> expToValueMap;
    for (auto &ele : PREInfoNodeMap) {
        PREInfoNode &curNode = ele.second;
        BitVector ExpToInsert = curNode.latest;
        ExpToInsert &= curNode.toBeUsed[1];
        BasicBlock &block = *ele.first;

        // insert new evaluations at the beginning
        IRBuilder<> ib(&block);
        for (auto i = 0; i < ExpToInsert.size(); ++i)
            if (ExpToInsert[i]) {
                Expression &exp = *exps[i];
                // allocate a value on stack and evaluate the exp
                ib.SetInsertPoint(&block, block.getFirstInsertionPt());
                Value* alloPtr = ib.CreateAlloca(exp.type);
                Value* evaPtr = exp.instr;
                Value* storePtr = ib.CreateStore(evaPtr, alloPtr);

                /*ib.Insert(alloPtr);
                ib.Insert(evaPtr);
                ib.Insert(storePtr);*/

                Value* loadPtr = ib.CreateLoad(alloPtr);
                expToValueMap[exp] = loadPtr;
            }
    }


    for (auto &ele : PREInfoNodeMap) {
        PREInfoNode &curNode = ele.second;
        BitVector ExpToInsert = curNode.latest;
        ExpToInsert &= curNode.toBeUsed[1];
        BasicBlock &block = *ele.first;

        // insert new evaluations at the beginning
        IRBuilder<> ib(&block);
        for (auto &instr : block)
            if (ins2Exp.find(&instr) != ins2Exp.end()) {
                Expression &exp = *ins2Exp[&instr];
                BasicBlock::iterator it(&instr);
                ReplaceInstWithValue(block.getInstList(), it, expToValueMap[exp]);
            }
    }
}

void PRE::initAnticipated(Function &function, PRE *pre) {
    //BasicBlock &exit = function.get();
    for (auto &ele : pre->PREInfoNodeMap) {
        if (pre->exitBBSet.find(ele.second.blockPtr) == pre->exitBBSet.end()) {
            ele.second.anticipated[0] = pre->expEmptySetVector;
            ele.second.anticipated[1] = pre->expEmptySetVector;
        } else {
            ele.second.anticipated[0] = pre->expFullSetVector;
            ele.second.anticipated[1] = pre->expFullSetVector;
        }
    }
}
bool PRE::updateAnticipated(PREInfoNode &curNode, std::vector<PREInfoNode*> &backNodes, PRE *pre) {
    BitVector* cur = curNode.anticipated;
    BitVector originalIn = cur[0];

    // calc out
    cur[1] = backNodes.size() > 0 ? pre->expFullSetVector : pre->expEmptySetVector;
    for (auto &from : backNodes) {
        cur[1] &= from->anticipated[0];
    }

    // calc in: in = (out - kill) u usedinblock
    cur[0] = cur[1];
    cur[0].reset(curNode.changed);
    cur[0] |= curNode.usedBeforeFirstChange;

    return originalIn != cur[0];
}

void PRE::initEarliest(Function &function, PRE *pre) {
    BasicBlock &exit = function.getEntryBlock();
    for (auto &ele : pre->PREInfoNodeMap) {
        if (ele.second.blockPtr == &exit) {
            ele.second.available[0] = pre->expEmptySetVector;
            ele.second.available[1] = pre->expEmptySetVector;
        } else {
            ele.second.available[0] = pre->expFullSetVector;
            ele.second.available[1] = pre->expFullSetVector;
        }
    }
}
bool PRE::updateEarliest(PREInfoNode &curNode, std::vector<PREInfoNode*> &backNodes, PRE *pre) {
    BitVector* cur = curNode.available;
    BitVector originalOut = cur[1];

    // calc out
    cur[0] = backNodes.size() > 0 ? pre->expFullSetVector : pre->expEmptySetVector;
    for (auto &from : backNodes) {
        cur[0] &= from->available[1];
    }

    // calc out: out = (in U in_ant) - kill
    cur[1] = cur[0];
    cur[1] |= curNode.anticipated[0];
    cur[1].reset(curNode.changed);

    return originalOut != cur[1];
}

void PRE::initPostponable(Function &function, PRE *pre) {
    BasicBlock &exit = function.getEntryBlock();
    for (auto &ele : pre->PREInfoNodeMap) {
        if (ele.second.blockPtr == &exit) {
            ele.second.postponable[0] = pre->expEmptySetVector;
            ele.second.postponable[1] = pre->expEmptySetVector;
        } else {
            ele.second.postponable[0] = pre->expFullSetVector;
            ele.second.postponable[1] = pre->expFullSetVector;
        }
    }
}
bool PRE::updatePostponable(PREInfoNode &curNode, std::vector<PREInfoNode*> &backNodes, PRE *pre) {
    BitVector* cur = curNode.postponable;
    BitVector originalOut = cur[1];

    // calc out
    cur[0] = backNodes.size() > 0 ? pre->expFullSetVector : pre->expEmptySetVector;
    for (auto &from : backNodes) {
        cur[0] &= from->postponable[1];
    }

    // calc out: out = (in U in_ant) - kill
    cur[1] = cur[0];
    cur[1] |= curNode.earliest;
    cur[1].reset(curNode.used);

    return originalOut != cur[1];
}

void PRE::initToBeUsed(Function &function, PRE *pre) {
    for (auto &ele : pre->PREInfoNodeMap) {
        ele.second.toBeUsed[0] = pre->expFullSetVector;
        ele.second.toBeUsed[1] = pre->expFullSetVector;
    }
}
bool PRE::updateToBeUsed(PREInfoNode &curNode, std::vector<PREInfoNode*> &backNodes, PRE *pre) {
    BitVector* cur = curNode.toBeUsed;
    BitVector originalIn = cur[0];

    // calc out
    cur[1] = pre->expEmptySetVector;
    for (auto &from : backNodes) {
        cur[1] |= from->toBeUsed[0];
    }

    // calc in: in = (out - kill) u usedinblock
    cur[0] = cur[1];
    cur[0] |= curNode.used;
    cur[0].reset(curNode.latest);

    return originalIn != cur[0];
}

std::vector<PRE::PREInfoNode*>& PRE::getPreds(BasicBlock &cur, PRE *pre) {
    auto *rtn = new std::vector<PREInfoNode*>();
    for (auto pred : predecessors(&cur)) {
        rtn->push_back(&pre->PREInfoNodeMap[pred]);
    }
    return *rtn;
}
std::vector<PRE::PREInfoNode*>& PRE::getSuccs(BasicBlock &cur, PRE *pre) {
    auto *rtn = new std::vector<PREInfoNode*>();
    for (auto succ : successors(&cur)) {
        rtn->push_back(&pre->PREInfoNodeMap[succ]);
    }
    return *rtn;

}

void PRE::updateExpSet(Expression *expPtr) {
    if (exp2Int.find(*expPtr) == exp2Int.end()) {
        exps.push_back(expPtr);
        int newIdx = exp2Int.size();
        exp2Int[*expPtr] = newIdx;
    }
}

int PRE::getExpIndex(Expression *expPtr) {
    // assuming the expression should exist
    if (exp2Int.find(*expPtr) != exp2Int.end())
        return exp2Int[*expPtr];
    return -1;
}

BitVector* PRE::getVarRelatedExpSet(Value* dest) {
    if (var2RelatedExpSet.find(dest) == var2RelatedExpSet.end()) {
        BitVector rtn = BitVector();
        for (unsigned long i = 0; i < exps.size(); ++i) {
            if (exps[i]->relatedTo(dest)) {
                rtn.set(i);
            }
        }
        var2RelatedExpSet[dest] = rtn;
    }
    return &var2RelatedExpSet[dest];
}



// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerPRE(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
    PM.add(new PRE());
}
static RegisterStandardPasses RegisterPRE(PassManagerBuilder::EP_EarlyAsPossible, registerPRE);
