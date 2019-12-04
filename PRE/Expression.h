//
// Created by animula on 11/17/19.
//

#ifndef LLVM_PRE_EXPRESSION_H
#define LLVM_PRE_EXPRESSION_H

#include <vector>
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Type.h"
#include <string>
using namespace llvm;

class Expression {
public:
    unsigned opCode;
    Type* type = nullptr;
    std::vector<Value*> &args;
    Instruction *instr;

    Expression(unsigned opCode, Type* type, std::vector<Value *> &args, Instruction *instr): opCode(opCode), type(type), args(args), instr(instr){};
    static Expression* getExpression(Instruction &instr);
    bool operator<(const Expression &exp) const;
    bool relatedTo(Value* var) const;
};


#endif //LLVM_PRE_EXPRESSION_H
