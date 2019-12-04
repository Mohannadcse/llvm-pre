//
// Created by animula on 11/17/19.
//

#include "Expression.h"
using namespace llvm;

Expression* Expression::getExpression(Instruction &instr) {
    errs() << "generating an exp:" << "\n";
    //NOTE: for icmp ops, the type of cmp is treated as an argument and should be ok
    unsigned opCode = instr.getOpcode();
    Type *type = instr.getType();
    std::vector<Value*> args;
    errs() << instr << "\n";
    errs() << instr.getOpcodeName() << ": " << instr.getName() << "/" << *type << "\n";
    for (auto& operand : instr.operands()) {
        errs() << *operand << ": " << operand->getName() << "\n";
        args.push_back(operand);
    }

    return new Expression(opCode, type, args, &instr);
}


bool Expression::operator<(const Expression &exp) const {
    errs() << "comparing exps" << "\n";
    errs() << *this->instr << "\n";
    errs() << *exp.instr << "\n";

    if (opCode != exp.opCode)
        return opCode < exp.opCode;
    if (type->getTypeID() != exp.type->getTypeID())
        return type->getTypeID() < exp.type->getTypeID();
    if (args.size() != exp.args.size())
        return args.size() < exp.args.size();
    for (int i = 0; i < args.size(); ++i) {
        errs() << args[i] << "\n" << exp.args[i] << "\n";
        if (args[i] != exp.args[i])
            return args[i] < exp.args[i];
    }
    return false;
}


bool Expression::relatedTo(Value* var) const {
    for (Value* arg : args) {
        if (var == arg)
            return true;
    }
    return false;
}