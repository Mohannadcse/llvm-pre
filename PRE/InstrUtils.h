//
// Created by animula on 11/18/19.
//

#ifndef LLVM_PRE_INSTRUTILS_H
#define LLVM_PRE_INSTRUTILS_H

#include <llvm/IR/Instruction.h>

using namespace llvm;

class InstrUtils {
public:
    static bool isMemoryOp(Instruction &instr) {
        unsigned opCode = instr.getOpcode();
        return opCode == Instruction::Alloca ||
               opCode == Instruction::Load ||
               opCode == Instruction::Store ||
               opCode == Instruction::AtomicCmpXchg ||
               opCode == Instruction::AtomicRMW ||
               opCode == Instruction::Fence ||
               opCode == Instruction::GetElementPtr;
    }
    static bool isLogicalOp(Instruction &instr) {
        unsigned opCode = instr.getOpcode();
        return opCode == Instruction::And ||
               opCode == Instruction::Or ||
               opCode == Instruction::Xor;
    }
    static bool isConvertOp(Instruction &instr) {
        unsigned opCode = instr.getOpcode();
        return opCode == Instruction::Trunc ||
               opCode == Instruction::ZExt ||
               opCode == Instruction::SExt ||
               opCode == Instruction::FPTrunc ||
               opCode == Instruction::FPExt ||
               opCode == Instruction::FPToUI ||
               opCode == Instruction::FPToSI ||
               opCode == Instruction::UIToFP ||
               opCode == Instruction::SIToFP ||
               opCode == Instruction::IntToPtr ||
               opCode == Instruction::PtrToInt ||
               opCode == Instruction::BitCast ||
               opCode == Instruction::AddrSpaceCast;
    }
    static bool isGoodMiscOp(Instruction &instr) {
        unsigned opCode = instr.getOpcode();
        return opCode == Instruction::ICmp ||
                opCode == Instruction::FCmp;
    }
    static bool isBadMiscOp(Instruction &instr) {
        unsigned opCode = instr.getOpcode();
        return opCode == Instruction::PHI ||
                opCode == Instruction::Select ||
                opCode == Instruction::Call ||
                opCode == Instruction::VAArg ||
                opCode == Instruction::LandingPad ||
                opCode == Instruction::CatchPad ||
                opCode == Instruction::CleanupPad;
    }
};


#endif //LLVM_PRE_INSTRUTILS_H
