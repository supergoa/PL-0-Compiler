#define VM_READ(dest) (({ Instruction ins = { .op = OP_READ, .arg1 = (dest) }; ins; })) 
#define VM_WR(src) (({ Instruction ins = { .op = OP_WR, .arg1 = (src) }; ins; })) 
#define VM_BEQ(disp) (({ Instruction ins = { .op = OP_BEQ, .arg1 = (disp) }; ins; })) 
#define VM_BNE(disp) (({ Instruction ins = { .op = OP_BNE, .arg1 = (disp) }; ins; })) 
#define VM_BLT(disp) (({ Instruction ins = { .op = OP_BLT, .arg1 = (disp) }; ins; })) 
#define VM_BLE(disp) (({ Instruction ins = { .op = OP_BLE, .arg1 = (disp) }; ins; })) 
#define VM_BGT(disp) (({ Instruction ins = { .op = OP_BGT, .arg1 = (disp) }; ins; })) 
#define VM_BGE(disp) (({ Instruction ins = { .op = OP_BGE, .arg1 = (disp) }; ins; })) 
#define VM_BR(disp) (({ Instruction ins = { .op = OP_BR, .arg1 = (disp) }; ins; })) 
#define VM_BL(disp) (({ Instruction ins = { .op = OP_BL, .arg1 = (disp) }; ins; })) 
#define VM_RET(ri) (({ Instruction ins = { .op = OP_RET, .arg1 = (ri) }; ins; })) 
#define VM_MOV(dest, ri) (({ Instruction ins = { .op = OP_MOV, .arg1 = (dest), .arg2 = (ri) }; ins; })) 
#define VM_CMP(ri, rj) (({ Instruction ins = { .op = OP_CMP, .arg1 = (ri), .arg2 = (rj) }; ins; })) 
#define VM_ADD(dest, ri, rj) (({ Instruction ins = { .op = OP_ADD, .arg1 = (dest), .arg2 = (ri), .arg3 = (rj) }; ins; })) 
#define VM_SUB(dest, ri, rj) (({ Instruction ins = { .op = OP_SUB, .arg1 = (dest), .arg2 = (ri), .arg3 = (rj) }; ins; })) 
#define VM_MUL(dest, ri, rj) (({ Instruction ins = { .op = OP_MUL, .arg1 = (dest), .arg2 = (ri), .arg3 = (rj) }; ins; })) 
#define VM_DIV(dest, ri, rj) (({ Instruction ins = { .op = OP_DIV, .arg1 = (dest), .arg2 = (ri), .arg3 = (rj) }; ins; })) 
#define VM_MOD(dest, ri, rj) (({ Instruction ins = { .op = OP_MOD, .arg1 = (dest), .arg2 = (ri), .arg3 = (rj) }; ins; })) 
#define VM_MOVI(dest, imm) (({ Instruction ins = { .op = OP_MOVI, .arg1 = (dest), .arg2 = (imm) }; ins; })) 
#define VM_CMPI(ri, imm) (({ Instruction ins = { .op = OP_CMPI, .arg1 = (ri), .arg2 = (imm) }; ins; })) 
#define VM_ADDI(dest, ri, imm) (({ Instruction ins = { .op = OP_ADDI, .arg1 = (dest), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_SUBI(dest, ri, imm) (({ Instruction ins = { .op = OP_SUBI, .arg1 = (dest), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_MULI(dest, ri, imm) (({ Instruction ins = { .op = OP_MULI, .arg1 = (dest), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_DIVI(dest, ri, imm) (({ Instruction ins = { .op = OP_DIVI, .arg1 = (dest), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_MODI(dest, ri, imm) (({ Instruction ins = { .op = OP_MODI, .arg1 = (dest), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_LD(dest, ri, imm) (({ Instruction ins = { .op = OP_LD, .arg1 = (dest), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_ST(src, ri, imm) (({ Instruction ins = { .op = OP_ST, .arg1 = (src), .arg2 = (ri), .arg3 = (imm) }; ins; })) 
#define VM_PSH(src, ri) (({ Instruction ins = { .op = OP_PSH, .arg1 = (src), .arg2 = (ri) }; ins; })) 
#define VM_POP(dest, ri) (({ Instruction ins = { .op = OP_POP, .arg1 = (dest), .arg2 = (ri) }; ins; })) 
#define VM_NOP() (({ Instruction ins = { .op = OP_NOP }; ins; })) 
#define VM_HLT() (({ Instruction ins = { .op = OP_HLT }; ins; })) 
