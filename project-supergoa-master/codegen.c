#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <error.h>
#include <assert.h>

#include "ast.h"
#include "symtab.h"
#include "codegen.h"
#include "vm_types.h"

// declarations
static void visitTranslationUnit(struct TranslationUnit *node);
static void visitBlock(struct Block *node);
static void visitVarDecls(struct TypedIdentList *list);
static void visitFuncDecls(struct FuncDeclList *list);
static void visitFuncDecl(struct FuncDecl *node);
static void visitFormals(struct TypedIdentList *list);

// statements
static void visitStatement(struct Statement *node);
static void visitAssignStatement(struct Statement *node);
static void visitCallStatement(struct Statement *node);
static void visitReturnStatement(struct Statement *node);
static void visitCompoundStatement(struct Statement *list);
static void visitIfStatement(struct Statement *node);
static void visitWhileStatement(struct Statement *node);
static void visitReadStatement(struct Statement *node);
static void visitWriteStatement(struct Statement *node);

// expressions
static int visitExpression(struct Expression *node, int reg_base);
static int visitBinaryExpressionInt(struct Expression *node, int reg_base);
static int visitUnaryExpressionInt(struct Expression *node, int reg_base);
static int visitBinaryExpressionBool(struct Expression *node, int reg_base);
static int visitUnaryExpressionBool(struct Expression *node, int reg_base);
static int visitNumberFactor(struct Expression *node, int reg_base);
static int visitBooleanFactor(struct Expression *node, int reg_base);
static int visitVariableFactor(struct Expression *node, int reg_base);
static int visitFunctionFactor(struct Expression *node, int reg_base);

// common functions for statements and expressions
static void setVariable(struct Symbol *symbol, int reg);
static void setupFunctionCall(struct Symbol *fsymbol, struct ExpressionList *parameters, int reg);

// helper functions for emitting ops
static int emit(Instruction instr);
static void backpatch(int branch_instruction_address, int new_disp);
static Instruction code[CODE_SIZE];
static int code_index;

static struct Scope *current_scope = NULL;

// helper macros for special registers
#define FP 12
#define SP 13
#define LN 14
#define IP 15

// stack frame offsets
#define OFFSET_FIRST_PARAM -4
#define OFFSET_RET_VAL -3
#define OFFSET_STATIC_LINK -2
#define OFFSET_RET_ADDR -1
#define OFFSET_FIRST_LOCAL 1 

#include "codegen_tools.c"

void codegen(struct TranslationUnit *ast) {
  for (int i = 0; i < CODE_SIZE; i++) {
    code[i].op = OP_HLT;
    code[i].arg1 = 0;
    code[i].arg2 = 0;
    code[i].arg3 = 0;
  }
  code_index = 0;
  visitTranslationUnit(ast);
}

static void visitTranslationUnit(struct TranslationUnit *node) {
  current_scope = node->scope;
  visitBlock(node->block);
  code[code_index++] = VM_HLT();
}

static void visitBlock(struct Block *node) {
  visitVarDecls(node->vardecls);

  // skip past function definitions, since we want to start running the current function body
  int saved_jump = emit(VM_BR(0));
  visitFuncDecls(node->funcdecls);

  // code_index is now the body of the function (or main)
  int entry_point = code_index;
  backpatch(saved_jump, code_index - saved_jump); // backpatch
  visitStatement(node->statement);
}

static void visitVarDecls(struct TypedIdentList *list) {
  // given skeleton
  struct TypedIdentListElement *cur = list->head;
  int num_vars = 0;
  while (NULL != cur) {
    // TODO: create space for each var and and update its stack frame offset
    cur->node->symbol->address = OFFSET_FIRST_LOCAL + num_vars++;
    emit(VM_ADDI(SP, SP, 1));
    cur = cur->next;
  }
}

static void visitFuncDecl(struct FuncDecl *node) {
  struct Symbol *fsymbol = node->symbol;
  
  //printf("fsymbol %d", node->symbol->address);
  node->symbol->address = code_index;

  struct Scope *previous_scope = current_scope;
  current_scope = node->scope;  

  // TODO: setup the function address and stack frame
  emit(VM_PSH(LN, SP));
  emit(VM_PSH(FP, SP));
  emit(VM_MOV(FP, SP));

  visitFormals(node->formals);
  visitBlock(node->block);

  current_scope = previous_scope;

  emit(VM_MOV(SP, FP));
  emit(VM_POP(FP, SP));
  emit(VM_POP(LN, SP));
  emit(VM_RET(LN));
}

static void visitFormals(struct TypedIdentList *list) {
  // given skeleton
  int num_formals = 0;
  struct TypedIdentListElement *cur = list->head;
  while (NULL != cur) {
    struct TypedIdent *node = cur->node;

    node->symbol->address = OFFSET_FIRST_PARAM - num_formals++;

    // TODO: parameters are pushed in reverse order and space for the
    // return value is made by the caller before the stack frame, so
    // update the address of each parameter accordingly.
    
    cur = cur->next;
  }
}

static void visitFuncDecls(struct FuncDeclList *list) {
  // given
  struct FuncDeclListElement *cur = list->head;
  while (NULL != cur) {
    visitFuncDecl(cur->node);
    cur = cur->next;
  }
}

static void visitStatement(struct Statement *node) {
  // given
  switch (node->kind) {
  case ASSIGNSTATEMENT:
    visitAssignStatement(node);
    break;
  case CALLSTATEMENT:
    visitCallStatement(node);
    break;
  case RETURNSTATEMENT:
    visitReturnStatement(node);
    break;
  case COMPOUNDSTATEMENT:
    visitCompoundStatement(node);
    break;
  case IFSTATEMENT:
    visitIfStatement(node);
    break;
  case WHILESTATEMENT:
    visitWhileStatement(node);
    break;
  case READSTATEMENT:
    visitReadStatement(node);
    break;
  case WRITESTATEMENT:
    visitWriteStatement(node);
    break;
  default:
    error(0, 0, "unknown option");
    exit(1);
    break;
  }
}

static void setVariable(struct Symbol *symbol, int reg) {
  // TODO: generate code that moves a value into a variable's address
  // on the stack.  the variable may be in a parent scope, so first
  // generate code that finds the variable's scope's stack frame by
  // following the static links.

  int level_difference = (current_scope->level) - symbol->scope->level;
  if(level_difference > 0) {
    emit(VM_PSH(FP, SP));

    int iter = level_difference;  
    while(iter-->0) {
      emit(VM_LD(FP, FP, -2)); 
    }
    emit(VM_ST(reg, FP, symbol->address));
    emit(VM_POP(FP, SP)); 
  } else {
    emit(VM_ST(reg, FP, symbol->address));
  }
}

static void visitAssignStatement(struct Statement *node) {
  // given
  struct Symbol *symbol = node->assign_symbol;
  int assigned_reg = visitExpression(node->assign_expression, node->assign_expression->ershov - 1);

  setVariable(symbol, assigned_reg);
}

static void setupFunctionCall(struct Symbol *fsymbol, struct ExpressionList *parameters, int reg_base) {
  // TODO: allocate space for the parameters
  if(parameters->size > 0) emit(VM_ADDI(SP, SP, parameters->size));

  // according to codegen, evaluate each expression and store their results on the stack
  struct ExpressionListElement *cur = parameters->head;
  int i=0;
  while(NULL!=cur) {
    int reg_val = visitExpression(cur->node, cur->node->ershov - 1);
    emit(VM_ST(reg_val, SP, -i++));
    cur = cur->next;
  }


  // TODO: allocate space for the return value
  emit(VM_ADDI(SP, SP, 1));

  // TODO: allocate space for the static link and set the static link.
  // the static link depends on the scope of the function being
  // called.
  //emit(VM_ADDI(SP, SP, 1)); // unsure

  if (fsymbol->scope->level == current_scope->level)  {
    emit(VM_PSH(FP, SP));
  } else {
    int level_difference = (current_scope->level - 1) - fsymbol->scope->level;
    if (level_difference >= 0) {
      // TODO
      emit(VM_LD(0, FP, -2));
      int iter = level_difference;
      while(iter-->0) {
        emit(VM_LD(0, 0, -2));
      }
      emit(VM_PSH(0, SP));
    } else {
      error(0, 0, "nesting depth of callee should not be more than one level deeper than caller");
      exit(1);
    }
  }

  // TODO: emit the branch and link to the function's code index
  // (recall that branches are relative)

  emit(VM_BL(-(code_index-fsymbol->address))); // NOT SURE IF CORRECT
  // emit code to tear down the stack
  // TODO: deallocate space for the static link
  emit(VM_SUBI(SP, SP, 1));
  // TODO: pop the return value into reg_base
  emit(VM_POP(reg_base, SP));
  // TODO: deallocate space for the parameters
  if(parameters->size > 0) emit(VM_SUBI(SP, SP, parameters->size));
}

static void visitCallStatement(struct Statement *node) {
  // given
  struct Symbol *fsymbol = node->call_symbol;
  struct ExpressionList *parameters = node->call_parameters;
  // since this is a statement, we know that no intermediate values
  // will be in registers.  so just use r0, though we don't need the
  // return value for a call statement
  int reg_base = 0;  // put result in r0
  setupFunctionCall(fsymbol, parameters, reg_base);
}

static void visitReturnStatement(struct Statement *node) {
  // TODO: generate code for the return statement. recall that the
  // function's symbol is stored as an attribute on the return
  // statement node. store the result in the stack slot for the return
  // value (FP - 3), i.e., OFFSET_RET_VAL
  int reg_val = visitExpression(node->return_expression, node->return_expression->ershov-1);
  emit(VM_ST(reg_val, FP, OFFSET_RET_VAL));
  emit(VM_MOV(SP, FP));
  emit(VM_POP(FP, SP));
  emit(VM_POP(LN, SP));
  emit(VM_RET(LN));
  //emit(VM_RET(reg_val)); //?
}

static void visitCompoundStatement(struct Statement *node) {
  // given
  struct StatementListElement *cur = node->compound_statement->head;
  while (NULL != cur) {
    visitStatement(cur->node);
    cur = cur->next;
  }
}

static void visitIfStatement(struct Statement *node) {
  // TODO

  // first evaluate the expression, recording the register in which the result is stored
  int result_reg = visitExpression(node->if_condition, node->if_condition->ershov-1);

  // emit a comparison, i.e., cmpi reg 1
  emit(VM_CMPI(result_reg, 1));

  // emit a branch to skip the if body when comparison is false.  be
  // sure to store save the result of the emit, i.e., the index of the
  // branch instruction, for later backpatching.
  int save_ind_if = emit(VM_BNE(1));

  // process the body of the if
  visitStatement(node->if_branch);

  // emit a branch to skip the else body, again saving the index for
  // later backpatching.
  int save_ind_else = emit(VM_BR(1));

  // backpatch the first branch (the one that skips the if body) to
  // jump to the current code index.  remember that branchs are
  // relative, i.e., don't backpatch it to the current code_index, but
  // instead the difference between the current code_index and the
  // index of the branch instruction.
  backpatch(save_ind_if, code_index - save_ind_if);

  // process the else branch if it exists
  if(node->if_elsebranch!=NULL) visitStatement(node->if_elsebranch);
  
  // backpatch the second branch (that skips the else body)
  backpatch(save_ind_else, code_index - save_ind_else);
}

static void visitWhileStatement(struct Statement *node) {
  int save_ind_cond = code_index;

  // TODO (somewhat similar to if)
  // first evaluate the expression, recording the register in which the result is stored
  int result_reg = visitExpression(node->while_condition, node->while_condition->ershov-1);
  
  // emit a comparison, i.e., cmpi reg 1
  emit(VM_CMPI(result_reg, 1));

  // emit a branch to skip the if body when comparison is false.  be
  // sure to store save the result of the emit, i.e., the index of the
  // branch instruction, for later backpatching.
  int jump = emit(VM_BNE(1));

  // process the body of the if
  visitStatement(node->while_body);


  // backpatch the first branch (the one that skips the if body) to
  // jump to the current code index.  remember that branchs are
  // relative, i.e., don't backpatch it to the current code_index, but
  // instead the difference between the current code_index and the
  // index of the branch instruction.
  emit(VM_BR(-(code_index - save_ind_cond)));
  backpatch(jump, code_index - jump);
}

static void visitReadStatement(struct Statement *node) {
  // TODO
  emit(VM_READ(0));
  setVariable(node->read_symbol, 0);
}

static void visitWriteStatement(struct Statement *node) {
  // given
  int reg = visitExpression(node->write_expression, node->write_expression->ershov - 1);
  emit(VM_WR(reg));
}

static int visitExpression(struct Expression *node, int reg_base) {
  if ((reg_base + node->ershov) > 11) {
    /* Some expressions may require storing more intermediate results
       than there are available registers.  It is left as an optional exercise
       to allocate extra space in the stack frame for the temporary
       variables. */
    error(0, 0, "expression requires too many registers, please rewrite the source code using extra local variables");
    exit(1);
  }
  if (BINARYEXPRESSION == node->kind) {
    if (isInt(node->datatype)) {
      return visitBinaryExpressionInt(node, reg_base);
    } else if (isBool(node->datatype)) {
      return visitBinaryExpressionBool(node, reg_base);
    } else {
      assert(false); // should not happen if typechecker is correct
    }
  } else if (UNARYEXPRESSION == node->kind) {
    // classroom
    if (isInt(node->datatype)) {
      return visitUnaryExpressionInt(node, reg_base);
    } else if (isBool(node->datatype)) {
      return visitUnaryExpressionBool(node, reg_base);
    } else {
      assert(false); // should not happen if typechecker is correct
    }
  } else if (NUMBERFACTOR == node->kind) {
    return visitNumberFactor(node, reg_base);
  } else if (BOOLEANFACTOR == node->kind) {
    return visitBooleanFactor(node, reg_base);
  } else if (VARIABLEFACTOR == node->kind) {
    return visitVariableFactor(node, reg_base);
  } else if (FUNCTIONFACTOR == node->kind) {
    return visitFunctionFactor(node, reg_base);
  } else {
    error(0, 0, "unknown option");
    exit(1);
  }
}

static int visitBinaryExpressionInt(struct Expression *node, int reg_base) {
  int right_reg;
  int left_reg;
  // use ershov numbers to determine the base registers for the left
  if(node->binary_left->ershov == node->binary_right->ershov) {
    right_reg = visitExpression(node->binary_right, reg_base-1);
    left_reg = visitExpression(node->binary_left, reg_base);
  }
  if(node->binary_left->ershov < node->binary_right->ershov) {
    right_reg = visitExpression(node->binary_right, reg_base);
    left_reg = visitExpression(node->binary_left, reg_base);
  }
  if(node->binary_left->ershov > node->binary_right->ershov) {
    left_reg = visitExpression(node->binary_left, reg_base);
    right_reg = visitExpression(node->binary_right, reg_base);
  }
  // and right children
  int result_reg = reg_base - node->ershov + 1;
  switch (node->binary_op->kind) {
  case PLUS:
    emit(VM_ADD(result_reg, left_reg, right_reg));
    // TODO
    break;
  case MINUS:
    emit(VM_SUB(result_reg, left_reg, right_reg));
    // TODO
    break;
  case MULT:
    emit(VM_MUL(result_reg, left_reg, right_reg));
    // TODO
    break;
  case DIV:
    emit(VM_DIV(result_reg, left_reg, right_reg));
    // TODO
    break;
  case MOD:
    emit(VM_MOD(result_reg, left_reg, right_reg));
    // TODO
    break;
  default:
    assert(false);  // not supposed to happen if parser and typechecker are correct */
    break;
  }
  
  return result_reg;
}

static int visitUnaryExpressionInt(struct Expression *node, int reg_base) {
  int result_reg = visitExpression(node->unary_expression, reg_base);
  struct DataType *operand_type = node->unary_expression->datatype;
  switch (node->unary_op->kind) {
  case MINUS:
    emit(VM_MULI(result_reg, result_reg, -1));
    break;
  default:
    assert(false);  // not supposed to happen if parser and typechecker are correct */
    break;
  }
  return result_reg;
}

static int visitBinaryExpressionBool(struct Expression *node, int reg_base) {
  // TODO
  int right_reg;
  int left_reg;
  // use ershov numbers to determine the base registers for the left
  if(node->binary_left->ershov == node->binary_right->ershov) {
    right_reg = visitExpression(node->binary_right, reg_base-1);
    left_reg = visitExpression(node->binary_left, reg_base);
  }
  if(node->binary_left->ershov < node->binary_right->ershov) {
    right_reg = visitExpression(node->binary_right, reg_base);
    left_reg = visitExpression(node->binary_left, reg_base);
  }
  if(node->binary_left->ershov > node->binary_right->ershov) {
    left_reg = visitExpression(node->binary_left, reg_base);
    right_reg = visitExpression(node->binary_right, reg_base);
  }

  

  // and right children
  int result_reg = reg_base - node->ershov + 1;
  switch (node->binary_op->kind) {
  case LT:
    // TODO: classroom exercise, use compare and branch to implement boolean operations
    emit(VM_CMP(left_reg, right_reg));
    emit(VM_BLT(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  case LTE:
    // TODO
    emit(VM_CMP(left_reg, right_reg));
    emit(VM_BLE(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  case GT:
    // TODO
    emit(VM_CMP(left_reg, right_reg));
    emit(VM_BGT(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  case GTE:
    // TODO
    emit(VM_CMP(left_reg, right_reg));
    emit(VM_BGE(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  case AND:
    // TODO
    emit(VM_CMPI(left_reg, 0));
    emit(VM_BEQ(5));
    emit(VM_CMPI(right_reg, 0));
    emit(VM_BEQ(3));
    emit(VM_MOVI(result_reg, 1));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 0));
    break;
  case OR:
    // TODO
    emit(VM_CMPI(left_reg, 1));
    emit(VM_BEQ(5));
    emit(VM_CMPI(right_reg, 1));
    emit(VM_BEQ(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  case EQ:
    // TODO
    emit(VM_CMP(left_reg, right_reg));
    emit(VM_BEQ(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  case NEQ:
    // TODO
    emit(VM_CMP(left_reg, right_reg));
    emit(VM_BNE(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  default:
    assert(false);  // not supposed to happen if parser and typechecker are correct */
    break;
  }

  return result_reg;
}

static int visitUnaryExpressionBool(struct Expression *node, int reg_base) {
  // classroom exercise
  int result_reg = visitExpression(node->unary_expression, reg_base);
  struct DataType *operand_type = node->unary_expression->datatype;
  switch (node->unary_op->kind) {
  case NOT:
    emit(VM_CMPI(result_reg, 0));
    emit(VM_BEQ(3));
    emit(VM_MOVI(result_reg, 0));
    emit(VM_BR(2));
    emit(VM_MOVI(result_reg, 1));
    break;
  default:
    assert(false);  // not supposed to happen if parser and typechecker are correct */
    break;
  }
  return result_reg;
}

static int visitNumberFactor(struct Expression *node, int reg_base) {
  emit(VM_MOVI(reg_base, node->number_value));
  return reg_base;
}

static int visitBooleanFactor(struct Expression *node, int reg_base) {
  // TODO: generate code for a boolean constant.  1 is true, 0 is false.
  if(node->boolean_value) {
    emit(VM_MOVI(reg_base, 1));
  } else {
    emit(VM_MOVI(reg_base, 0));
  }
  return reg_base;
}

static int visitVariableFactor(struct Expression *node, int reg_base) {
  // TODO
  struct Symbol *symbol = node->variable_symbol;

  // similarly to assignment, first need to generate code that finds
  // follows the stack frame for the scope of the variable.  then
  // store the value in reg_base.

  int level_difference = (current_scope->level) - symbol->scope->level;
  if(level_difference > 0) {
    emit(VM_MOV(reg_base, FP));
  } else {
    emit(VM_LD(reg_base, FP, symbol->address));
  }

  int iter = level_difference;  
  while(iter-->0) {
    emit(VM_LD(reg_base, reg_base, -2)); 
  }    
  if(level_difference>0)emit(VM_LD(reg_base, reg_base, symbol->address));
  
  return reg_base;
}

static int visitFunctionFactor(struct Expression *node, int reg_base) {
  // given
  struct Symbol *fsymbol = node->function_symbol;
  struct ExpressionList *parameters = node->function_parameters;

  // push any registers that hold temporary values
  for (int i = 0; i < reg_base; i++) {
    code[code_index++] = VM_PSH(i, SP);
  }

  setupFunctionCall(fsymbol, parameters, reg_base);

  // pop any registers that hold temporary values
  for (int i = reg_base - 1; i >= 0; i--) {
    code[code_index++] = VM_POP(i, SP);
  }

  return reg_base;
}

static int emit(Instruction instr) {
  code[code_index] = instr;
  return code_index++;  // return the index of the instr, before incrementing it
}

static void backpatch(int branch_instruction_address, int new_disp) {
  code[branch_instruction_address].arg1 = new_disp;
}
