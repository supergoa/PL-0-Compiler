#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <error.h>
#include <assert.h>

#include "lexer.h"
#include "ast.h"
#include "parser.h"
#include "symtab.h"
#include "typechecker.h"

static void visitTranslationUnit(struct TranslationUnit *node);
static void visitBlock(struct Block *node);
static void visitVarDecl(struct TypedIdent *node);
static void visitVarDecls(struct TypedIdentList *list);
static void visitFuncDecl(struct FuncDecl *node);
static void visitFormal(struct TypedIdent *node);
static void visitFormals(struct TypedIdentList *list);
static void visitFuncDeclList(struct FuncDeclList *list);
static void visitStatement(struct Statement *node);
static void visitAssignStatement(struct Statement *node);
static void visitCallStatement(struct Statement *node);
static void visitReturnStatement(struct Statement *node);
static void visitCompoundStatement(struct Statement *list);
static void visitIfStatement(struct Statement *node);
static void visitWhileStatement(struct Statement *node);
static void visitReadStatement(struct Statement *node);
static void visitWriteStatement(struct Statement *node);
static void visitExpressionList(struct ExpressionList *list);
static void visitExpression(struct Expression *node);
static void visitBinaryExpression(struct Expression *node);
static void visitUnaryExpression(struct Expression *node);
static void visitNumberFactor(struct Expression *node);
static void visitBooleanFactor(struct Expression *node);
static void visitVariableFactor(struct Expression *node);
static void visitFunctionFactor(struct Expression *node);

void typechecker(struct TranslationUnit *ast) {
  // printf("helllllllllllllllllllllo?/n");
  visitTranslationUnit(ast);
}

static struct Scope *global_scope = NULL;

static struct Scope *current_scope = NULL;

//static struct Scope *previous_scope = NULL; // I made this, not part of orig proj

#include "typechecker_tools.c"

static void visitTranslationUnit(struct TranslationUnit *node) {
  // given
  //printf("start of program");
  global_scope = addScope("<GLOBAL>", NULL);
  current_scope = global_scope;
  node->scope = current_scope;
  visitBlock(node->block);
}

static void visitBlock(struct Block *node) {
  //printf("beforeVar");
  visitVarDecls(node->vardecls);
  // printf("beforeFunc");
  visitFuncDeclList(node->funcdecls);
  //  printf("beforeStatement");
  visitStatement(node->statement);
}

static void visitVarDecl(struct TypedIdent *node) {
  // TODO: use addVariable to add node->identifier to the symbol table under the current_scope
  // printf("adding variable %s, ", node->identifier); 
  node->symbol = addVariable(current_scope, node->identifier, node);
}

static void visitVarDecls(struct TypedIdentList *list) {
  // given
  struct TypedIdentListElement *cur = list->head;
  while (NULL != cur) {
    visitVarDecl(cur->node);
    cur = cur->next;
  }
}

static void visitFuncDecl(struct FuncDecl *node) {
  /* node->identifier; */
  // TODO: add the function to the current scope using addFunction

  // printf("adding function %s", node->identifier);
  addFunction(current_scope, node->identifier, node);
  node->symbol= getSymbol(current_scope, node->identifier);
  // int
  // TODO create a new nested scope with addScope() for the function
  // and include it's parameters in the scope. visit the function
  // node's children then restore the scope
  
  struct Scope *previous_scope = current_scope;
  current_scope = addScope(node->identifier, current_scope);
  node->scope = current_scope;
  
  visitFormals(node->formals);
  visitBlock(node->block);
  current_scope = previous_scope;
}

static void visitFormal(struct TypedIdent *node) {
  // TODO: add the formal variable's name to the current scope
  node->symbol = addVariable(current_scope, node->identifier, node);
  // node->symbol = getSymbol(current_scope, node->identifier);
}

static void visitFormals(struct TypedIdentList *list) {
  // given
  struct TypedIdentListElement *cur = list->head;
  while (NULL != cur) {
    visitFormal(cur->node);
    cur = cur->next;
  }
}

static void visitFuncDeclList(struct FuncDeclList *list) {
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

#define ASSIGN_VAR_NOT_FOUND "variable not found in assignment"
#define ASSIGN_INCORRECT_TYPE "incorrect type assigned to variable"
static void visitAssignStatement(struct Statement *node) {
  visitExpression(node->assign_expression);

  // TODO: look for the variable name (assign_variable) in the current scope.
  node->assign_symbol = searchSymbol(current_scope, node->assign_variable);
  // if it's not found or it's type doesn't match the right-hand-side,
  // throw the appropriate type err (one of the macros above)
  if(node->assign_symbol==NULL) {
    type_error(ASSIGN_VAR_NOT_FOUND);
  }
  if(!equalTypes(node->assign_expression->datatype, node->assign_symbol->datatype)) {
    type_error(ASSIGN_INCORRECT_TYPE);
  }
}

bool checkExpressionList(struct ExpressionList *exprlist, struct TupleElement *param) {
  // given
  struct ExpressionListElement *expr = exprlist->head;
  while (NULL != expr && NULL != param) {
    if (!equalTypes(expr->node->datatype, param->type)) {
      return false;
    }

    expr = expr->next;
    param = param->next;
  }

  if (NULL != expr || NULL != param) {
    return false;
  }

  return true;
}

#define CALL_FUNC_NOT_FOUND "function not found"
#define CALL_MISMATCHED_ARGUMENTS "incorrect arguments to function"
static void visitCallStatement(struct Statement *node) {
  visitExpressionList(node->call_parameters);

  node->call_symbol = searchSymbol(current_scope, node->call_function);
  if(node->call_symbol == NULL) {
    type_error(CALL_FUNC_NOT_FOUND);
  }
  if(!checkExpressionList(node->call_parameters, node->call_symbol->datatype->params->tuple_head)) {
    type_error(CALL_MISMATCHED_ARGUMENTS);
  }

  // TODO: check that the function call parameters use the correct
  // types.  somewhat similar to visitAssignStatement.  use
  // checkExpressionList, which takes an already type-checked
  // expression list and a TupleElement (from
  // symbol->datatype->params->tuple_head) and compare each element in
  // the lists.  be sure to throw one of the two errors above if the
  // symbol is not a type or the parameter usage is incorrect.
}

#define RETURN_FROM_GLOBAL_SCOPE "attempted return from global scope"
#define RETURN_INCORRECT_TYPE "type of return value does not match function"
static void visitReturnStatement(struct Statement *node) {
  visitExpression(node->return_expression);

  node->function_symbol = searchSymbol(current_scope, current_scope->name);
  if(node->function_symbol == NULL) {
    type_error(RETURN_FROM_GLOBAL_SCOPE);
  }
  if(!equalTypes(node->function_symbol->datatype->return_type, node->return_expression->datatype)) {
    type_error(RETURN_INCORRECT_TYPE);
  }
  // TODO: look at current scope, get the function return type (by looking
  // at parent scope).  return type and type of expression should
  // match
}

static void visitCompoundStatement(struct Statement *node) {
  // given
  struct StatementListElement *cur = node->compound_statement->head;
  while (NULL != cur) {
    visitStatement(cur->node);
    cur = cur->next;
  }
}

#define CONDITION_NOT_BOOL "condition expression is not a boolean"
static void visitIfStatement(struct Statement *node) {
  visitExpression(node->if_condition);
  visitStatement(node->if_branch); // should this be here?
  if(node->if_elsebranch != NULL) visitStatement(node->if_elsebranch); // should this be here?
  
  if(!isBool(node->if_condition->datatype)) {
    type_error(CONDITION_NOT_BOOL);
  }
  // TODO: type check the if statement.  be sure to call the correct
  // visitors for its children.  throw the above error when necessary.
}

static void visitWhileStatement(struct Statement *node) {
  visitExpression(node->while_condition);
  visitStatement(node->while_body);

  if(!isBool(node->while_condition->datatype)) {
    type_error(CONDITION_NOT_BOOL);
  }
  // TODO: type check the while statement.  be sure to call the correct
  // visitors for its children.  throw the CONDITION_NOT_BOOL error when necessary.
}

#define READ_VAR_NOT_FOUND "variable not found in read"
static void visitReadStatement(struct Statement *node) {
  node->read_symbol = searchSymbol(current_scope, node->read_variable);
  if(node->read_symbol == NULL || !isPrimitiveType(node->read_symbol->datatype)) {
    type_error(READ_VAR_NOT_FOUND);
  }
  // TODO: find the type of the variable used for to store the read
  // and update the read statement's symbol accordingly, using the
  // error above when necessary.
}

static void visitWriteStatement(struct Statement *node) {
  visitExpression(node->write_expression);
  // TODO: what needs checking?
}

static void visitExpressionList(struct ExpressionList *list) {
  // TODO: very similar to visitFuncDeclList
  //printf("called!\n");
  struct ExpressionListElement *cur = list->head;
  while (NULL != cur) {
    // printf("inside!\n");
    visitExpression(cur->node);
    cur = cur->next;
  }
}

static void visitExpression(struct Expression *node) {
  if (BINARYEXPRESSION == node->kind) {
    visitBinaryExpression(node);
    // TODO: set ershov number
    if(node->binary_left->ershov == node->binary_right->ershov) {
      node->ershov = node->binary_left->ershov+1;
    } else if(node->binary_left->ershov > node->binary_right->ershov) {
      node->ershov = node->binary_left->ershov;
    } else {
      node->ershov = node->binary_right->ershov;
    }
  } else if (UNARYEXPRESSION == node->kind) {
    visitUnaryExpression(node);
    // TODO: set ershov number
    node->ershov = node->unary_expression->ershov;
  } else if (NUMBERFACTOR == node->kind) {
    visitNumberFactor(node);
    // TODO: set ershov number
    node->ershov = 1;
  } else if (BOOLEANFACTOR == node->kind) {
    visitBooleanFactor(node);
    // TODO: set ershov number
    node->ershov = 1;
  } else if (VARIABLEFACTOR == node->kind) {
    visitVariableFactor(node);
    // TODO: set ershov number
    node->ershov = 1;
  } else if (FUNCTIONFACTOR == node->kind) {
    visitFunctionFactor(node);
    // TODO: set ershov number
    node->ershov = 1;
  } else {
    error(0, 0, "unknown option");
    exit(1);
  }
}

#define EXPRESSION_TYPE_MISMATCH "operand(s) do not match in expression"
#define EXPRESSION_EXPECTED_INT "expected int type for integer operation"
#define EXPRESSION_EXPECTED_BOOL "expected bool type for boolean operation"
static void visitBinaryExpression(struct Expression *node) {
  // TODO: traverse children and check types
  visitExpression(node->binary_left);
  visitExpression(node->binary_right);

  if(!equalTypes(node->binary_left->datatype, node->binary_right->datatype)) {
    type_error(EXPRESSION_TYPE_MISMATCH);
  }
  
  struct DataType *operands_type = node->binary_left->datatype;
  switch (node->binary_op->kind) {
  case PLUS:
    // fall-through
  case MINUS:
    // fall-through
  case MULT:
    // fall-through
  case DIV:
    // fall-through
  case MOD:
    // TODO: check usage of arithmetic operators (what are their types?)
    if(isInt(operands_type)) {
      node->datatype = getInt();
    } else {
      type_error(EXPRESSION_EXPECTED_INT);
    }
    break;
  case LT:
    // fall-through
  case LTE:
    // fall-through
  case GT:
    // fall-through
  case GTE:
    // TODO: check usage of relational operators (what are their types?)
    if(isInt(operands_type)) {
      node->datatype = getBool();
    } else {
      type_error(EXPRESSION_EXPECTED_INT);
    }
    break;
  case AND:
    // fall-through
  case OR:
    // TODO: check usage of boolean ops (what are their types?)
    if(isBool(operands_type)) {
      node->datatype = getBool();
    } else {
      type_error(EXPRESSION_EXPECTED_BOOL);
    }
    break;
  case EQ:
    // fall-through
  case NEQ:
    // TODO: check usage of boolean ops
    // either type is okay (operator overloading)
    // but types must match, i.e., a, a -> bool, where a is a type parameter
    
    node->datatype = getBool();
    break;
  default:
    assert(false);  // not supposed to happen if parser is correct
    break;
  }
}

static void visitUnaryExpression(struct Expression *node) {
  visitExpression(node->unary_expression);
  struct DataType *operand_type = node->unary_expression->datatype;
  switch (node->unary_op->kind) {
  case MINUS:
    // int -> int
    if (isInt(operand_type)) {
      node->datatype = getInt();
    } else {
      type_error(EXPRESSION_EXPECTED_INT);
    }
    break;
  case NOT:
    // bool -> bool
    if (isBool(operand_type)) {
      node->datatype = getBool();
    } else {
      type_error(EXPRESSION_EXPECTED_BOOL);
    }
    break;
  default:
    assert(false);  // not supposed to happen if parser is correct
    break;
  }
}

static void visitNumberFactor(struct Expression *node) {
  // TODO: set the datatype
  // printf("in number fact\n");
  node->datatype = getInt();
}

static void visitBooleanFactor(struct Expression *node) {
  // TODO: set the datatype
   node->datatype = getBool();
}

#define EXPRESSION_VAR_NOT_FOUND "variable not found in expression"
#define EXPRESSION_FOUND_FUNC "function symbol used instead of variable"
static void visitVariableFactor(struct Expression *node) {
  // TODO: check that the symbol is a variable and annotate the node
  // with the symbol and datatype
  
  node->variable_symbol = searchSymbol(current_scope, node->variable);
  if(node->variable_symbol == NULL) {
    type_error(EXPRESSION_VAR_NOT_FOUND);
  }
  if(!isPrimitiveType(node->variable_symbol->datatype)) {
    type_error(EXPRESSION_FOUND_FUNC);
  }
  if(isInt(node->variable_symbol->datatype)) {
    node->datatype = getInt();
  } else {
    node->datatype = getBool();
  }
}

#define EXPRESSION_FUNC_NOT_FOUND "function not found in expression"
#define EXPRESSION_FOUND_VAR "variable symbol used instead of function"
static void visitFunctionFactor(struct Expression *node) {
  // TODO: similar to visitCallStatement and visitVariableFactor
  visitExpressionList(node->function_parameters);
  node->function_symbol = searchSymbol(current_scope, node->function_name);
  
  if(node->function_symbol == NULL) {
    type_error(EXPRESSION_FUNC_NOT_FOUND);
  }
  if(!isFuncType(node->function_symbol->datatype)) {
    type_error(EXPRESSION_FOUND_VAR);
  }
  // printf("if im here");
  if(isInt(node->function_symbol->datatype->return_type)) {
    node->datatype = getInt();
    //  printf("i must be here...1");
  } else if(isBool(node->function_symbol->datatype->return_type)){
    //  printf("i must be here...2");
    node->datatype = getBool();
  }
}
