#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

#include "lexer.h"
#include "ast.h"
#include "parser.h"

#include "parser_tools.c"

static struct TranslationUnit *program();
static struct  Block *block();
static struct  TypedIdentList *vardecls();
static struct  Token *type();
static struct  FuncDeclList *funcdecls();
static struct  TypedIdentList *formals();
static struct  Statement *statement();
static struct  ExpressionList *exprlist();
static struct  Expression *expr();
static struct  Expression *simpleexpr();
static struct  Expression *term();
static struct  Expression *factor();
bool static is_relop();
bool static is_termop();
bool static is_factorop();

struct TranslationUnit* parser(struct Token** token_list_in) {
  token_list = token_list_in;
  token_i = -1;

  return program();
}

// program      ::= block PERIOD
static struct  TranslationUnit *program() {
  // given
  struct TranslationUnit *node = newTranslationUnit();

  node->block = block();

  next();
  ensure_token(EOT);

  return node;
}

// block        ::= vardecls funcdecls statement
static struct  Block *block() {
  struct Block *node = newBlock();

  node->vardecls = vardecls();
  node->funcdecls = funcdecls();
  node->statement = statement();
  
  return node;
}

// vardecls     ::= { VAR IDENT COLON type }
static struct  TypedIdentList *vardecls() {
  struct TypedIdentList *list = newTypedIdentList();

  next();
  while(is_token(VAR)) {
    struct TypedIdent *node = newTypedIdent();

    next();
    ensure_token(IDENT);
    node->identifier = token()->identifier;

    next();
    ensure_token(COLON);

    node->type = type();

    next();
    addTypedIdent(list, node);
  }
 
  previous();
  return list;
}

// funcdelcs    ::= { FUNC IDENT LPAREN [ formals ] RPAREN [ COLON type ] block }
static struct  FuncDeclList *funcdecls() {
  struct FuncDeclList *list = newFuncDeclList();

  next();
  while(is_token(FUNC)) {
    struct FuncDecl *node = newFuncDecl();

    next();
    ensure_token(IDENT);
    node->identifier = token()->identifier;

    next();
    ensure_token(LPAREN);

    node->formals = formals();
    
    next();
    ensure_token(RPAREN);

    next();
    if(is_token(COLON)) {
	node->has_return = true;
	node->return_type = type();
    } else {
	previous();
    }
    
    node->block = block();

    addFuncDecl(list, node);
    next();
  }
 
  previous();
  return list;
}

// formals      ::= IDENT COLON type { COMMA IDENT COLON type }
static struct  TypedIdentList *formals() {
  struct TypedIdentList *list = newTypedIdentList();

  next();
  while(is_token(IDENT)) {
    struct TypedIdent *node = newTypedIdent();
    node->identifier = token()->identifier;
   
    next();
    ensure_token(COLON);

    node->type = type();

    next();
    addTypedIdent(list, node);

    if(is_token(COMMA)) {
      next();
    }
  }

  previous();
  return list;
}

// type         ::= INT | BOOL
static struct  Token *type() {
  // given
  next();
  if (is_token(INT) || is_token(BOOL)) {
    return token();
  } else {
    parse_error();
    return NULL;
  }
}

/*
statement    ::= [ IDENT ASSIGN expr
                 | IDENT LPAREN exprlist RPAREN
                 | RETURN expression
                 | BEGIN { statement } END
                 | IF expr THEN statement [ELSE expr]
                 | WHILE expr DO statement
                 | READ IDENT
                 | WRITE expression
                 ]
*/
static struct  Statement *statement() {
  // skeleton given to select which statement
  next();
  if (is_token(IDENT)) {

    char *name = token()->identifier;
    
    next();
    if (is_token(ASSIGN)) {
      
      struct Statement *node = newStatement(ASSIGNSTATEMENT);
      node->assign_variable = name;
      node->assign_expression = expr();

      return node;
      
    } else if (is_token(LPAREN)) {
      
      struct Statement *node = newStatement(CALLSTATEMENT);
      node->call_function = name;
      node->call_parameters = exprlist();

      next();
      ensure_token(RPAREN);

      return node;
      
    } else {
      parse_error();
      return NULL;
    }
  } else if (is_token(RETURN)) {

    struct Statement *node = newStatement(RETURNSTATEMENT);
    node->return_expression = expr();
    return node;
    
  } else if (is_token(BEGIN)) {

    struct Statement *node = newStatement(COMPOUNDSTATEMENT);
    struct StatementList *list = newStatementList();
    while(true) {
      struct Statement *add = statement();
      addStatement(list, add);
      if(lookahead_token(END)) {
	break;
      }
    }
    next();
    ensure_token(END);
    node->compound_statement = list;
    
    return node;
    
  } else if (is_token(IF)) {

    struct Statement *node = newStatement(IFSTATEMENT);
    node->if_condition = expr();

    next();
    ensure_token(THEN);

    node->if_branch = statement();

    next();
    if(is_token(ELSE)) {
      node->if_elsebranch = statement();
    } else {
      previous();
    }
   
    return node;
    
  } else if (is_token(WHILE)) {

    struct Statement *node = newStatement(WHILESTATEMENT);
    node->while_condition = expr();

    next();
    ensure_token(DO);

    node->while_body = statement();

    return node;
    
  } else if (is_token(READ)) {
    // given
    struct Statement *node = newStatement(READSTATEMENT);

    next();
    ensure_token(IDENT);
    node->read_variable = token()->identifier;
    return node;
    
  } else if (is_token(WRITE)) {
    // given
    struct Statement *node = newStatement(WRITESTATEMENT);
    node->write_expression = expr();
    return node;
    
  } else {
    parse_error();
    return NULL;
  }
}

// exprlist     ::= expr { COMMA expr }
static struct  ExpressionList *exprlist() {
  struct ExpressionList *node = newExpressionList();
  next();
  if(is_token(RPAREN)) {
    previous();
  } else {
    previous();
    addExpression(node, expr());
    next();
    while(is_token(COMMA)) {
      addExpression(node, expr());
      next();
    }
    previous();
  }
  return node;
}

// expr         ::= simpleexpr [ relop simpleexpr ]
static struct  Expression *expr() {
  // TODO: classroom exercise
  struct Expression *left = simpleexpr();

  next();
  if (is_relop()) {
    struct Expression *node = newExpression(BINARYEXPRESSION);

    node->binary_left = left;
    node->binary_op = token();
    node->binary_right = simpleexpr();
    
    return node;
  } else {
    previous();
    return left;
  }
}

// relop        ::= LT | LTE | GT | GTE | EQ | NEQ
bool static is_relop() {
  //given
  switch (token()->kind) {
  case LT:
    // fall-through
  case LTE:
    // fall-through
  case GT:
    // fall-through
  case GTE:
    // fall-through
  case EQ:
    // fall-through
  case NEQ:
    return true;
  default:
    return false;
  }
}

// simpleexpr   ::= term [ termop term ]
static struct  Expression *simpleexpr() {
  struct Expression *left = term();

  next();
  if (is_termop()) {
    struct Expression *node = newExpression(BINARYEXPRESSION);

    node->binary_left = left;
    node->binary_op = token();
    node->binary_right = term();
    
    return node;
  } else {
    previous();
    return left;
  }
}

// termop       ::= PLUS | MINUS | OR
bool static is_termop() {
  switch (token()->kind) {
  case PLUS:
    // fall-through
  case MINUS:
    // fall-through
  case OR:
      return true;
  default:
    return false;
  }
}

// term         ::= factor [ factorop factor ]
static struct Expression *term() {
  struct Expression *left = factor();
  next();
  if (is_factorop()) {
    struct Expression *node = newExpression(BINARYEXPRESSION);

    node->binary_left = left;
    node->binary_op = token();
    node->binary_right = factor();
    
    return node;
  } else {
    previous();
    return left;
  }
}

// factorop     ::= MULT | DIV | MOD | AND
bool static is_factorop() {
  switch (token()->kind) {
  case MULT:
    // fall-through
  case DIV:
    // fall-through
  case MOD:
    // fall-through
  case AND:
    return true;
  default:
    return false;
  }
}

static struct  Expression *factor() {
  next();
  if (is_token(IDENT)) {

    char *name = token()->identifier;
    struct Expression *node;
    next();
    if(is_token(LPAREN)) {
      node = newExpression(FUNCTIONFACTOR);
      node->function_name = name;
      node->function_parameters = exprlist();

      next();
      ensure_token(RPAREN);
    } else {
      previous();
      
      node = newExpression(VARIABLEFACTOR);
      node->variable = name;
    }

    return node;
  } else if (is_token(NUMBER)) {
    // given
    struct Expression *node = newExpression(NUMBERFACTOR);

    node->number_value = token()->number;
    return node;
    
  } else if (is_token(TRUE)) {
    // given
    struct Expression *node = newExpression(BOOLEANFACTOR);

    node->boolean_value = true;
    return node;
    
  } else if (is_token(FALSE)) {
    struct Expression *node = newExpression(BOOLEANFACTOR);
    
    node->boolean_value = false;
    return node;
    
  } else if (is_token(LPAREN)) {
    struct Expression *node = expr();

    next();
    ensure_token(RPAREN);
    
    return node;
    
  } else if (is_token(NOT) || is_token(MINUS)) {

    struct Expression *node = newExpression(UNARYEXPRESSION);
    node->unary_op = token();
    node->unary_expression = factor();
    return node;
    
  } else {
    parse_error();
    return NULL;
  }
}
