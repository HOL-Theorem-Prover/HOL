%{
#include <storage.h>
#include <node.h>
#include <hash.h>
#include <assoc.h>
#include <setjmp.h>
#define catch_err(c) {longjmp_on_err = 1; if(!setjmp(longjmp_buf))c; longjmp_on_err = 0;}

extern int longjmp_on_err;
extern jmp_buf longjmp_buf;

node_ptr parse_tree;
%}

%union {
  node_ptr node;
}

/* all of the terminal grammar symbols (tokens recognized
by the lexical analyzer) 
note: all binary operators associate from left to right
ops are listed from lowest to highest priority */

%left GOTO LET STEP EVAL RESET
%left ASYNC MODULE PROCESS MODTYPE LAMBDA CONTEXT EU AU EBU ABU
%left VAR DEFINE INIT TRANS INVAR FORMAT SPEC FAIRNESS ISA CONSTANT ASSIGN
%left INPUT OUTPUT IMPLEMENTS
%left BOOLEAN ARRAY OF SCALAR LIST OVER BDD
%left SEMI LP RP LB RB LCB RCB
%left EQDEF TWODOTS ATLINE
%left <node> FALSEEXP TRUEEXP
%left APROPOS SELF SIGMA
%left CASE ESAC COLON

%left <node> ATOM
%left <node> NUMBER
%left <node> QUOTE

%left  COMMA
%left  IMPLIES
%left  IFF
%left  OR
%left  AND
%left  NOT
%left  EX AX EF AF EG AG E A UNTIL EBF EBG ABF ABG BUNTIL
%left  APATH EPATH
%left  EQUAL LT GT LE GE
%left  UNION
%left  SETIN
%left  MOD
%left  PLUS MINUS
%left  TIMES DIVIDE
%left  UMINUS		/* supplies precedence for unary minus */
%left  NEXT SMALLINIT
%left  DOT



/* all nonterminals return a parse tree node */
%type <node> modules module declarations declaration var vlist
%type <node> type isa init trans invar define dlist spec fairness 
%type <node> neatomlist term subrange
%type <node> number expr caselist constant
%type <node> moduletype usertype neexprlist assign alist alhs neatomset
%type <node> input output implements netermlist neconstlist
%type <node> trace state

%start begin
%%
begin         : modules {parse_tree = $1;}
              | commandlist
              ;

modules       : module {$$ = cons($1,NIL);}
              | modules module {$$ = cons($2,$1);}
              ;


module        : MODULE moduletype declarations {$$ = new_node(MODULE,$2,$3);}
              ;

moduletype    : ATOM {$$ = new_node(MODTYPE,$1,NIL);}
              | ATOM LP neatomlist RP {$$ = new_node(MODTYPE,$1,$3);}
              ;

declarations  : {$$ = NIL;}
              | declarations declaration {$$ = cons($2,$1);}
              ;

declaration   : var
              | isa
              | init
              | trans
              | invar
              | define
              | spec
              | fairness
              | assign 
              | input
              | output
              | implements
              ;

implements    : IMPLEMENTS ATOM {$$ = new_node(IMPLEMENTS,$2,NIL);}
              ;

var           : VAR vlist {$$ = new_node(VAR,$2,NIL);}
              ;

input         : INPUT vlist {$$ = new_node(INPUT,$2,NIL);}
              ;

output        : OUTPUT netermlist SEMI {$$ = new_node(OUTPUT,$2,NIL);}
              ;

vlist         : {$$ = NIL;}
              | vlist term COLON type SEMI
                {$$ = cons(new_node(COLON,$2,$4),$1);}
              ;

type          : BOOLEAN {$$ = new_node(BOOLEAN,NIL,NIL);}
              | LCB neconstlist RCB {$$ = new_node(SCALAR,$2,NIL);}
              | usertype
              | ARRAY subrange OF type {$$ = new_node(ARRAY,$2,$4);}
              | PROCESS usertype {$$ = new_node(PROCESS,$2,NIL);}
              | subrange
              ;

usertype      : ATOM {$$ = new_node(MODTYPE,$1,NIL);}
              | ATOM LP neexprlist RP {$$ = new_node(MODTYPE,$1,$3);}
              ;

subrange      : number TWODOTS number {$$ = new_node(TWODOTS,$1,$3);}
              ;

isa           : ISA ATOM {$$ = new_node(ISA,$2,NIL);}
              ;

init          : INIT expr {$$ = new_node(INIT,$2,NIL);}
              ;

trans         : TRANS expr {$$ = new_node(TRANS,$2,NIL);}
              ;

invar         : INVAR expr {$$ = new_node(INVAR,$2,NIL);}
              ;

define        : DEFINE dlist {$$ = new_node(DEFINE,$2,NIL);}
              ;

dlist         : {$$ = NIL;}
              | dlist term EQDEF expr SEMI
                {$$ = cons(new_node(EQDEF,$2,$4),$1);}
              ;

assign        : ASSIGN alist {$$ = new_node(ASSIGN,$2,NIL);}
              ;

alist         : {$$ = NIL;}
              | alist alhs EQDEF expr SEMI
                {$$ = new_node(AND,$1,new_node(EQDEF,$2,$4));}
              ;

alhs          : term
              | NEXT LP term RP {$$ = new_node(NEXT,$3,NIL);}
              | SMALLINIT LP term RP {$$ = new_node(SMALLINIT,$3,NIL);}
              ;

spec          : SPEC expr {$$ = new_node(SPEC,$2,NIL);}
              ;

fairness      : FAIRNESS expr {$$ = new_node(FAIRNESS,$2,NIL);}
              ;


neconstlist   : constant {$$ = cons(find_atom($1),NIL);}
              | neconstlist COMMA constant {$$ = cons(find_atom($3),$1);}
              ;

neatomlist    : ATOM {$$ = cons(find_atom($1),NIL);}
              | neatomlist COMMA ATOM {$$ = cons(find_atom($3),$1);}
              ;

neexprlist    : expr {$$ = cons($1,NIL);}
              | neexprlist COMMA expr {$$ = cons($3,$1);}
              ;

netermlist    : term {$$ = cons($1,NIL);}
              | netermlist COMMA term {$$ = cons($3,$1);}
              ;

term          : ATOM
              | SELF {$$ = new_node(SELF,NIL,NIL);}
              | term DOT ATOM {$$ = new_node(DOT,$1,$3);}
              | term LB expr RB {$$ = new_node(ARRAY,$1,$3);}
              ;

number        : NUMBER
	      | PLUS NUMBER %prec UMINUS
		{ $$ = $2; }
	      | MINUS NUMBER %prec UMINUS
		{$2->left.inttype = -($2->left.inttype); $$ = $2;}

expr          : term
              | number
	      | subrange
	      | FALSEEXP
	      | TRUEEXP
	      | LP expr RP { $$ = $2; }
	      | expr IMPLIES expr { $$ = new_node(IMPLIES,$1,$3); }
	      | expr IFF expr { $$ = new_node(IFF,$1,$3); }
	      | expr OR expr { $$ = new_node(OR,$1,$3); }
	      | expr AND expr { $$ = new_node(AND,$1,$3); }
	      | NOT expr { $$ = new_node(NOT,$2,NIL); }
              | EX expr { $$ = new_node(EX,$2,NIL); }
              | AX expr { $$ = new_node(AX,$2,NIL); }
              | EF expr { $$ = new_node(EF,$2,NIL); }
              | AF expr { $$ = new_node(AF,$2,NIL); }
              | EG expr { $$ = new_node(EG,$2,NIL); }
              | AG expr { $$ = new_node(AG,$2,NIL); }
	      | A LB expr UNTIL expr RB { $$ = new_node(AU,$3,$5); }
	      | E LB expr UNTIL expr RB { $$ = new_node(EU,$3,$5); }
	      | A LB expr BUNTIL subrange expr RB
                       { $$ = new_node(ABU,new_node(AU,$3,$6),$5); }
	      | E LB expr BUNTIL subrange expr RB
                       { $$ = new_node(EBU,new_node(EU,$3,$6),$5); }
              | EBF subrange expr { $$ = new_node(EBF,$3,$2); }
              | ABF subrange expr { $$ = new_node(ABF,$3,$2); }
              | EBG subrange expr { $$ = new_node(EBG,$3,$2); }
              | ABG subrange expr { $$ = new_node(ABG,$3,$2); }
              | CASE caselist ESAC { $$ = $2; }
              | NEXT expr { $$ = new_node(NEXT,$2,NIL); }
              | expr PLUS expr { $$ = new_node(PLUS,$1,$3); }
              | expr MINUS expr { $$ = new_node(MINUS,$1,$3); }
              | expr TIMES expr { $$ = new_node(TIMES,$1,$3); }
              | expr DIVIDE expr { $$ = new_node(DIVIDE,$1,$3); }
              | expr MOD expr { $$ = new_node(MOD,$1,$3); }
              | expr EQUAL expr { $$ = new_node(EQUAL,$1,$3); }
              | expr LT expr { $$ = new_node(LT,$1,$3); }
              | expr GT expr { $$ = new_node(GT,$1,$3); }
              | expr LE expr { $$ = new_node(LE,$1,$3); }
              | expr GE expr { $$ = new_node(GE,$1,$3); }
              | LCB neatomset RCB { $$ = $2; } 
              | expr UNION expr { $$ = new_node(UNION,$1,$3); }
              | expr SETIN expr { $$ = new_node(SETIN,$1,$3); }
              | SIGMA LB ATOM EQUAL subrange RB expr
                { $$ = new_node(SIGMA,new_node(EQUAL,$3,$5),$7); }
	      ;


neatomset     : constant
              | neatomset COMMA constant {$$ = new_node(UNION,$1,$3);}
              ; 

constant      : ATOM
              | number
	      | FALSEEXP
	      | TRUEEXP
              ;

caselist      : {$$=new_node(TRUEEXP,NIL,NIL);}
              | expr COLON expr SEMI caselist
                {
	          $$ = new_node(CASE,new_node(COLON,$1,$3),$5);
	        }
              ;

commandlist   : command
              | commandlist command
              ;

command       : SPEC expr SEMI {catch_err(check_spec($2))}
              | GOTO state SEMI {catch_err(goto_state($2))}
              | LET term EQDEF expr SEMI {catch_err(assign_command($2,$4))}
              | STEP SEMI {catch_err(single_step())}
              | EVAL expr SEMI {catch_err(eval_command($2))}
              | INIT expr SEMI {catch_err(init_command($2))}
              | FAIRNESS expr SEMI {catch_err(fair_command($2))}
              | TRANS expr SEMI {catch_err(trans_command($2))}
              | RESET SEMI {catch_err(reset_command())}
              | error SEMI {yyerrok;}
              ;

trace         : NUMBER {$$ = (node_ptr)find_atom($1);}
              | state DOT NUMBER {$$ = find_node(DOT,$1,find_atom($3));}
              ;

state         : trace DOT NUMBER {$$ = find_node(DOT,$1,find_atom($3));}
              ;
%%
