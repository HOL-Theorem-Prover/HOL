/***************************************************************************\
*                                                                           *
* Changed to implement bounded until - Sergio Campos - 05/92                *
*                                                                           *
* Changed implementation of bounded for SMV 2.3                             *
*   - steed@iil.intel.com - 07/92                                           *
*                                                                           *
* Corrected implementation of bounded for SMV 2.4                           *
*   - steed@iil.intel.com - 10/92                                           *
\***************************************************************************/

#include <stdio.h>
#include <storage.h>
#include <string.h>
#include <node.h>
#include <hash.h>
#include <bdd.h>
#include <assoc.h>
#include <grammar.tab.h>

static hash_ptr module_hash;
static hash_ptr symbol_hash;
static hash_ptr param_hash;
static hash_ptr constant_hash;
static hash_ptr print_hash;
static hash_ptr assign_hash;
static hash_ptr global_assign_hash;
static hash_ptr frame_hash;
static hash_ptr value_hash;
static hash_ptr state_hash;
static int enforce_constant = 0;
static node_ptr module_stack = NIL;
static node_ptr variables = NIL;
static node_ptr all_symbols = NIL;
static node_ptr heuristic_order = NIL;
static bdd_ptr vars,input_vars;
static int is_input_decl = 0;
static int assign_type;
static int instantiate_mode;
static node_ptr the_impl;
static node_ptr real_state_variables = NIL;
int option_kripke = 1;

#define NSTBASE 16
int nstvars = NSTBASE,real_nstvars=0,nstbase=NSTBASE;
#define MAXSTVARS 500
#define EVALUATING ((bdd_ptr)(-1))
#define TYPE_ERROR ((node_ptr)(-1))
extern int verbose;
extern int indent_size;
extern int yylineno;
extern node_ptr parse_tree;
extern int option_incremental;

static bdd_ptr eval();
static bdd_ptr trans;	/* TRANS expr, ASSIGN next(v) := expr */
static bdd_ptr invar;	/* ASSIGN v := expr (normal assignments) */
static bdd_ptr init;	/* INIT expr, ASSIGN init(v) := expr */
static bdd_ptr frame;
extern int option_conj_part,conj_part_limit;
static node_ptr cp_trans,forward_quantifiers,reverse_quantifiers;
static bdd_ptr reachable_states = (bdd_ptr)0;
static node_ptr fairness_const = NIL;
static bdd_ptr fair_states = (bdd_ptr)0;
static bdd_ptr proc_selector;
static bdd_ptr running;
static node_ptr the_node;
static node_ptr boolean_type;
static node_ptr zero_number,one_number;
static node_ptr running_atom;


static bdd_ptr orig_trans,orig_init;
static node_ptr orig_fairness_const;

node_ptr string_to_atom(s)
char *s;
{
  return(find_node(ATOM,find_string(s),NIL));
}

node_ptr find_atom(a)
node_ptr a;
{
  if(a == NIL)return(a);
  return(find_node(a->type,a->left.nodetype,a->right.nodetype));
}

static int eval_num(e,context)
node_ptr e,context;
{
  node_ptr n;
  bdd_ptr d;
  int temp = enforce_constant;
  enforce_constant = 1;
  d = eval(e,context);
  enforce_constant = temp;
  if(!ISLEAF(d))catastrophe("eval_num: !ISLEAF(d)");
  n=(node_ptr)(d->left);
  if(n->type != NUMBER)rpterr("numeric constant required");
  enforce_constant = temp;
  return(n->left.inttype);
}


bdd_ptr get_definition(n)
node_ptr n;
{
  node_ptr def = find_assoc(symbol_hash,n);
  bdd_ptr res;
  if(!def)return((bdd_ptr)0);
  if(enforce_constant && def->type == VAR)rpterr("constant required");
  if(def->type == BDD || def->type == VAR)
    return(save_bdd((bdd_ptr)car(def)));
  res = (bdd_ptr)find_assoc(value_hash,n);
  if(res == EVALUATING)circular(n);
  if(res)return(save_bdd(res));
  if(verbose > 1){
    indent_size++;
    indent_node(stderr,"evaluating ",n,":\n");
  }
  insert_assoc(value_hash,n,EVALUATING);
  push_atom(n);
  res = eval(def,NIL);
  pop_atom(n);
  insert_assoc(value_hash,n,save_bdd(res));
  if(verbose > 1){
    indent_node(stderr,"size of ",n," = ");
    fprintf(stderr,"%d BDD nodes\n",size_bdd(res));
    indent_size--;
  }
  return(res);
}

static bdd_ptr eval_sign(a,flag)
bdd_ptr a;
int flag;
{
  switch(flag){
  case -1: return(not_bdd(a));
  default: return(a);
  }
}

static bdd_ptr unary_op(op,n,resflag,argflag,context)
bdd_ptr (*op)();
node_ptr n,context;
int resflag,argflag;
{
  bdd_ptr arg = eval(car(n),context);
  release_bdd(arg);
  the_node = n;
  return(save_bdd(eval_sign(op(eval_sign(arg,argflag)),resflag)));
}

static bdd_ptr binary_op(op,n,resflag,argflag1,argflag2,context)
bdd_ptr (*op)();
node_ptr n,context;
int resflag,argflag1,argflag2;
{
  bdd_ptr arg1 = eval(car(n),context);
  bdd_ptr arg2 = eval(cdr(n),context);
  release_bdd(arg1);
  release_bdd(arg2);
  the_node = n;
  return(save_bdd(eval_sign(op(eval_sign(arg1,argflag1),
			       eval_sign(arg2,argflag2)),
			    resflag)));
}

static bdd_ptr ternary_op(op,n,resflag,argflag,context)
bdd_ptr (*op)();
node_ptr n,context;
int resflag,argflag;
{
  bdd_ptr arg1 = eval(car(n),context);
  int arg2 = eval_num(car(cdr(n)),context);
  int arg3 = eval_num(cdr(cdr(n)),context);

  release_bdd(arg1);
  the_node = n;
  return(save_bdd(eval_sign(op(eval_sign(arg1,argflag),
                               arg2, arg3),
                            resflag)));
}

static bdd_ptr quad_op(op, n, resflag, argflag1, argflag2, context)
bdd_ptr (*op)();
node_ptr n,context;
int resflag,argflag1,argflag2;
{
  bdd_ptr arg1 = eval(car(car(n)), context);
  bdd_ptr arg2 = eval(cdr(car(n)), context);
  int arg3 = eval_num(car(cdr(n)), context);
  int arg4 = eval_num(cdr(cdr(n)), context);

  release_bdd(arg1);
  release_bdd(arg2);
  the_node = n;
  return(save_bdd(eval_sign(op(eval_sign(arg1,argflag1),
			       eval_sign(arg2,argflag2),
			       arg3, arg4),
			    resflag)));
}

static bdd_ptr eval_if_then_else(ifexp,thenexp,elseexp,context)
node_ptr ifexp,thenexp,elseexp,context;
{
  bdd_ptr ifarg = eval(ifexp,context);
  bdd_ptr thenarg = eval(thenexp,context);
  bdd_ptr elsearg = eval(elseexp,context);
  release_bdd(ifarg);
  release_bdd(thenarg);
  release_bdd(elsearg);
  return(save_bdd(if_then_else_bdd(ifarg,thenarg,elsearg)));
}

static node_ptr eval_struct();
static node_ptr eval_struct1(n,context)
node_ptr n,context;
{
  node_ptr temp,name;
  switch(n->type){
  case CONTEXT: return(eval_struct(cdr(n),car(n)));
  case ATOM:
    name = find_node(DOT,context,find_atom(n));
    if(temp = find_assoc(param_hash,name))
      return(eval_struct(temp,context));
    return(name);
  case DOT:
    temp = eval_struct(car(n),context);
    if(temp == TYPE_ERROR)rpterr("type error, operator = .");
    return(find_node(DOT,temp,find_atom(cdr(n))));
  case ARRAY:
    temp = eval_struct(car(n),context);
    if(temp == TYPE_ERROR)rpterr("type error, operator = []");
    return(find_node(ARRAY,temp,
		     find_node(NUMBER,eval_num(cdr(n),context),NIL)));
  case SELF:
    return(context);
  default:
      return(TYPE_ERROR);
  }
}

static node_ptr eval_struct(n,context)
node_ptr n,context;
{
  node_ptr res;
  int temp = yylineno;
  if(n == NIL)return(NIL);
  yylineno = n->lineno;
  res = eval_struct1(n,context);
  yylineno = temp;
  return(res);
}

static bdd_ptr enforce_definition(n)
node_ptr n;
{
  bdd_ptr res;
  if(res = get_definition(n))return(res);
  undefined(n);
}

static node_ptr equal_node(n1,n2)
node_ptr n1,n2;
{
  if(n1 == n2)return(one_number);
  return(zero_number);
}

static bdd_ptr equal_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(equal_node,a,b));
}

static notanumber(n)
node_ptr n;
{
  start_err();
  fprintf(stderr,"not a number: ");
  print_node(stderr,n);
  finish_err();
}

static node_ptr numeric_op(op,n1,n2)
int (*op)();
node_ptr n1,n2;
{
  if(n1->type != NUMBER)notanumber(n1);
  if(n2->type != NUMBER)notanumber(n2);
  return(find_node(NUMBER,(*op)(car(n1),car(n2)),NIL));
}

static int plus_op(a,b)
int a,b;
{
  return(a+b);
}

static node_ptr plus_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(plus_op,n1,n2));
}

static bdd_ptr plus_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(plus_node,a,b));
}

static int minus_op(a,b)
int a,b;
{
  return(a-b);
}

static node_ptr minus_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(minus_op,n1,n2));
}

static bdd_ptr minus_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(minus_node,a,b));
}

static int times_op(a,b)
int a,b;
{
  return(a*b);
}

static node_ptr times_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(times_op,n1,n2));
}

static bdd_ptr times_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(times_node,a,b));
}

static int divide_op(a,b)
int a,b;
{
  int r = a%b;
  if(r<0)return(a/b-1);
  return(a/b);
}

static node_ptr divide_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(divide_op,n1,n2));
}

static bdd_ptr divide_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(divide_node,a,b));
}

static int mod_op(a,b)
int a,b;
{
  int r = a%b;
  if(r<0)r += b;
  return(r);
}

static node_ptr mod_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(mod_op,n1,n2));
}

static bdd_ptr mod_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(mod_node,a,b));
}


static node_ptr union_node(n1,n2)
node_ptr n1,n2;
{
  if(n1 != NIL && n1->type != LIST)n1 = find_node(LIST,n1,NIL);
  if(n2 != NIL && n2->type != LIST)n2 = find_node(LIST,n2,NIL);
  if(n1 == NIL)return(n2);
  if(n2 == NIL)return(n1);
  if(car(n1) == car(n2))
    return(find_node(LIST,car(n1),union_node(cdr(n1),cdr(n2))));
  if(((int)car(n1)) < ((int)car(n2)))
    return(find_node(LIST,car(n1),union_node(cdr(n1),n2)));
  return(find_node(LIST,car(n2),union_node(n1,cdr(n2))));
}

static bdd_ptr union_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(union_node,a,b));
}

static node_ptr setin_node(n1,n2)
node_ptr n1,n2;
{
  if(n2 == NIL)return(zero_number);
  if(n2->type != LIST){
    if(n1 == n2)return(one_number);
    return(zero_number);
  }
  if(n1 == car(n2))return(one_number);
  return(setin_node(n1,cdr(n2)));
}

static bdd_ptr setin_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(setin_node,a,b));
}

static int lt_op(a,b)
int a,b;
{
  if(a < b)return(1);
  return(0);
}

static node_ptr lt_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(lt_op,n1,n2));
}

static bdd_ptr lt_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(lt_node,a,b));
}

static int gt_op(a,b)
int a,b;
{
  if(a > b)return(1);
  return(0);
}

static node_ptr gt_node(n1,n2)
node_ptr n1,n2;
{
  return(numeric_op(gt_op,n1,n2));
}

static bdd_ptr gt_bdd(a,b)
bdd_ptr a,b;
{
  return(apply_bdd(gt_node,a,b));
}


bdd_ptr cp_reverse(g)
bdd_ptr g;
{
  if(!option_conj_part)return(collapse(trans,g));
  else{
    node_ptr t = cp_trans;
    node_ptr q = reverse_quantifiers;
    g = and_bdd(r_shift(g),trans);
    while(t){
      if(verbose)fprintf(stderr,"relational product: size of g = %d\n",size_bdd(g));
      g = and_bdd(forsome(car(q),g),car(t));
      if(reachable_states)g = simplify_assuming(g,reachable_states);
      t = cdr(t);
      q = cdr(q);
    }
    g = forsome(car(q),g);
    return(g);
  }
}


static bdd_ptr ex(g)
bdd_ptr g;
{
  if(fair_states)g = and_bdd(g,fair_states);
  g = cp_reverse(and_bdd(g,invar));
  if(reachable_states)g = and_bdd(g,reachable_states);
  return(g);
}

static bdd_ptr eu(f,g)
bdd_ptr f,g;
{
  bdd_ptr new,oldY;
  bdd_ptr Y = g;
  int n = 1;
  if(fair_states)Y = and_bdd(Y,fair_states);
  if(reachable_states)Y = and_bdd(Y,reachable_states);
  if(verbose)indent_node(stderr,"computing fixed point approximations for ",
			 the_node,"...\n");
  new = Y;
  while(new != ZERO){
    if(verbose){
      double states = count_bdd(Y);
      int size;
      size = size_bdd(Y);
      indent(stderr);
      fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,states,size);
    }
    oldY = Y;
    Y = save_bdd(or_bdd(Y,and_bdd(f,ex(new))));
    new = save_bdd(and_bdd(Y,not_bdd(oldY)));
    save_bdd(f); mygarbage(); release_bdd(f); release_bdd(new); release_bdd(Y);
  }
  return(Y);
}

static bdd_ptr ebu(f, g, inf, sup)     /* bounded until */
bdd_ptr f,g;	/* NOT saved by save_bdd */
int inf, sup;
{
  bdd_ptr oldY;
  bdd_ptr Y = g;
  int n = 1;
  int i;

  if (inf > sup || inf < 0) return ZERO;
  if(fair_states)Y = and_bdd(Y,fair_states);
  if(reachable_states)Y = and_bdd(Y,reachable_states);
  if(verbose)indent_node(stderr,"computing fixed point approximations for ",
			 the_node,"...\n");

  /* compute Y = g | (f & ex(Y)) for states within the bound */
  for (i = sup; i > inf; i--) {
    /* There are more states within the bounds */
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = Y;
    Y = save_bdd(or_bdd(Y, and_bdd(f, ex(Y))));
    if (Y == oldY) {
      /* fixpoint found. collect garbage, and goto next phase */
      i = inf + 1;
    }
    save_bdd(f); mygarbage(); release_bdd(f); release_bdd(Y);
  }

  /* compute Y = f & ex(Y) for states before the bound */
  for (i = inf; i > 0; i--) {
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = Y;
    Y = save_bdd(and_bdd(f,ex(Y)));
    if (Y == oldY) {
      /* fixpoint found. collect garbage, and finish */
      i = 1;
    }
    save_bdd(f); mygarbage(); release_bdd(f); release_bdd(Y);
  }
  return(Y);
}

static bdd_ptr ef(g)
bdd_ptr g;
{
  return(eu(ONE,g));
}

static bdd_ptr ebf(g, inf, sup)
bdd_ptr g;
{
  return(ebu(ONE, g, inf, sup));
}

static bdd_ptr fair_iter(g,fc)
bdd_ptr g;
node_ptr fc;
{
  if(fc == NIL)return(save_bdd(ONE));
  if(fc->type == LIST){
    bdd_ptr l = fair_iter(g,fc->left.nodetype);
    bdd_ptr r = fair_iter(g,fc->right.nodetype);
    bdd_ptr res = save_bdd(and_bdd(l,r));
    release_bdd(l); release_bdd(r);
    mygarbage();
    return(res);
  }
  if(fc->type == BDD){
    bdd_ptr s = ((bdd_ptr)(fc->left.nodetype));
    bdd_ptr r = save_bdd(eu(g,and_bdd(g,s)));
    mygarbage();
    return(r);
  }
  catastrophe("fair_iter: fc->type = %d",fc->type);
}

static bdd_ptr eg(g)
bdd_ptr g;
{
  bdd_ptr oldY = ZERO;
  bdd_ptr Y = g;
  int n = 1;
  if(verbose)indent_node(stderr,"computing fixed point approximations for ",
			 the_node,"...\n");
  while(Y != oldY){
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = save_bdd(Y);
    {
      bdd_ptr Z = fair_iter(Y,fairness_const);
      Y = save_bdd(and_bdd(Y,Z));
      release_bdd(Z); mygarbage(); release_bdd(Y);
    }
    Y = save_bdd(and_bdd(Y,ex(Y)));
    release_bdd(oldY); mygarbage(); release_bdd(Y); 
  }
  return(Y);
}

static bdd_ptr ebg(g, inf, sup)
bdd_ptr g;	/* NOT saved by save_bdd */
{
  bdd_ptr oldY;
  bdd_ptr Y = g;
  int n = 1;
  int i;
  if (inf > sup || inf < 0) return ZERO;
  if(fair_states)Y = and_bdd(Y,fair_states);
  if (reachable_states) Y = and_bdd(Y, reachable_states);
  if(verbose)indent_node(stderr,"computing fixed point approximations for ",
			 the_node,"...\n");
  /* compute Y = g & ex(Y) for states within the bound */
  for (i = sup; i > inf; i--) {
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = Y;
    Y = save_bdd(and_bdd(Y, ex(Y)));
    if (Y == oldY) {
      /* fixpoint found. goto next phase */
      i = inf + 1;
    }
    mygarbage(); release_bdd(Y);
  }
  /* compute Y = ex(Y) for states before the bound */
  for (i = inf; i > 0; i--) {
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = Y;
    Y = save_bdd(ex(Y));
    if (Y == oldY) {
      /* fixpoint found. */
      i = 1;
    }
    mygarbage(); release_bdd(Y); 
  }
  return(Y);
}

static bdd_ptr au(f,g)
bdd_ptr f,g;
{
  bdd_ptr t1 = save_bdd(not_bdd(f));
  bdd_ptr t2 = save_bdd(not_bdd(g));
  bdd_ptr t4 = save_bdd(eg(t2));
  bdd_ptr t3 = not_bdd(or_bdd(eu(t2,and_bdd(t1,t2)),t4));
  release_bdd(t4); release_bdd(t2); release_bdd(t1);
  return(t3);
}

static bdd_ptr abu(f, g, inf, sup)         /* bounded until */
bdd_ptr f,g;	/* NOT saved by save_bdd */
int     inf, sup;
{
  bdd_ptr oldY;
  bdd_ptr Y = g;
  int n = 1;
  int i;
  if (inf > sup || inf < 0) return ZERO;
  if(fair_states)Y = and_bdd(Y,fair_states);
  if(reachable_states)Y = and_bdd(Y,reachable_states);
  if(verbose)indent_node(stderr,"computing fixed point approximations for ",
			 the_node,"...\n");
  /* compute Y = g | (f & ax(Y)) for states within the bound */
  for (i = sup; i > inf; i--) {
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = Y;
    Y = save_bdd(or_bdd(Y, and_bdd(f, not_bdd(ex(not_bdd(Y))))));
    if (Y == oldY) {
      /* fixpoint found. goto next phase */
      i = inf + 1;
    }
    save_bdd(f); mygarbage(); release_bdd(f); release_bdd(Y);
  }
  /* compute Y = f & ax(Y) for states before the bound */
  for (i = inf; i > 0; i--) {
    if(verbose){
      indent(stderr); fprintf(stderr,"size of Y%d = %g states, %d BDD nodes\n",
		       n++,count_bdd(Y),size_bdd(Y));
    }
    oldY = Y;
    Y = save_bdd(and_bdd(f, not_bdd(ex(not_bdd(Y)))));
    if (Y == oldY) {
      /* fixpoint found. finish */
      i = 1;
    }
    save_bdd(f); mygarbage(); release_bdd(f); release_bdd(Y);
  }
  return(Y);
}

static int in_list(n,r)
node_ptr n,r;
{
  while(r){
    if(car(r) == n)return(1);
    r = cdr(r);
  }
  return(0);
}

void type_error(n)
node_ptr n;
{
  start_err();
  indent_node(stderr,"type error: value = ",n,"");
  finish_err();
}  

static node_ptr the_range,the_var;
static range_error(n)
node_ptr n;
{
  start_err();
  indent_node(stderr,"cannot assign value ",n," to variable ");
  print_node(stderr,the_var);
  finish_err();
}

static void range_check(n)
node_ptr n;
{
  if(n == NIL)catastrophe("range_check: n == NIL");
  if(n->type == LIST){
    while(n){
      if(!in_list(car(n),the_range))range_error(car(n));
      n = cdr(n);
    }
  }
  else if(!in_list(n,the_range))range_error(n);
}


static bdd_ptr eval1(n,context)
node_ptr n,context;
{
  if(n == NIL)return(save_bdd(ONE));
  switch(n->type){
  case ATOM:
    {
      node_ptr name = find_node(DOT,context,find_atom(n));
      node_ptr temp1 = find_assoc(param_hash,name);
      node_ptr temp2 = find_assoc(symbol_hash,name);
      bdd_ptr  temp3 = (bdd_ptr)find_assoc(constant_hash,find_atom(n));
      if(temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
	rpterr("atom \"%s\" is ambiguous",n->left.strtype->text);
      if(temp1)return(eval1(temp1,context));
      if(temp3)return(save_bdd(temp3));
    } /* fall through on purpose here */
  case DOT:
  case ARRAY:
    return(enforce_definition(eval_struct(n,context)));
  case CONTEXT: return(eval1(cdr(n),car(n)));
  case LIST:
  case AND: return(binary_op(and_bdd,n,1,1,1,context));
  case OR: return(binary_op(or_bdd,n,1,1,1,context));
  case NOT: return(unary_op(not_bdd,n,1,1,context));
  case IMPLIES: return(binary_op(or_bdd,n,1,-1,1,context));
  case IFF: return(binary_op(xor_bdd,n,-1,1,1,context));
  case CASE: return(eval_if_then_else(car(car(n)),cdr(car(n)),cdr(n),context));
  case EQUAL: return(binary_op(equal_bdd,n,1,1,1,context));
  case PLUS: return(binary_op(plus_bdd,n,1,1,1,context));
  case MINUS: return(binary_op(minus_bdd,n,1,1,1,context));
  case TIMES: return(binary_op(times_bdd,n,1,1,1,context));
  case DIVIDE: return(binary_op(divide_bdd,n,1,1,1,context));
  case MOD: return(binary_op(mod_bdd,n,1,1,1,context));
  case LT: return(binary_op(lt_bdd,n,1,1,1,context));
  case GT: return(binary_op(gt_bdd,n,1,1,1,context));
  case LE: return(binary_op(gt_bdd,n,-1,1,1,context));
  case GE: return(binary_op(lt_bdd,n,-1,1,1,context));
  case NUMBER: return(save_bdd(leaf_bdd(find_atom(n))));
  case NEXT: return(unary_op(r_shift,n,1,1,context));
  case TRUEEXP: return(save_bdd(ONE));
  case FALSEEXP: return(save_bdd(ZERO));
  case EX: return(unary_op(ex,n,1,1,context));
  case AX: return(unary_op(ex,n,-1,-1,context));
  case EF: return(unary_op(ef,n,1,1,context));
  case AF: return(unary_op(eg,n,-1,-1,context));
  case EG: return(unary_op(eg,n,1,1,context));
  case AG: return(unary_op(ef,n,-1,-1,context));
  case EU: return(binary_op(eu,n,1,1,1,context));
  case AU: return(binary_op(au,n,1,1,1,context));
  case EBU: return(quad_op(ebu,n,1,1,1,context));
  case ABU: return(quad_op(abu,n,1,1,1,context));
  case EBF: return(ternary_op(ebf,n,1,1,context));
  case ABF: return(ternary_op(ebg,n,-1,-1,context));
  case EBG: return(ternary_op(ebg,n,1,1,context));
  case ABG: return(ternary_op(ebf,n,-1,-1,context));
  case EQDEF:
    {
      node_ptr t1,t2,r;
      switch(assign_type){
      case INIT:
	if(car(n)->type != SMALLINIT)return(save_bdd(ONE));
	t1 = t2 = car(car(n));
	break;
      case TRANS:
	if(car(n)->type != NEXT)return(save_bdd(ONE));
	t1 = car(n);
	t2 = car(car(n));
	break;
      default:
	if(car(n)->type == NEXT || car(n)->type == SMALLINIT)
	  return(save_bdd(ONE));
	t1 = t2 = car(n);
      }
      r = find_assoc(symbol_hash,eval_struct(t2,context));
      if(r == NIL)undefined(t2);
      if(r->type != VAR)redefining(t2);
      if(verbose > 2){
	indent_size++;
	indent_node(stderr,"evaluating ",t1,":\n");
      }
      {
	bdd_ptr v = eval(cdr(n),context);
	the_var = t2;
	the_range = cdr(r);
	walk_leaves(range_check,v);
	{
	  bdd_ptr v1 = eval(t1,context);
	  release_bdd(v1); release_bdd(v);
	  v = save_bdd(setin_bdd(v1,v));
	}
	if(verbose > 2){
	  indent_node(stderr,"size of ",t1," = ");
	  fprintf(stderr,"%d BDD nodes\n",size_bdd(v));
	  indent_size--;
	}
	return(v);
      }
    }
  case TWODOTS:
    {
      node_ptr t = NIL;
      int dim1,dim2,i;
      dim1 = eval_num(car(n),context);
      dim2 = eval_num(cdr(n),context);
      for(i=dim2;i>=dim1;i--)
	t = find_node(UNION,find_node(NUMBER,i,NIL),t);
      if(t == NIL)
	rpterr("empty range: %d..%d", dim1, dim2);
      n = t;
    } /* fall through on purpose here */
  case UNION: return(binary_op(union_bdd,n,1,1,1,context));
  case SETIN: return(binary_op(setin_bdd,n,1,1,1,context));
  default:
    catastrophe("eval1: type = %d\n",n->type);
  }
}

static bdd_ptr eval(n,context)
node_ptr n,context;
{
  bdd_ptr res;
  int temp = yylineno;
  if(n == NIL)return(save_bdd(ONE));
  yylineno = n->lineno;
  res = eval1(n,context);
  yylineno = temp;
  mygarbage();
  return(res);
}

static node_ptr eval_tree(n,context)
node_ptr n,context;
{
  if(n == NIL)return(NIL);
  if(n->type == LIST)
    return(find_node(LIST,eval_tree(n->left.nodetype,context),
		     eval_tree(n->right.nodetype,context)));
  return(find_node(BDD,eval(n,context),NIL));
}


static void instantiate();
static void instantiate_by_name(c,n,trans,init,spec,fair,assign,procs,actual)
node_ptr c,n;
node_ptr *trans,*init,*spec,*fair,*assign,*procs;
node_ptr actual;
{
  node_ptr s = module_stack;
  node_ptr c1 = find_atom(c);
  node_ptr m = find_assoc(module_hash,c1);
  yylineno = c->lineno;
  if(!m)undefined(c);
  while(s){
    if(car(s) == c1)rpterr("module \"%s\" is recursively defined",
		      c->left.strtype->text);
    s = cdr(s);
  }
  module_stack = cons(c1,module_stack);
  instantiate(m,n,trans,init,spec,fair,assign,procs,actual);
  s = cdr(module_stack); free_node(module_stack); module_stack = s;
}

static void process_by_name(c,n,trans,init,spec,fair,assign,procs,actual)
node_ptr c,n;
node_ptr *trans,*init,*spec,*fair,*assign,*procs;
node_ptr actual;
{
  node_ptr my_assign = NIL;
  instantiate_by_name(c,n,trans,init,spec,fair,&my_assign,procs,actual);
  *procs = cons(cons(n,my_assign),*procs);
}

static int get_bdd_var()
{
  if(nstvars == MAXSTVARS)toomanyvars();
  if(verbose > 1)fprintf(stderr,"  BDD variable %d\n",nstvars+1);
  if(!is_input_decl){
    release_bdd(vars);
    vars = save_bdd(and_bdd(atomic_bdd(nstvars+1),vars));
  }
  else{
    release_bdd(input_vars);
    input_vars = save_bdd(and_bdd(atomic_bdd(nstvars+1),input_vars));
  }    
  return(++nstvars);
}
  

static node_ptr odd_elements(),even_elements();

static node_ptr odd_elements(l)
node_ptr l;
{
  if(l == NIL)return(NIL);
  return(cons(car(l),even_elements(cdr(l))));
}

static node_ptr even_elements(l)
node_ptr l;
{
  if(l == NIL)return(NIL);
  return(odd_elements(cdr(l)));
}

static bdd_ptr scalar_var(l,n)
node_ptr l;
int n;
{
  if(l == NIL)catastrophe("scalar_var: l = NIL");
  if(cdr(l) == NIL){
    node_ptr v = find_atom(car(l));
    bdd_ptr temp = (bdd_ptr) find_assoc(constant_hash,v);
    if(temp)return(temp);
    temp = save_bdd(leaf_bdd(v));
    if(v && v->type == ATOM)insert_assoc(constant_hash,v,temp);
    return(temp);
  }
  if((++n) > nstvars)get_bdd_var();
  {
    bdd_ptr p0 = scalar_var(odd_elements(l),n);
    bdd_ptr p1 = scalar_var(even_elements(l),n);
    return(find_bdd(THE_CURRENT_VAR(n),p0,p1));
  }
}

static node_ptr param_context;
static node_ptr put_in_context(v)
node_ptr v;
{
  return(find_node(CONTEXT,param_context,v));
}

static void inst_one_var(name,type,trans,init,spec,fair,assign,procs,context)
node_ptr name,type;
node_ptr *trans,*init,*spec,*fair,*assign,*procs;
node_ptr context;
{
  yylineno = type->lineno;
  switch(type->type){
  case BOOLEAN:
    insert_assoc(symbol_hash,name,
		 new_node(VAR,NIL,
			   boolean_type));
    variables = cons(name,variables);
    all_symbols = cons(name,all_symbols);
    break;
  case TWODOTS:
    {
      node_ptr t = NIL;
      int dim1,dim2,i;
      dim1 = eval_num(car(type),context);
      dim2 = eval_num(cdr(type),context);
      for(i=dim2;i>=dim1;i--)
	t = cons(find_node(NUMBER,i,NIL),t);
      if(t == NIL){
	start_err();
	fprintf(stderr, "empty range type %d..%d for ", dim1, dim2);
	print_node(stderr,name);
	finish_err();
      }
      insert_assoc(symbol_hash,name,
		   new_node(VAR,NIL,
			     t));
      variables = cons(name,variables);
      all_symbols = cons(name,all_symbols);
      break;
   }   
  case SCALAR:
    insert_assoc(symbol_hash,name,
		 new_node(VAR,NIL,
			   car(type)));
    variables = cons(name,variables);
    all_symbols = cons(name,all_symbols);
    break;
  case MODTYPE:
    {
      node_ptr actual;
      param_context = context;
      actual = map(put_in_context,cdr(type));
      instantiate_by_name(car(type),name,
			  trans,init,spec,fair,assign,procs,actual);
      break;
    }
  case PROCESS:
    {
      node_ptr actual;
      param_context = context;
      actual = map(put_in_context,cdr(car(type)));
      process_by_name(car(car(type)),name,
			  trans,init,spec,fair,assign,procs,actual);
      break;
    }
  case ARRAY:
    {
      int dim1,dim2,i;
      dim1 = eval_num(car(car(type)),context);
      dim2 = eval_num(cdr(car(type)),context);
      for(i=dim1;i<=dim2;i++)
	inst_one_var(find_node(ARRAY,name,find_node(NUMBER,i,NIL)),
		     cdr(type),trans,init,spec,fair,assign,procs,context);
      break;
    }
  default:
    catastrophe("instantiate_vars: type = %d",type->type);
  }
}

static void instantiate_vars(l,n,trans,init,spec,fair,assign,procs)
node_ptr l,n;
node_ptr *trans,*init,*spec,*fair,*assign,*procs;
{
  if(l == NIL)return;
  instantiate_vars(cdr(l),n,trans,init,spec,fair,assign,procs);
  {
    node_ptr v = car(l);
    node_ptr name = eval_struct(car(v),n);
    node_ptr type = cdr(v);
    node_ptr val;
    if(find_assoc(symbol_hash,name))redefining(name);
    inst_one_var(name,type,trans,init,spec,fair,assign,procs,n);
  }
}

void make_params(basename,actual,formal)
node_ptr basename,actual,formal;
{
  while(formal){
    node_ptr old,new; 
    if(!actual)rpterr("too few actual paramaters");
    new = find_node(DOT,basename,find_atom(car(formal)));
    old = car(actual);
    formal = cdr(formal);
    actual = cdr(actual);
    if(find_assoc(param_hash,new)){
      start_err();
      fprintf(stderr,"Multiple substitution for ");
      print_node(stderr,new);
      finish_err();
    }
    insert_assoc(param_hash,new,old);
  }
  if(actual)rpterr("too many actual paramaters");
}

static void swap_nodes(n1,n2)
node_ptr *n1,*n2;
{
  node_ptr temp = *n1;
  *n1 = *n2;
  *n2 = temp;
}

static void instantiate(l,n,trans,init,spec,fair,assign,procs,actual)
node_ptr l,n;
node_ptr *trans,*init,*spec,*fair,*assign,*procs;
node_ptr actual;
{
  node_ptr d;
  node_ptr formal = car(l);
  node_ptr m = cdr(l);
  node_ptr mytrans = NIL;
  node_ptr myinit = NIL;
  node_ptr myspec = NIL;
  node_ptr myfair = NIL;
  node_ptr myassign = NIL;
  node_ptr myprocs = NIL;
  make_params(n,actual,formal);

  /* first, instantiate all the definitions */
  /* we do the definitions first, in case they are constants */
  /* used in the array declarations */

  d= m;
  while(d){
    node_ptr s = car(d);
    d = cdr(d);
    switch(s->type){
    case DEFINE:
      {
	node_ptr e = car(s);
	while(e){
	  node_ptr name = eval_struct(car(car(e)),n);
	  node_ptr def = cdr(car(e));
	  yylineno = e->lineno;
	  if(find_assoc(symbol_hash,name))redefining(name);
	  insert_assoc(symbol_hash,name,find_node(CONTEXT,n,def));
	  all_symbols = cons(name,all_symbols);
	  e = cdr(e);
	}
      }
      break;
    default:
      break;
    }
  }

  /* now, instantiate all the variables, and the
     TRANS, INIT, SPECIFICATION, FAIRNESS and ASSIGN declarations */
  d = m;
  while(d){
    node_ptr e = car(d);
    d = cdr(d);
    switch(e->type){
    case ISA:
      instantiate_by_name(car(e),n,&mytrans,&myinit,&myspec,&myfair,&myassign,
			  &myprocs,NIL);
      break;
    case INPUT:
      if(e->type == INPUT && instantiate_mode != 1)break;
      is_input_decl = 1;
      instantiate_vars(car(e),n,&mytrans,&myinit,&myspec,&myfair,&myassign,&myprocs);
      is_input_decl = 0;
      break;
    case VAR:
      instantiate_vars(car(e),n,&mytrans,&myinit,&myspec,&myfair,&myassign,&myprocs);
      break;
    case TRANS:
      mytrans = find_node(AND,mytrans,find_node(CONTEXT,n,car(e)));
      break;
    case INIT:
      myinit = find_node(AND,myinit,find_node(CONTEXT,n,car(e)));
      break;
    case SPEC:
      if(instantiate_mode == 1)break;
      if(instantiate_mode == 2)
	rpterr("sorry -- can't check a SPEC in an implementation (yet)");
      myspec = cons(find_node(CONTEXT,n,car(e)),myspec);
      break;
    case FAIRNESS:
      myfair = cons(find_node(CONTEXT,n,car(e)),myfair);
      break;
    case ASSIGN:
      myassign = find_node(AND,find_node(CONTEXT,n,car(e)),myassign);
      break;
    case OUTPUT:
      if(instantiate_mode != 1)break;
      {
	node_ptr l = car(e);
	while(l){
	  myspec = find_node(AND,myspec,
			     find_node(EQUAL,
				       find_node(CONTEXT,n,car(l)),
				       find_node(CONTEXT,the_impl,car(l))));
	  l = cdr(l);
	}
      }
      break;
    default:
      break;
    }
  }
  *trans = find_node(AND,*trans,mytrans);
  *init  = find_node(AND,*init,myinit);
  *spec  = append(myspec,*spec);
  *fair  = append(myfair,*fair);
  *assign = find_node(AND,*assign,myassign);
  *procs = append(*procs,myprocs);
}

void print_state(s,changes_only)
bdd_ptr s;
int changes_only;
{
  node_ptr l = all_symbols;
  node_ptr p = (node_ptr)(value_bdd(if_then_bdd(s,proc_selector)));
  if(p != NIL)indent_node(stdout,"[executing process ",p,"]\n");
  while(l){
    node_ptr n = car(l);
    bdd_ptr v = eval(n,NIL);
    node_ptr w;
    l = cdr(l);
    w = (node_ptr)(value_bdd(if_then_bdd(s,v)));
    if(changes_only){
      if(w == find_assoc(print_hash,n))continue;
      insert_assoc(print_hash,n,w);
    }
    indent_node(stdout,"",n," = ");
    print_node(stdout,w);
    printf("\n");
  }
}
						       
bdd_ptr cp_forward(g)
bdd_ptr g;
{
  if(!option_conj_part)return(r_collapse(trans,g));
  else{
    node_ptr t = cp_trans;
    node_ptr q = forward_quantifiers;
    g = and_bdd(g,trans);
    while(t){
      if(verbose)fprintf(stderr,"relational product: size of g = %d\n",size_bdd(g));
      g = and_bdd(forsome(car(q),g),car(t));
      t = cdr(t);
      q = cdr(q);
    }
    g = forsome(car(q),g);
    return(f_shift(g));
  }
}

node_ptr ex_explain(p,f)
node_ptr p;
bdd_ptr f;
{
  bdd_ptr s;
  if(p == NIL)return(p);
  if(fair_states)f = and_bdd(f,fair_states);
  s = sat_bdd(and_bdd(f,and_bdd(invar,cp_forward(car(p)))));
  if(s == ZERO)return(NIL);
  p = cons(save_bdd(s),p);
  mygarbage();
  return(p);
}

/*
 * eu_explain: finds a path that is an example for E[f U g]
 *
 * p is a bdd that represents the first state of the path. It is an initial
 * state from which the example can be found.
 *
 * The procedure is to try to execute eu(f,g) again, looking for a path from
 * p to a state where g is valid.
 *
 * We look for states that can be reached from p. At each step we generate a
 * set of states Y(i) that can be reached in one step from Y(i-1). We store
 * each Y(i) in a list.
 *
 * After having a list of Y's, we use sat_bdd on each of the Y(i) such that
 * the list of set of states becomes a list of states, each state i is one
 * state in Y(i). This forms the example.
 */
node_ptr eu_explain(p,f,g)
node_ptr p;
bdd_ptr f,g;
{
  if(p == NIL)return(p);
  {
    bdd_ptr         Y = (bdd_ptr) car(p);	/* Set of states reached
						 * so far - initially
						 * just one state */
    bdd_ptr         Z = Y;	/* Set of states reached so far along
				 * a path satifying f.  If we ever use
				 * Z, it means that car(p) does not
				 * satify g, therfore it satifies f */
    bdd_ptr         new = Y;	/* States added to Y just now */
    int             n = 0;	/* Iteration counter */
    node_ptr        l = p;	/* initialize list with first state
				 * (list is reversed) */
    if(verbose)indent_node(stderr,"searching (counter)example for ",the_node,
			   "\n");
    if(fair_states)g = save_bdd(and_bdd(g,fair_states));
    while(new != ZERO){
      if(verbose)
	fprintf(stderr,"iteration %d: states = %g, BDD nodes = %d\n",
		n++,count_bdd(Y),size_bdd(Y));
      new = save_bdd(and_bdd(new,invar)); mygarbage(); release_bdd(new);
      {
	bdd_ptr x = sat_bdd(and_bdd(new,g)); /* x is one state in Y & g */
	if(x != ZERO){                       /* did we reach g ?        */
          /* Yes. Instantiate the Y's, and return a list of states */
          node_ptr m = l;
	  if(fair_states)release_bdd(g);
	  while(1){
            if(reachable_states && and_bdd(x,reachable_states) == ZERO){
              fprintf(stdout,"this state is not reachable :\n");
              print_state(x,0);
              catastrophe("eu_explain: state not reachable");
	    }
	    release_bdd(car(m));
	    m->left.bddtype = save_bdd(x); /* substitute Y for one state
                                                   of Y in the list */
	    mygarbage();
	    if(m == p)return(l); /* if we reached the first state, it's over */
	    m = cdr(m);
            /*
             * instantiate the next Y. x is a state in car(m), such that there
             * is a path from the current x to it.
             */
	    x = and_bdd(car(m),and_bdd(invar,cp_reverse(x)));
	    /* if l != p, car(p) may include states not satifying f */
	    if(m==p)x=and_bdd(x,f);
	    x = sat_bdd(x);
	  }
	}
      }
      /* generate the next Y, that is, the set of states that can be reached
       * in one step from the states in Y that satify f.
       */
      Y = save_bdd(or_bdd(Z,cp_forward(and_bdd(f,new))));
      mygarbage();	/* new is no longer needed. */
      new = save_bdd(and_bdd(Y,not_bdd(Z)));
      mygarbage();
      /*
       * In case the new Y cannot satisfy g, save its subset of states
       * that satisfies f on the state list.
       */
      Z = save_bdd(and_bdd(f,Y));
      l = cons(Z,l);
      mygarbage(); release_bdd(Y); release_bdd(new);
    }
    /* reached the fixpoint and could not find it. Release the list. */
    while(l != p){
      node_ptr m=l;
      release_bdd(car(l));
      l = cdr(l);
      free_node(m);
    }
    if(fair_states)release_bdd(g);
    mygarbage();
    return(NIL);
  }
}

node_ptr ebu_explain(p, f, g, inf, sup)
node_ptr p;
bdd_ptr f,g;
int inf, sup;
{
  if(p == NIL)return(p);
  {
    bdd_ptr Y = (bdd_ptr)car(p);
    int n = 0;
    bdd_ptr Z;
    node_ptr l = p;
    int i;
    if (verbose)indent_node(stderr,"searching (counter)example for ",
		            the_node,"\n");
    /*
     * look for a path from p, with length inf, using only transitions
     * from states satisfying f.  The lsets os states in the list may
     * contain states in which f is false.  This is hadled later, when
     * a complete (counter)example is found, to avoid the need of
     * recovering the "old" car(p)
     */
    for (i = 0; i < inf; i++) {
      if(verbose)
	fprintf(stderr,"iteration %d: states = %g, BDD nodes = %d\n",
		n++,count_bdd(Y),size_bdd(Y));
      Z = save_bdd(Y);
      Y = save_bdd(and_bdd(invar,Y)); mygarbage(); release_bdd(Y);
      Y = cp_forward(and_bdd(Y,f));
      if (Y == ZERO) {
        /* there is no valid path */
        release_bdd(Z);
	while(l != p){
	  node_ptr m=l;
	  release_bdd(car(l));
	  l = cdr(l);
	  free_node(m);
	}
	mygarbage();
	return(NIL);
      }        
      l = cons(save_bdd(Y),l);
      mygarbage();
      release_bdd(Z);
      if (Z == Y) {
        /* fixpoint found - fill the list with Y to length inf. */
	while (++i < inf) {
	  l = cons(save_bdd(Y),l);
	}
	/* No need for further garbage collections. */
	break;
      }
      mygarbage();
    }
    /*
     * At this point, car(l) is the set of states that can be reached
     * in inf steps, using transitions from states where f is valid.
     * Now we can call eu_explain(l, f, g).  eu_explain will find a
     * shortest extension from car(l) to a state where g is valid.  We
     * then check that the length of this path is less than or equal
     * to (sup-inf).
     */
    {
      node_ptr ll = eu_explain(l, f, g);
      if (ll != NIL) {
	node_ptr m = ll;
	for (i = 0; m != NIL && m != l; i++, m = cdr(m)) {
	}
	if (m == NIL) {
	  catastrophe("ebu_explain: cannot get back to l");
	}
	/* did we reach g in time? */
	if (i <= (sup-inf)) {
          /* Yes. Instantiate the Y's, and return a list of states */
	  bdd_ptr x = l->left.bddtype;
          m = l;
	  while(1){
            if(reachable_states && and_bdd(x,reachable_states) == ZERO){
              fprintf(stdout,"this state is not reachable :\n");
              print_state(x,0);
              catastrophe("ebu_explain: state not reachable");
	    }
	    release_bdd(car(m));
	    m->left.bddtype = save_bdd(x); /* substitute Y for one state
                                                   of Y in the list */
	    mygarbage();
	    if(m == p)return(ll); /* if we reached the first state, it's over */
	    m = cdr(m);
            /*
             * instantiate the next Y. x is a state in car(m), such that there
             * is a path from the current x to it.
             */
	    x = and_bdd(car(m),and_bdd(invar,cp_reverse(x)));
	    /* if l != p, car(m) may include states not satifying f */
	    x = sat_bdd(and_bdd(x,f));
	  }
	}
	/* path from l to ll is longer than requested. */
	l = ll;
      }
      /* Could not find an example - free all newly allocated nodes */
      while (l != p) {
	node_ptr m = l;
	release_bdd(car(l));
	l = cdr(l);
	free_node(m);
      }
      mygarbage();
      return (NIL);
    }
  }
}

static node_ptr fairness_explain(p,f,fc)
node_ptr p;
bdd_ptr f;
node_ptr fc;
{
  if(fc == NIL)return(p);
  if(fc->type == LIST){
    p = fairness_explain(p,f,fc->left.nodetype);
    p = fairness_explain(p,f,fc->right.nodetype);
    return(p);
  }
  if(fc->type == BDD){
    bdd_ptr Y = save_bdd(and_bdd(f,car(fc)));
    node_ptr res = eu_explain(p,f,Y);
    release_bdd(Y); mygarbage();
    return(res);
  }
  catastrophe("fairness_explain: fc->type == %d",fc->type);
}

node_ptr eg_explain(p,g)
node_ptr p;
bdd_ptr g;
{
  node_ptr p1;
  bdd_ptr f;
  if(p == NIL)return(p);
  f = save_bdd(eg(g));
  if(and_bdd(car(p),f)==ZERO)return(NIL);
  while(1){
    bdd_ptr start = p->left.bddtype;
    p = fairness_explain(p,f,fairness_const);
    g = save_bdd(and_bdd(f,ex(start)));
    p1 = p; p = ex_explain(eu_explain(p,f,g),start);
    release_bdd(g); mygarbage();
    if(p)break;
    p = ex_explain(p1,f);
    if(p == NIL)catastrophe("eg_explain: p == NIL");
  }
  release_bdd(f); mygarbage();
  return(p);
}

node_ptr ebg_explain(p, g, inf, sup)
node_ptr p;
bdd_ptr g;
int inf, sup;
{
  if(p == NIL)return(p);
  {
    bdd_ptr Y = (bdd_ptr)car(p);
    int n = 0;
    bdd_ptr Z;
    node_ptr l = p;
    int i;

    if(verbose)indent_node(stderr,"searching (counter)example for ",the_node,
			   "\n");

    /* look for a path of length inf from p */
    for (i=0; i < inf; i++) {
      if(verbose)
	fprintf(stderr,"iteration %d: states = %g, BDD nodes = %d\n",
		n++,count_bdd(Y),size_bdd(Y));
      Z = save_bdd(Y);
      Y = and_bdd(invar,cp_forward(Y));
      if (Y == ZERO) {
        /* there is no valid path */
        release_bdd(Z);
	while(l != p){
	  node_ptr m=l;
	  release_bdd(car(l));
	  l = cdr(l);
	  free_node(m);
	}
	mygarbage();
	return(NIL);
      }        
      l = cons(save_bdd(Y),l);
      mygarbage();
      release_bdd(Z);
      if (Z == Y) {
        /* fixpoint found - fill the list with Y to length inf. */
	while (++i < inf) {
	  l = cons(save_bdd(Y),l);
	}
	/* No need for further garbage collections. */
	break;
      }
      mygarbage();
    }

    /*
     * At this point, car(l) is the set of states that can be reached
     * in inf steps.  Look for a continuation path of lenth sup-inf
     * using transitions from states that satify g
     */
    if(fair_states)g = save_bdd(and_bdd(g,fair_states));
    {
      node_ptr ll = l;
      Y = (bdd_ptr) car(l);
      for (i = inf; i < sup; i++) {
	if(verbose)
	  fprintf(stderr,"iteration %d: states = %g, BDD nodes = %d\n",
		  n++,count_bdd(Y),size_bdd(Y));
	Z = save_bdd(Y);
	Y = and_bdd(invar,cp_forward(and_bdd(g,Y)));
	if (Y == ZERO) {
	  /* there is no valid path */
	  release_bdd(Z);
	  while(l != p){
	    node_ptr m=l;
	    release_bdd(car(l));
	    l = cdr(l);
	    free_node(m);
	  }
	  if(fair_states)release_bdd(g);
	  mygarbage();
	  return(NIL);
	}        
	l = cons(save_bdd(Y),l);
	mygarbage();
	release_bdd(Z);
	if (Y == Z) {
	  /* fixpoint found - fill the list with Y to length sup. */
	  while (++i < sup) {
	    l = cons(save_bdd(Y),l);
	  }
	  /* No need for further garbage collections. */
	  break;
	}
	mygarbage();
      }

      /*
       * transform l from a list of sets of states into a list of states.
       */
      {
	node_ptr m = l;
	bdd_ptr x = sat_bdd(and_bdd(g,car(m)));

	/* g should hols in all states up to car(ll), inclusive */
	while (1) {
	  release_bdd(car(m));
	  m->left.bddtype = save_bdd(x);
	  mygarbage();
	  if (m == ll) break;
	  m = cdr(m);
	  /* instantiate the next Y */
	  x = sat_bdd(and_bdd(car(m), and_bdd(and_bdd(g,invar), cp_reverse(x))));
	}
	if(fair_states)release_bdd(g);

	/* Continue instantiating up to car(p), inclusive */
	while (1) {
	  release_bdd(car(m));
	  m->left.bddtype = save_bdd(x);
	  mygarbage();
	  if (m == p) break;
	  m = cdr(m);
	  /* instantiate the next Y */
	  x = sat_bdd(and_bdd(car(m), and_bdd(invar, cp_reverse(x))));
	}
        return(l);
      }
    }
  }
}

void print_spec(file,n)
FILE *file;
node_ptr n;
{
  node_ptr context = NIL;
  if(n->type == CONTEXT){context = car(n); n = cdr(n);}
  indent_node(file,"specification ",n," ");
  if(context){
    fprintf(file,"(in module ");
    print_node(file,context);
    fprintf(file,") ");
  }
}

int trace_number = 1;
void print_explanation(p)
node_ptr p;
{
  int state_number = 1;
  node_ptr last();
  node_ptr last_state = last(p);
  printf("-- as demonstrated by the following execution sequence\n");
  clear_hash(print_hash);
  while(p){
    if(cdr(p) && car(p) == last_state)
      printf("-- loop starts here --\n");
    printf("state %d.%d:\n",trace_number,state_number);
    print_state(car(p),1);
    printf("\n");
    insert_assoc(state_hash,find_node(DOT,find_node(NUMBER,trace_number,NIL),
				      find_node(NUMBER,state_number,NIL)),car(p));
    state_number++;
    mygarbage();
    p = cdr(p);
  }
  trace_number++;
}

node_ptr explain();
node_ptr explain1(s,n,context)
node_ptr s;
node_ptr n,context;
{
  bdd_ptr a1,a2;
  node_ptr p;
  if(n == NIL)return(NIL);
  yylineno = n->lineno;
  mygarbage();
  switch(n->type){
  case CONTEXT: 
    return(explain(s,cdr(n),car(n)));
  case AND:
  case OR:
  case NOT:
  case IMPLIES:
  case IFF:
    {
      node_ptr p =  explain(s,car(n),context);
      if(p)return(p);
      return(explain(s,cdr(n),context));
    }
  case EX:
    a1 = eval(car(n),context);
    the_node = n;
    p = ex_explain(s,a1);
    release_bdd(a1);
    if(p){
      node_ptr q = explain(p,car(n),context);
      if(q)return(q);
    }
    return(p);
  case AX:
    return(explain(s,find_node(NOT,find_node(EX,find_node(NOT,car(n),NIL),NIL),NIL),context));
  case EF:
    return(explain(s,find_node(EU,one_number,car(n)),context));
  case AG:
    return(explain(s,find_node(NOT,find_node(EU,one_number,
					     find_node(NOT,car(n),NIL)),NIL),context));
  case EG:
    a1 = eval(car(n),context);
    the_node = n;
    p = eg_explain(s,a1);
    release_bdd(a1);
    return(p);
  case AF:
    /* AF g and !EG !g are equivalent. */
    return (explain(s, find_node
		    (NOT, find_node
		     (EG, find_node
		      (NOT, car(n), NIL), NIL), NIL),
		    context));
  case EU:
    a1 = eval(car(n),context);
    a2 = eval(cdr(n),context);
    the_node = n;
    p = eu_explain(s,a1,a2);
    release_bdd(a2); release_bdd(a1);
    if(p){
      node_ptr q = explain(p,cdr(n),context);
      if(q)return(q);
    }
    return(p);
  case AU:
    /* A[f U g] and !(E[!g U (!g & !f)] | EG !g) are equivalent. */
    return (explain(s, find_node
		    (NOT, find_node
		     (OR, find_node
		      (EU, find_node
		       (NOT, cdr(n), NIL), find_node
		       (AND, find_node
			(NOT, car(n), NIL), find_node
			(NOT, cdr(n), NIL))), find_node
		      (EG, find_node
		       (NOT, cdr(n), NIL), NIL)), NIL),
		    context));
  case EBU:
    a1 = eval(car(car(n)), context);
    a2 = eval(cdr(car(n)), context);
    {
      int inf = eval_num(car(cdr(n)), context);
      int sup = eval_num(cdr(cdr(n)), context);
      the_node = n;
      p = ebu_explain(s, a1, a2, inf, sup);
    }
    release_bdd(a2); release_bdd(a1);
    if(p){
      node_ptr q = explain(p,cdr(car(n)), context);
      if(q)return(q);
    }
    return(p);
  case ABU:
    /*
     * A[f BU l..h g] is equivalent to
     * ! ((EBF 0..(l - 1) !f)
     *    | EBG l..l ((EBG 0..(h - l) !g)
     *  	      | E[!g BU 0..(h - l) (!g & !f)]))
     *
     * f:car(car(n)) g:cdr(car(n)) l:car(cdr(l)) h:cdr(car(n))
     */

    return (explain(s, find_node
		    (NOT, find_node
		     (OR, find_node
		      (EBF, find_node
		       (NOT, car(car(n)), NIL), find_node
		       (TWODOTS,
			zero_number, find_node
			(MINUS, car(cdr(n)), one_number))), find_node
		      (EBG, find_node
		       (OR, find_node
			(EBG, find_node
			 (NOT, cdr(car(n)), NIL), find_node
			 (TWODOTS,
			  zero_number, find_node
			  (MINUS,
			   cdr(cdr(n)),
			   car(cdr(n))))), find_node
			(EBU, find_node
			 (EU, find_node
			  (NOT, cdr(car(n)), NIL), find_node
			  (AND, find_node
			   (NOT, car(car(n)), NIL), find_node
			   (NOT, cdr(car(n)), NIL))), find_node
			 (TWODOTS,
			  zero_number, find_node
			  (MINUS,
			   cdr(cdr(n)),
			   car(cdr(n)))))), find_node
		       (TWODOTS,
			car(cdr(n)),
			car(cdr(n))))), NIL),
		    context));
						   
  case EBF:
    /* EBF range g and E[1 BU range g] are equivalent.  */
    return (explain(s, find_node
		    (EBU, find_node
		     (EU, one_number, car(n)),
		     cdr(n)),
		    context));
  case ABG:
    /* ABG range g and !EBF range !g are equivalent. */
    return (explain(s, find_node
		    (NOT, find_node
		     (EBF, find_node
		       (NOT, car(n), NIL),
		      cdr(n)), NIL),
		    context));
  case EBG:
    a1 = eval(car(n),context);
    {
      int inf = eval_num(car(cdr(n)), context);
      int sup = eval_num(cdr(cdr(n)), context);
      the_node = n;
      p = ebg_explain(s, a1, inf, sup);
    }
    release_bdd(a1);
    return(p);
  case ABF:
    /* ABF range g and !EBG range !g are equivalent. */
    return (explain(s, find_node
		    (NOT, find_node
		     (EBG, find_node
		       (NOT, car(n), NIL),
		      cdr(n)), NIL),
		    context));
  case ATOM:
    {
      node_ptr name = find_node(DOT,context,find_atom(n));
      node_ptr temp1 = find_assoc(param_hash,name);
      node_ptr temp2 = find_assoc(symbol_hash,name);
      bdd_ptr  temp3 = (bdd_ptr)find_assoc(constant_hash,find_atom(n));
      if(temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
	rpterr("atom \"%s\" is ambiguous",n->left.strtype->text);
      if(temp1)return(explain(s,temp1,context));
      if(temp3)return(NIL);
    } /* fall through on purpose here */
  case DOT:
  case ARRAY:
    {
      node_ptr t = eval_struct(n,context);
      node_ptr v = find_assoc(symbol_hash,t);
      if(v)return(explain(s,v,context));
      return(NIL);
    }
  default:
    return(NIL);
  }
}

node_ptr explain(s,n,context)
node_ptr s,n,context;
{
  node_ptr res = explain1(s,n,context);
  mygarbage();
  return(res);
}

static void check_circular_assign();

static void check_circ(n,context)
node_ptr n,context;
{
  if(n == NIL)return;
  yylineno = n->lineno;
  switch(n->type){
  case NUMBER:
  case BDD:
  case VAR:
    return;
  case ATOM:
    {
      node_ptr name = find_node(DOT,context,find_atom(n));
      node_ptr temp1 = find_assoc(param_hash,name);
      node_ptr temp2 = find_assoc(symbol_hash,name);
      bdd_ptr  temp3 = (bdd_ptr)find_assoc(constant_hash,find_atom(n));
      if(temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
	rpterr("atom \"%s\" is ambiguous",n->left.strtype->text);
      if(temp1){check_circ(temp1,context); return;}
      if(temp3)return;
    } /* fall through on purpose here */
  case DOT:
  case ARRAY:
    {
      node_ptr t = eval_struct(n,context);
      check_circular_assign(t,context);
      return;
    }
  case CONTEXT:
    check_circ(cdr(n),car(n));
    return;
  default:
    check_circ(car(n),context);
    check_circ(cdr(n),context);
    return;
  }
}

#define CLOSED_NODE (node_ptr)(-2)
static void check_circular_assign(n,context)
node_ptr n,context;
{
  node_ptr t = find_assoc(assign_hash,n);
  if(t == CLOSED_NODE)return;
  if(t == FAILURE_NODE)circular(n);
  if(t == NIL)t = find_assoc(symbol_hash,n);
  if(t == NIL){
    if(find_assoc(constant_hash,n))return;
    undefined(n);
  }
  insert_assoc(assign_hash,n,FAILURE_NODE);
  push_atom(n);
  check_circ(t,context);
  pop_atom();
  insert_assoc(assign_hash,n,CLOSED_NODE);
  switch(n->type){
  case NEXT: heuristic_order = cons(car(n),heuristic_order); break;
  case SMALLINIT: break;
  default: heuristic_order = cons(n,heuristic_order);
  }
}

static void multiple_assignment(t1)
node_ptr t1;
{
  start_err();
  fprintf(stderr,"multiply assigned: ");
  print_node(stderr,t1);
  finish_err();
}


static bdd_ptr eval_simplify(n,context,assumption)
node_ptr n,context;
bdd_ptr assumption;
{
  if(n == NIL)return(save_bdd(ONE));
  yylineno = n->lineno;
  switch(n->type){
  case AND:
    {
      bdd_ptr l = eval_simplify(car(n),context,assumption);
      bdd_ptr r = eval_simplify(cdr(n),context,assumption);
      bdd_ptr res = save_bdd(simplify_assuming(and_bdd(l,r),assumption));
      release_bdd(l); release_bdd(r); mygarbage();
      return(res);
    }
  case CONTEXT:
    return(eval_simplify(cdr(n),car(n),assumption));
  default:
    return(eval(n,context));
  }
}

static node_ptr eval_cp(l,n,context,assumption)
node_ptr l,n,context;
bdd_ptr assumption;
{
  if(n == NIL)return(l);
  yylineno = n->lineno;
  switch(n->type){
  case AND:
    {
      l = eval_cp(l,car(n),context,assumption);
      l = eval_cp(l,cdr(n),context,assumption);
      return(l);
    }
  case CONTEXT:
    return(eval_cp(l,cdr(n),car(n),assumption));
  default:
    {
      bdd_ptr z = eval(n,context);
      release_bdd(z);
      if(z == ONE)return(l);
      z = simplify_assuming(z,assumption);
      if(size_bdd(z) > conj_part_limit || size_bdd(car(l)) > conj_part_limit)
	return(cons(save_bdd(z),l));
      else{
	release_bdd(car(l));
	l->left.bddtype = save_bdd(and_bdd(car(l),z));
	return(l);
      }
    }
  }
}

static void check_assign(n,context,mode)
int mode;
node_ptr n,context;
{
  if(n == NIL)return;
  yylineno = n->lineno;
  switch(n->type){
  case AND:
    check_assign(car(n),context,mode);
    check_assign(cdr(n),context,mode);
    break;
  case CONTEXT:
    check_assign(cdr(n),car(n),mode);
    break;
  case EQDEF:
    {
      node_ptr t1,t2,t3;
      if(car(n)->type == SMALLINIT | car(n)->type == NEXT){
	t1 = eval_struct(car(car(n)),context);
	t3 = find_node(car(n)->type,t1,NIL);
      }
      else
        t1 = t3 = eval_struct(car(n),context);
      if(mode == 0){
	t2 = find_assoc(symbol_hash,t1);
	if(t2 == NIL)undefined(t1);
	if(t2->type != VAR)redefining(t1);
	if(find_assoc(assign_hash,t3))multiple_assignment(t3);
        if(t3->type == NEXT){
	  bdd_ptr q = (bdd_ptr)find_assoc(frame_hash,t1);
          if(!q)q = running;
	  else{
	    release_bdd(q); q = or_bdd(q,running);
          }
          insert_assoc(frame_hash,t1,save_bdd(q));
	}
	insert_assoc(assign_hash,t3,find_node(CONTEXT,context,cdr(n)));
	insert_assoc(global_assign_hash,t3,yylineno);
      }
      else check_circular_assign(t3,context);
      break;
    }
  default:
    catastrophe("check_assign: type = %d",n->type);
  }
}
	
static print_in_process(s,context)
char *s;
node_ptr context;
{
  fprintf(stderr,"%s",s);
  if(context != NIL)
    indent_node(stderr," in process ",context,"");
  fprintf(stderr,"...\n");
}

static void and_it_in(a,b)
bdd_ptr *a,b;
{
  release_bdd(*a); release_bdd(b);
  *a = save_bdd(and_bdd(*a,b));
  mygarbage();
}

static void check_assign_both(v,t,lineno)
node_ptr v;
int t,lineno;
{
  node_ptr v1 = find_node(t,v,NIL);
  int lineno2 = (int)find_assoc(global_assign_hash,v1);
  if(lineno2){
    yylineno = lineno;
    start_err();
    fprintf(stderr,"assigned ");
    print_node(stderr,v);
    fprintf(stderr,", line %d: assigned ", lineno2);
    print_node(stderr,v1);
    finish_err();
  }
}


static node_ptr list_of_procnames = NIL;
static check_program(procs,spec_expr,fair_expr)
node_ptr procs,spec_expr,fair_expr;
{
  node_ptr l=procs;
  running_atom = string_to_atom("running");

  /* now create the process selector variable */
  if(verbose)fprintf(stderr,"process selector variable:\n");
  list_of_procnames = map(car,procs);
  proc_selector = save_bdd(scalar_var(list_of_procnames,0));
  real_nstvars = nstvars - NSTBASE;

  while(l){
    node_ptr context = car(car(l));
    node_ptr assign_expr = cdr(car(l)),temp_node;
    l = cdr(l);

    /* create the running variable for this process */
    running = save_bdd(equal_bdd(proc_selector,leaf_bdd(context)));
    temp_node = eval_struct(running_atom,context);
    if(find_assoc(symbol_hash,temp_node))redefining(temp_node);
    insert_assoc(symbol_hash,temp_node,find_node(BDD,running,NIL));

    /* now check for  multiple or circular assignments */
    if(verbose)print_in_process("checking for multiple assignments",context);
    check_assign(assign_expr,NIL,0);
    if(verbose)print_in_process("checking for circular assignments",context);
    check_assign(assign_expr,NIL,1);

    clear_hash(assign_hash);
  }

  /* now check specs and fairness constraints */
  {
    node_ptr l1 = spec_expr;
    while(l1){
      check_circ(car(l1),NIL);
      l1 = cdr(l1);
    }
    l1 = fair_expr;
    while(l1){
      check_circ(car(l1),NIL);
      l1 = cdr(l1);
    }
  }

  frame = save_bdd(ONE);
  real_state_variables = NIL;
  l = variables;
  while(l){
    node_ptr v = car(l);
    int lineno = (int)find_assoc(global_assign_hash,v);
    l = cdr(l);
    if(lineno){
      check_assign_both(v,NEXT,lineno);
      check_assign_both(v,SMALLINIT,lineno);
    }
    {
      bdd_ptr q = (bdd_ptr)find_assoc(frame_hash,v);
      bdd_ptr r = eval(v,NIL); release_bdd(r);
      if(option_kripke || q)
	real_state_variables = cons(r,real_state_variables);
      if(q && (q != ONE)){
	release_bdd(q);
	and_it_in(&frame,
		  save_bdd(or_bdd(q,equal_bdd(r,r_shift(r)))));
      }
    }
  }
  clear_hash(frame_hash);
  clear_hash(global_assign_hash);
}

static void build_init(init_expr,procs)
node_ptr init_expr,procs;
{
  node_ptr l=procs;
  if(verbose)print_in_process("evaluating INIT statements",NIL);
  init = eval(init_expr,NIL);
  
  while(l){
    node_ptr context = car(car(l));
    node_ptr assign_expr = cdr(car(l)),temp_node;
    l = cdr(l);

    if(verbose)print_in_process("evaluating init() assignments",context);
    assign_type = INIT;
    and_it_in(&init,eval(assign_expr,NIL));
  }
  if(verbose)fprintf(stderr,
		     "size of global initial set = %g states, %d BDD nodes\n",
		     count_bdd(init),size_bdd(init));
}
    
node_ptr make_support_list(l)
node_ptr l;
{
  bdd_ptr support_bdd();
  if(l == NIL)return(l);
  {
    node_ptr r = make_support_list(cdr(l));
    bdd_ptr s = support_bdd(car(l));
    if(r)return(cons(save_bdd(and_bdd(car(r),s)),r));
    return(cons(save_bdd(s),r));
  }
}

node_ptr make_quantifiers(l,vars)
node_ptr l;
bdd_ptr vars;
{
  if(l == NIL)return(cons(save_bdd(vars),NIL));
  return(cons(save_bdd(varset_diff(vars,car(l))),make_quantifiers(cdr(l),vars)));
}

static void build_model(trans_expr,procs,assumption)
node_ptr trans_expr,procs;
bdd_ptr assumption;
{
  bdd_ptr temp,running;
  node_ptr l=procs;

  trans = save_bdd(ONE);
  invar = save_bdd(ONE);

  while(l){
    node_ptr context = car(car(l));
    node_ptr assign_expr = cdr(car(l)),temp_node;
    l = cdr(l);

    running = eval(running_atom,context);

    /* now evaluate the TRANS, ASSIGN statements */

    if(!option_conj_part){
      if(verbose)print_in_process("evaluating TRANS statements",context);
      temp = eval_simplify(trans_expr,NIL,assumption);
      if(verbose)print_in_process("evaluating next() assignments",context);
      assign_type = TRANS;
      and_it_in(&temp,eval_simplify(assign_expr,NIL,assumption));
      if(verbose)fprintf(stderr,
			 "size of transition relation = %d  BDD nodes\n",
			 size_bdd(temp));
      release_bdd(temp); temp = save_bdd(or_bdd(not_bdd(running),temp));
      and_it_in(&trans,temp);
    }
    else{
      if(cdr(procs))rpterr("cannot use process keyword with conjunctive partitioning");
      cp_trans = cons(save_bdd(ONE),NIL);
      if(verbose)print_in_process("evaluating TRANS statements",context);
      cp_trans = eval_cp(cp_trans,trans_expr,NIL,assumption);
      if(verbose)print_in_process("evaluating next() assignments",context);
      assign_type = TRANS;
      cp_trans = eval_cp(cp_trans,assign_expr,NIL,assumption);
      if(verbose){
	int i = 1;
	node_ptr q = cp_trans;
	fprintf(stderr,"transition relation:\n");
	while(q){
	  fprintf(stderr,"partition %d: size = %d\n",i++,size_bdd(car(q)));
	  q = cdr(q);
	}
      }
      {
	node_ptr sl = make_support_list(cp_trans);
	bdd_ptr cp_vars = vars;
	int i = nstbase;
	while (i) {
	  /*
	   * Quantification should also consider the process selection
	   * variables even for synchronous models, as sat_bdd chooses
	   * them too.
	   */
	  cp_vars = and_bdd(atomic_bdd(i--),cp_vars);
	}
	forward_quantifiers = make_quantifiers(sl,cp_vars);
	reverse_quantifiers = make_quantifiers(sl,r_shift(cp_vars));
	walk(release_bdd,sl);
      }
    }      

    if(verbose)print_in_process("evaluating normal assignments",context);
    assign_type = 0;
    temp = eval_simplify(assign_expr,NIL,assumption);
    if(verbose)fprintf(stderr,
		       "size of invariant set = %g states, %d BDD nodes\n",
		       count_bdd(temp),size_bdd(temp));
    release_bdd(temp); temp = save_bdd(or_bdd(not_bdd(running),temp));
    and_it_in(&invar,temp);

  }

  if(cdr(procs))and_it_in(&trans,save_bdd(frame));
  if(verbose && cdr(procs)){
    fprintf(stderr,
	    "size of global initial set = %d  BDD nodes\n",
	    size_bdd(init));
    fprintf(stderr,
	    "size of global transition relation = %d  BDD nodes\n",
	    size_bdd(trans));
    fprintf(stderr,
	    "size of global invariant set = %d  BDD nodes\n",
	    size_bdd(invar));
  }
}


static bdd_ptr vars1,prime_vars,prime_vars1;
static node_ptr mod1_name,mod2_name;

static bdd_ptr hom_counter(set1,set2,R,Rold)
bdd_ptr set1,set2,R,Rold;
{
  bdd_ptr res = and_bdd(Rold,and_bdd(set2,
				     not_bdd(forsome(vars1,
						     and_bdd(set1,R)))));
  bdd_ptr res1 = sat_bdd(and_bdd(res,set1));
  if(res1 != ZERO)return(save_bdd(res1));
  return(save_bdd(sat_bdd(res)));
}
  
static void impl_message(str)
char *str;
{
  indent_node(stdout,"module ",mod2_name,"");
  printf(" %s module ",str);
  print_node(stdout,mod1_name); printf("\n\n");
}

static bdd_ptr trans_1,init_1,invar_1;


/*
static node_ptr check_simulation(Y,new,invar1,trans1,i)
bdd_ptr invar1,trans1;
{
  while(new != ZERO){
    if(verbose)fprintf(stderr,"iteration %d: BDD size = %d, states = %g\n",
		       i++,size_bdd(Y),count_bdd(Y));
    Z = save_bdd(Y); 
    new = save_bdd(and_bdd(new,invar));
    mygarbage();
    {
      bdd_ptr s0 = sat_bdd(and_bdd(new,not_bdd(invar1)));
      if(s0 != ZERO){
	save_bdd(s0);
	release_bdd(Z);
	release_bdd(new);
	mygarbage();
	return(cons(s0,NIL));
      }
      mygarbage();
      s0 = and_bdd(trans,and_bdd(new,not_bdd(trans1)));
      if(s0 != ZERO){
	bdd_ptr s1 = save_bdd(sat_bdd(and_bdd(invar,r_collapse(s0,ONE))));
	s0 = save_bdd(sat_bdd(collapse(s0,s1)));
	release_bdd(Z);
	release_bdd(new);
	mygarbage();
	return(cons(s0,cons(s1,NIL)));
      }
      mygarbage();
    }
    Y = save_bdd(or_bdd(Y,r_collapse(trans,new)));
    release_bdd(new); 
    mygarbage();
    new = save_bdd(and_bdd(Y,not_bdd(Z)));
    release_bdd(Z); mygarbage(); release_bdd(new);
    {
      node_ptr res = check_simulation(Y,new,invar1,trans1,i+1);
      if(res != NIL)
	res = cons(save_bdd(sat_bdd(and_bdd(invar,
					    r_collapse(trans,car(res))))),res);
      release_bdd(Y);
      return(res);
    }
  }
}


static node_ptr check_init_simulation(init1,invar1,trans1)
bdd_ptr init1,invar1,trans1;
{
  bdd_ptr s0 = and_bdd(init,not_bdd(init1));
  if(s0 != ZERO){
    s0 = save_bdd(sat_bdd(and_bdd(invar,s0)));
    mygarbage();
    return(cons(s0,NIL));
  }
  return(check_simulation(init,init,invar1,trans1,0));
}

*/
static bdd_ptr check_hom(R,Rold,n)
bdd_ptr R,Rold;
int n;
{
  bdd_ptr res,set1,set2;
  if(verbose>0)
    fprintf(stderr,"iteration %d: BDD size = %d\n",n,size_bdd(R));
  res = hom_counter(init_1,init,R,Rold);
  mygarbage();
  if(res != ZERO)impl_message("does not implement");
  else{
    bdd_ptr Rnew = save_bdd(r_shift(and_bdd(R,invar_1)));
    if(verbose>0)fprintf(stderr,"BDD size = %d\n",size_bdd(Rnew));
    mygarbage(); release_bdd(Rnew);
/*    Rnew = save_bdd(not_bdd(forsome(prime_vars1,
				    and_bdd(Rnew,trans_1)))); */
    Rnew = save_bdd(not_bdd(collapse_vars(Rnew,trans_1,prime_vars1)));
    if(verbose>0)fprintf(stderr,"BDD size = %d\n",size_bdd(Rnew));
    mygarbage(); release_bdd(Rnew);
    Rnew = save_bdd(and_bdd(Rnew,r_shift(invar)));
    if(verbose>0)fprintf(stderr,"BDD size = %d\n",size_bdd(Rnew));
    mygarbage(); release_bdd(Rnew);
/*    Rnew = save_bdd(not_bdd(forsome(prime_vars,and_bdd(Rnew,trans)))); */
    Rnew = save_bdd(not_bdd(collapse_no_shift(Rnew,trans)));
    if(verbose>0)fprintf(stderr,"BDD size = %d\n",size_bdd(Rnew));
    mygarbage(); release_bdd(Rnew);
    Rnew = save_bdd(and_bdd(Rnew,R));
    if(verbose>0)fprintf(stderr,"BDD size = %d\n",size_bdd(Rnew));
    mygarbage();
    if(Rnew != R){
      release_bdd(res);
      res = check_hom(Rnew,R,n+1);
      if(res != ZERO){
	set1 = save_bdd(and_bdd(invar_1,r_collapse(trans_1,res)));
	mygarbage();
	set2 = save_bdd(and_bdd(invar,r_collapse(trans,res)));
	release_bdd(res); mygarbage();
	res = hom_counter(set1,set2,R,Rold);
	release_bdd(set1); release_bdd(set2); mygarbage();
      }
    }
    release_bdd(Rnew);
  }
  if(res != ZERO){
    print_state(res,0);
    printf("\n");
  }
  mygarbage();
  return(res);
}


static void check_implements(n1,mod1,n2,mod2)
node_ptr n1,n2,mod1,mod2;
{
  void read_order();
  node_ptr trans1,init1,spec1,fair1,assign1,procs1;
  node_ptr trans2,init2,spec2,fair2,assign2,procs2;
  node_ptr actual;

  if(verbose>0){
    indent_node(stderr,"checking ",n2," implements? ");
    print_node(stderr,n1);
    fprintf(stderr,"\n");
  }
  trans1 = init1 = spec1 = fair1 = assign1 = procs1 = NIL;
  trans2 = init2 = spec2 = fair2 = assign2 = procs1 = NIL;
  the_impl = find_atom(n2);

  actual = car(mod1);

  variables = NIL;
  all_symbols = NIL;
  vars = save_bdd(ONE);
  input_vars = save_bdd(ONE);
  instantiate_mode = 1;
  process_by_name(n1,NIL,&trans1,&init1,&spec1,&fair1,
		      &assign1,&procs1,actual);
  vars1 = vars;

  vars = save_bdd(ONE);
  instantiate_mode = 0;
  process_by_name(n2,the_impl,&trans2,&init2,&spec2,&fair2,
		      &assign2,&procs2,actual);
  
  release_bdd(vars); release_bdd(input_vars);
  vars = save_bdd(and_bdd(vars,input_vars));
  variables = reverse(variables);
  all_symbols = reverse(all_symbols);

  read_order();

  if(verbose>0)indent_node(stderr,"module ",n1,":\n");
/*  catastrophe("check_implements: broken (sorry)"); */

  build_init(init1,procs1);
  build_model(trans1,procs1,ONE);
  trans_1 = trans; init_1 = init; invar_1 = invar;

  if(verbose>0)indent_node(stderr,"module ",n2,":\n");
  build_init(init2,procs2);
  build_model(trans2,procs2,ONE);

  release_bdd(init); init = save_bdd(and_bdd(init,invar));
  release_bdd(init_1); init_1 = save_bdd(and_bdd(init_1,invar_1));

  {
    bdd_ptr R = eval(spec1,NIL);
    prime_vars1 = save_bdd(r_shift(vars1));
    prime_vars = save_bdd(r_shift(vars));
    mod1_name = n1; mod2_name = n2;
    if(check_hom(R,ONE,0) == ZERO)impl_message("implements");
  }  
  /* here clear out all tables and restart BDD package */
  clear_hash(symbol_hash);
  clear_hash(param_hash);
  clear_hash(constant_hash);
  clear_hash(print_hash);
  clear_hash(assign_hash);
  restart_bdd();
  nstvars = 0;
}
      
check_all_implements(parse_tree)
node_ptr parse_tree;
{
  node_ptr m = parse_tree;
  while(m){
    node_ptr n = car(m);
    node_ptr n2 = find_atom(car(car(n)));
    node_ptr mod2 = find_assoc(module_hash,n2);
    node_ptr decls = cdr(mod2);
    while(decls){
      node_ptr d = car(decls);
      decls = cdr(decls);
      if(d->type == IMPLEMENTS){
	node_ptr n1 = find_atom(car(d));
	node_ptr mod1 = find_assoc(module_hash,n1);
	yylineno = (car(d))->lineno;
	if(!mod2)undefined(n1);
	check_implements(n1,mod1,n2,mod2);
      }
    }
    m = cdr(m);
  }
}

static node_ptr approx_list = NIL;

compute_reachable(trans_expr,procs)
node_ptr trans_expr,procs;
{
  extern int option_forward_search,option_restrict_trans,option_AG_only;
  bdd_ptr Y = init,Z,new = init;
  int i = 0;
  approx_list = NIL;
  if(verbose)fprintf(stderr,"searching reachable state space..\n");
  while(new != ZERO){
    if(verbose)fprintf(stderr,"iteration %d: BDD size = %d, states = %g\n",
		       i++,size_bdd(Y),count_bdd(Y));
    if(option_AG_only)approx_list = cons(save_bdd(Y),approx_list);
    Z = save_bdd(Y); 
    if(option_incremental){
      build_model(trans_expr,procs,save_bdd(new));
      release_bdd(new);
    }
    new = save_bdd(and_bdd(new,invar));
    mygarbage();
    Y = save_bdd(or_bdd(Y,cp_forward(new)));
    release_bdd(new); 
    if(option_incremental){
      release_bdd(trans); release_bdd(invar);
      if(option_conj_part)walk(release_bdd,cp_trans);
    }
    mygarbage();
    new = save_bdd(and_bdd(Y,not_bdd(Z)));
    release_bdd(Z); mygarbage(); release_bdd(Y); release_bdd(new);
  }
  reachable_states = save_bdd(Y);
  if(option_restrict_trans | option_incremental){
    build_model(trans_expr,procs,reachable_states);
    mygarbage();
    if(verbose)fprintf(stderr,
		    "size of simplified transition relation: %d BDD nodes\n",
		       size_bdd(trans));
  }
}

print_reachable_states()
{
  extern int option_print_reachable,bits_encoding_var;
  extern bdd_ptr forall(),support_bdd();
  if(option_print_reachable){
    if(!reachable_states)compute_reachable(NIL,NIL);
    {
      bdd_ptr mask = save_bdd(ONE),r = reachable_states;
      int n = 0;
      node_ptr l = real_state_variables;
      while(l){
	release_bdd(mask);
	mask = save_bdd(and_bdd(mask,make_var_mask(car(l))));
	mygarbage();
	n += bits_encoding_var;
	l = cdr(l);
      }
      if(option_kripke){
	bdd_ptr iv = forall(support_bdd(proc_selector),invar);
	r = and_bdd(reachable_states,iv);
      }
      {
	double log();
	double reached = n_count_bdd(and_bdd(r,mask),n);
	double space = n_count_bdd(mask,n);
        printf("reachable states: %g (2^%g) out of %g (2^%g)\n",
	       reached, log(reached)/log(2.0),
	       space, log(space)/log(2.0));
      }
    }
  }
}

static node_ptr cont_AG_counterexample(l,p)
node_ptr l,p;
{
  bdd_ptr s;
  if(l == NIL)return(p);
  s = save_bdd(sat_bdd(and_bdd(car(l),and_bdd(invar,cp_reverse(car(p))))));
  mygarbage();
  if(s == ZERO)catastrophe("make_AG_counterexample: s == ZERO");
  return(cont_AG_counterexample(cdr(l),cons(s,p)));
}

static node_ptr make_AG_counterexample(l,s0)
node_ptr l;
bdd_ptr s0;
{
  node_ptr p;
  bdd_ptr s;
  if(l == NIL)return(NIL);
  p = make_AG_counterexample(cdr(l),s0);
  if(p != NIL)return(p);
  s = sat_bdd(and_bdd(car(l),s0));
  if(s == ZERO)return(NIL);
  return(cont_AG_counterexample(cdr(l),cons(save_bdd(s),NIL)));
}


static int check_AG_only(n,context)
node_ptr n,context;
{
  if(n == NIL)return(1);
  switch(n->type){
  case CONTEXT:
    return(check_AG_only(cdr(n),car(n)));
  case AND:
    return(check_AG_only(n->left,context) & check_AG_only(n->right,context));
  case AG:
    {
      bdd_ptr s0 = eval(car(n),context);
      release_bdd(s0);
      s0 = save_bdd(and_bdd(reachable_states,
				    and_bdd(invar,not_bdd(s0))));
      mygarbage();
      if(s0 == ZERO){release_bdd(s0); return(1);}
      {
	node_ptr l = make_AG_counterexample(approx_list,s0);
	release_bdd(s0);
	print_explanation(n,l,0,context);
	explain(car(reverse(l)),car(n),context);
	return(0);
      }
    }
  default:
    return;
  }
}


void output_order()
{
  extern char *output_order_file;
  if(output_order_file){
    FILE *f = fopen(output_order_file,"w");
    node_ptr l = variables;
    if(!f)rpterr("cannot open %s for output",output_order_file);
    while(l){
      print_node(f,car(l));
      fprintf(f,"\n");
      l = cdr(l);
    }
    if(fclose(f) == EOF)rpterr("cannot close %s",output_order_file);
    if(verbose>1)
      fprintf(stderr,"smv: variable order output to file %s\n",output_order_file);
    exit(0);
  }
}



void read_order()
{
  extern char *input_order_file;
  node_ptr orig_variables = variables;
  int token;
  if(input_order_file){
    variables = NIL;
    open_input(input_order_file);
    token = yylex();
    while(token){
      node_ptr var = NIL;
      while(1){
	if(token != ATOM)rpterr("syntax error");
	var = find_node(DOT,var,find_atom(yylval.node));
	token = yylex();
	if(token != DOT)break;
	token = yylex();
      }
      variables = cons(var,variables);
    }
    variables = reverse(variables);
  }
  close_input();
  {
    node_ptr l=variables;
    while(l){
      node_ptr n = car(l);
      node_ptr q = find_assoc(symbol_hash,n);
      if(!q || q->type != VAR){
	start_err();
	indent_node(stderr,"unknown variable in order file :",n,"");
	finish_err();
      }
      if(car(q)){
	start_err();
	indent_node(stderr,"variable appears twice in order file :",n,"");
	finish_err();
      }
      if(verbose > 1){
	print_node(stderr,n);
	fprintf(stderr,":\n");
      }
      q->left.bddtype = save_bdd(scalar_var(cdr(q),nstvars));
      l = cdr(l);
    }
    l = orig_variables;
    while(l){
      node_ptr n = car(l);
      node_ptr q = find_assoc(symbol_hash,n);
      if(!q || q->type != VAR)catastrophe("read_order: orig_variables");
      if(!car(q)){
	start_err();
	indent_node(stderr,"not in order file: ",n,"");
	finish_err();
      }
      l = cdr(l);
    }
  }
}    
  
  
void check_spec(the_spec)
node_ptr the_spec;
{
  bdd_ptr s0;
  node_ptr exp;
  if(!fair_states)fair_states = save_bdd(eg(ONE));
  s0 = eval(the_spec,NIL);
  release_bdd(s0);
  s0 = save_bdd(sat_bdd(and_bdd(init,and_bdd(invar,not_bdd(s0)))));
  printf("-- ");
  print_spec(stdout,the_spec);
  if(s0 == ZERO)
    printf("is true\n");
  else{
    printf("is false\n");
    exp = reverse(explain(cons(s0,NIL),the_spec,NIL));
    if(!exp)exp=cons(s0,NIL);
    print_explanation(exp);
  }
  release_bdd(s0);
}

bdd_ptr interactive_state;
node_ptr interactive_label;


void goto_state(s)
node_ptr s;
{
  bdd_ptr d = (bdd_ptr)find_assoc(state_hash,s);
  if(d) {
    interactive_state = d;
    interactive_label = s;
    clear_hash(print_hash);
    print_state(d,1);
  }
  else indent_node(stderr,"no label ",s,"\n");
}

void assign_command(var,val)
node_ptr var,val;
{
  extern bdd_ptr support_bdd();
  node_ptr x;
  if(!interactive_state){
    fprintf(stderr,"no current state defined\n");
    return;
  }
  x = find_assoc(symbol_hash,eval_struct(var,NIL));
  if(!x || x->type != VAR)indent_node(stderr,"",var," is not a variable\n");
  else {
    bdd_ptr v = eval(var,NIL);
    bdd_ptr r = eval(val,NIL);
    bdd_ptr w = leaf_bdd((node_ptr)(value_bdd(if_then_bdd(interactive_state,r))));
    bdd_ptr q = setin_bdd(v,w);
    if(q == ZERO){
      indent_node(stderr,"cannot assign ",w->left," to variable ");
      print_node(stderr,var);
      fprintf(stderr,"\n");
      return;
    }
    interactive_state = save_bdd(sat_bdd(and_bdd(forsome(support_bdd(v),interactive_state),q)));
    interactive_label = NIL;
    print_state(interactive_state,1);
  }
}

void single_step()
{
  node_ptr q;
  if(!interactive_state){
    fprintf(stderr,"no current state defined\n");
    return;
  }
  if(interactive_label){
    node_ptr new_label = find_node(DOT,car(interactive_label),
				   plus_node(cdr(interactive_label),one_number));
    bdd_ptr z = (bdd_ptr)find_assoc(state_hash,new_label);
    if(z){
      indent_node(stdout,"state ",new_label,":\n");
      interactive_state = z;
      interactive_label = new_label;
      print_state(z,1);
      return;
    }
    else indent_node(stderr,"no state ",new_label,"\n");
  }
  q = ex_explain(cons(interactive_state,NIL),ONE);
  if(!q)
    fprintf(stderr,"current state has no successor\n");
  else{
    interactive_state = (bdd_ptr)car(q);
    print_state(interactive_state,1);
  }
}

void eval_command(exp)
node_ptr exp;
{
  bdd_ptr r;
  node_ptr w;
  if(!interactive_state){
    fprintf(stderr,"no current state defined\n");
    return;
  }
  r = eval(exp,NIL);
  w = (node_ptr)(value_bdd(if_then_bdd(interactive_state,r)));
  indent_node(stdout,"= ",w,"\n");
  {
    node_ptr expl = reverse(explain(cons(interactive_state,NIL),exp,NIL));
    if(expl){
      print_explanation(expl);
    }
  }
}

void trans_command(n)
node_ptr n;
{
  bdd_ptr t = eval(n,NIL);
  release_bdd(t); release_bdd(trans);
  trans = save_bdd(and_bdd(trans,t));
  if(fair_states)release_bdd(fair_states); fair_states = (bdd_ptr)0;
  mygarbage();
}

void init_command(n)
node_ptr n;
{
  bdd_ptr t = eval(n,NIL);
  release_bdd(t); release_bdd(init);
  init = save_bdd(and_bdd(init,t));
  mygarbage();
}

void fair_command(n)
node_ptr n;
{
  bdd_ptr t;
  if(fair_states)release_bdd(fair_states); fair_states = (bdd_ptr)0;
  t = eval(n,NIL);
  fairness_const = cons(find_node(BDD,t,NIL),fairness_const);
}

void reset_command()
{
  release_bdd(trans); release_bdd(init);
  if(fair_states)release_bdd(fair_states); fair_states = (bdd_ptr)0;
  trans = save_bdd(orig_trans);
  init = save_bdd(orig_init);
  fairness_const = orig_fairness_const;
}

void build_symbols()
{
  extern int option_forward_search,option_AG_only,heuristics,option_interactive;
  extern int interactive_mode;
  extern FILE *yyin;
  node_ptr trans_expr,init_expr,spec_expr,fair_expr,assign_expr,procs;
  bdd_ptr s0;
  node_ptr m;

  /* set up constant symbols for bdd.c */
  zero_number = find_node(NUMBER,0,NIL);
  one_number = find_node(NUMBER,1,NIL);
  ZERO = save_bdd(leaf_bdd(zero_number));
  ONE  = save_bdd(leaf_bdd(one_number));

  boolean_type = cons(zero_number,cons(one_number,NIL));

  /* build the module table */
  parse_tree = reverse(parse_tree);
  module_hash = new_assoc();
  m = parse_tree;
  while(m){
    node_ptr n = car(m);
    node_ptr name = find_atom(car(car(n)));
    node_ptr params = cdr(car(n));
    node_ptr def = cdr(n);
    m = cdr(m);
    if(find_assoc(module_hash,name))redefining(name);
    insert_assoc(module_hash,name,new_node(LAMBDA,params,reverse(def)));
  }

  symbol_hash = new_assoc();
  param_hash = new_assoc();
  constant_hash = new_assoc();
  print_hash = new_assoc();
  assign_hash = new_assoc();
  global_assign_hash = new_assoc();
  frame_hash = new_assoc();
  value_hash = new_assoc();
  state_hash = new_assoc();

  check_all_implements(parse_tree);

  /* now build the symbol table */
  variables = NIL;
  all_symbols = NIL;
  vars = save_bdd(ONE);
  m = string_to_atom("main");
  trans_expr = init_expr = spec_expr = fair_expr = assign_expr = procs = NIL;
  instantiate_mode = 0;
  process_by_name(m,NIL,&trans_expr,&init_expr,&spec_expr,&fair_expr,
		      &assign_expr,&procs,NIL);
  variables = reverse(variables);
  all_symbols = reverse(all_symbols);
  spec_expr = reverse(spec_expr);
  fair_expr = reverse(fair_expr);

  read_order();
  output_order();
  check_program(procs,spec_expr,fair_expr);


  build_init(init_expr,procs);
  if(!(option_forward_search && option_incremental))
    build_model(trans_expr,procs,ONE);
  if(option_forward_search)compute_reachable(trans_expr,procs);

  if(verbose)fprintf(stderr,"evaluating fairness constraints...\n");
  fairness_const = eval_tree(fair_expr,NIL);
  the_node = one_number;

  /* now evaluate the specifications */
  {
    node_ptr l = spec_expr;
    while(l){
      node_ptr the_spec = car(l);
      l = cdr(l);
      if(verbose){
	fprintf(stderr,"evaluating ");
	print_spec(stderr,the_spec);
	fprintf(stderr,"\n");
      }
      if(!(option_AG_only && option_forward_search)){
	check_spec(the_spec);
      }
      else
	check_AG_only(the_spec,NIL);
    }
  }
  print_usage();
  printf("BDD nodes representing transition relation: %d + %d\n",
	 size_bdd(trans),size_bdd(invar));
  print_reachable_states();

  if(option_interactive){
    interactive_state = (bdd_ptr)0;
    interactive_label = NIL;
    interactive_mode = 1;
    yyin = stdin;
    orig_trans = save_bdd(trans);
    orig_init = save_bdd(init);
    orig_fairness_const = fairness_const;
    yyparse();
  }
}
