#include <stdlib.h>
#include <stdio.h>

/* BDD stuff */
#include <bdd.h>
#include <fdd.h>
#include <bvec.h>

/* Mosml stuff */
#include <mlvalues.h> 
#include <fail.h>
#include <alloc.h>
#include <memory.h>


/* Reduced Ordered Binary Decision Diagrams: interface to
   Jørn Linds <jl@it.dtu.dk> BuDDy library.
   Made by Ken Larsen <kfl@itu.dk>

   The type bdd.bdd of a Binary Decision Diagram is an abstract type;
   really a BDD structure.  This will contain an integer which is a
   root number.  The root number cannot just be treated as an ordinary
   int for two reasons:
   
   1. The gc cannot understand the root number (it would be confused
      by the untagged integer field)

   2. The (camlrunm) gc don't know how to garbage collect a bdd 
      (call bdd_delref from the bdd lib.)
   
   This raises the question how to deallocate the bdd structure when
   it is no longer reachable.  One possibility is to use finalized
   objects, calling the bdd_delref function explicitly whenever a bdd
   value is about to be garbage-collected by the camlrunm runtime
   systemq.

   A bdd should be a finalized object: a pair, 

              header with Final_tag
	      0: finalization function mlbdd_finalize
	      1: the bdd's root number

   whose component 0 is a pointer to the finalizing function
   mlbdd_finalize, and whose component 1 is a root number.  The
   finalization function should apply bdd_delref to the second
   component of the pair: */

/* A nice macro to have */
#define Bdd_val(x) (Field(x, 1))

/* I don't want to adjust the GC so I've made my own alloc_final,
   stolen from alloc.c
*/
value mlbdd_alloc_final(mlsize_t len, final_fun fun)
{
  value result;
  result = alloc_shr(len, Final_tag);
  Field (result, 0) = (value) fun;
  return result;
} 

/* Sometimes it is nice to raise the Domain exception
 */
#define RAISE_DOMAIN mlraise(Atom(SMLEXN_DOMAIN))

void mlbdd_errorhandler(int errorcode) 
{
  /* printf("mlbdd error: %d\n",errorcode); */
  failwith((char *) bdd_errstring(errorcode));
} 


void mlbdd_gc(int num, bddGbcStat* foo)
{
  if(num==1) { 
    printf ("<"); 
    gc_full_major(Val_unit); /* Increases speed from fx. 17.6 to 15.3 = 13% */
    printf ("$");
    fflush(stdout);
  }
  else if(num==0) { printf(">"); fflush(stdout); }
  else { failwith ("mlbdd internal error"); }
}

/* ML type: int -> int -> unit */
value mlbdd_bdd_init(value nodes, value cachesize) /* ML */
{
  /* setup the our error handler */
  bdd_error_hook(&mlbdd_errorhandler);
  bdd_init(Int_val(nodes), Int_val(cachesize));
  bdd_error_hook(&mlbdd_errorhandler);
  /* bdd_gbc_hook(NULL); */
  bdd_gbc_hook(mlbdd_gc);
  return Val_unit;    
}

/* ML type: unit -> unit */
value mlbdd_bdd_done(value nill) /* ML */
{
  bdd_done();
  return Val_unit;
}

/* ML type: unit -> bool */
value mlbdd_bdd_isrunning(value nill) /* ML */
{
  return bdd_isrunning() ? Val_true : Val_false;
}

/* ML type: int -> unit */
value mlbdd_bdd_setvarnum(value n) /* ML */
{ 
  bdd_setvarnum(Int_val(n));
  return Val_unit;
}

/* ML type: unit -> int */
value mlbdd_getvarnum(value dummy) /* ML */
{ 
  return Val_long(bdd_varnum());
}


/* When the bdd becomes unreachable from the ML process, it will be
   garbage-collected, mlbdd_finalize() will be called on the bdd,
   which will do the necessary bdd-bookkeeping.  */
void mlbdd_finalize(value obj) 
{
  bdd_delref(Bdd_val(obj));
}

/* Creation of a bdd makes a finalized pair (mlbdd_finalize, root) as
   described above. */
value mlbdd_make(BDD root) 
{
  value res;
  bdd_addref(root);
  res = mlbdd_alloc_final(2, &mlbdd_finalize);
  Bdd_val(res) = root;  /* Hopefully a BDD fits in a long */
  return res;
}

/* FOR INTERNAL USAGE */
/* ML type: bdd -> int */
value mlbdd_root(value r) /* ML */
{
  return Val_int(Bdd_val(r));
}

/* ML type: varnum -> bdd */
value mlbdd_bdd_ithvar(value i) /* ML */
{ 
  return mlbdd_make(bdd_ithvar(Int_val(i)));
}

/* ML type: varnum-> bdd */
value mlbdd_bdd_nithvar(value i) /* ML */
{ 
  return mlbdd_make(bdd_nithvar(Int_val(i)));
}

/* ML type: bool -> bdd */
value mlbdd_fromBool(value b) /* ML */
{
  return mlbdd_make(Bool_val(b) ? bddtrue : bddfalse);
}

/* ML type: bdd -> bool */
value mlbdd_toBool(value obj)    /* ML */
{
  BDD root;
  root = Bdd_val(obj);
  if(root == bddtrue)       return Val_true;
  else if(root == bddfalse) return Val_false;
  else RAISE_DOMAIN;
}

/* ML type: bdd -> varnum */
value mlbdd_bdd_var(value r) /* ML */
{
  return Val_int(bdd_var(Bdd_val(r)));
}

/* ML type: bdd -> bdd */
value mlbdd_bdd_low(value r) /* ML */
{
  return mlbdd_make(bdd_low(Bdd_val(r)));
}

/* ML type: bdd -> bdd */
value mlbdd_bdd_high(value r) /* ML */
{
  return mlbdd_make(bdd_high(Bdd_val(r)));
}

/* Pass the opr constants from <bdd.h> to ML */ 
/* ML type: unit -> int * int * int * int * int * int * int * int * int *int 	                   * int * int * int * int * int * int * int * int */
value mlbdd_constants(value unit)	/* ML */
{
  value res = alloc_tuple(18);
  Field(res, 0)  = Val_long(bddop_and);
  Field(res, 1)  = Val_long(bddop_xor);
  Field(res, 2)  = Val_long(bddop_or);
  Field(res, 3)  = Val_long(bddop_nand);
  Field(res, 4)  = Val_long(bddop_nor);
  Field(res, 5)  = Val_long(bddop_imp);
  Field(res, 6)  = Val_long(bddop_biimp);
  Field(res, 7)  = Val_long(bddop_diff);
  Field(res, 8)  = Val_long(bddop_less);
  Field(res, 9)  = Val_long(bddop_invimp);
  Field(res, 10) = Val_long(BDD_REORDER_FIXED);
  Field(res, 11) = Val_long(BDD_REORDER_FREE);
  Field(res, 12) = Val_long(BDD_REORDER_WIN2);
  Field(res, 13) = Val_long(BDD_REORDER_WIN2ITE);
  Field(res, 14) = Val_long(BDD_REORDER_SIFT);
  Field(res, 15) = Val_long(BDD_REORDER_SIFTITE);
  Field(res, 16) = Val_long(BDD_REORDER_RANDOM);
  Field(res, 17) = Val_long(BDD_REORDER_NONE);

  return res;
}


/* ML type: bdd -> bdd -> int -> bdd */
value mlbdd_bdd_apply(value left, value right, value opr) /* ML */
{
  return mlbdd_make(bdd_apply(Bdd_val(left),Bdd_val(right), 
				Int_val(opr)));
}

/* ML type: bdd -> bdd */
value mlbdd_bdd_not(value r) /* ML */
{
  return mlbdd_make(bdd_not(Bdd_val(r)));
}

/* ML type: bdd -> bdd -> bdd -> bdd */
value mlbdd_bdd_ite(value x, value y, value z) /* ML */
{
  return mlbdd_make(bdd_ite(Bdd_val(x), Bdd_val(y), Bdd_val(z)));
}


/* ML type: bdd -> bdd -> bool */
value mlbdd_equal(value left, value right) /* ML */
{
  return ((Bdd_val(left) == Bdd_val(right)) ? Val_true : Val_false);
}

/* ML type: bdd -> bdd -> bdd */
value mlbdd_bdd_restrict(value r, value var) /* ML */
{
  return mlbdd_make(bdd_restrict(Bdd_val(r),Bdd_val(var)));
}

/* ML type: bdd -> bdd -> int -> bdd */
value mlbdd_bdd_compose(value f, value g, value var) /* ML */
{
  return mlbdd_make(bdd_compose(Bdd_val(f),Bdd_val(g),Int_val(var)));
}



/* ML type: bdd -> bdd -> bdd */
value mlbdd_bdd_simplify(value f, value d) /* ML */
{
  return mlbdd_make(bdd_simplify(Bdd_val(f), Bdd_val(d)));
}

/* ML type: bdd -> unit */
value mlbdd_bdd_printdot(value r) /* ML */
{
  bdd_printdot(Bdd_val(r));
  return Val_unit;
}

/* ML type: bdd -> unit */
value mlbdd_bdd_printset(value r) /* ML */
{
  bdd_printset(Bdd_val(r));
  fflush(stdout);
  return Val_unit;
}

/* ML type: string -> bdd -> unit */
value mlbdd_bdd_fnprintset(value filename, value r) /* ML */
{
  char *fname;
  FILE *ofile;
  fname = String_val(filename);
  ofile = fopen(fname, "w");
  if (ofile == NULL)
    failwith("Unable to open file");
  else {
    bdd_fprintset(ofile, Bdd_val(r));
    fclose(ofile);
  }
  return Val_unit;
}


/* ML type: string -> bdd -> unit */
value mlbdd_bdd_fnprintdot(value filename, value r) /* ML */
{
  bdd_fnprintdot(String_val(filename), Bdd_val(r));
  return Val_unit;
}

/* ML type: unit -> unit */
value mlbdd_bdd_printall(value nill) /* ML */
{
  bdd_printall();
  return nill;
}

/* ML type: unit -> int * int * int * int * int * int * int * int */
value mlbdd_bdd_stats(value nill)
{
  static bddStat stat;
  value result = alloc_tuple(8);

  bdd_stats(& stat);

  Field(result, 0) = Val_long(stat.produced);
  Field(result, 1) = Val_long(stat.nodenum);
  Field(result, 2) = Val_long(stat.maxnodenum);
  Field(result, 3) = Val_long(stat.freenodes);
  Field(result, 4) = Val_long(stat.minfreenodes);
  Field(result, 5) = Val_long(stat.varnum);
  Field(result, 6) = Val_long(stat.cachesize);
  Field(result, 7) = Val_long(stat.gbcnum);

  return result;
}

/* ML type: bdd -> real */ 
value mlbdd_bdd_satcount(value r) /* ML */
{
  return copy_double(bdd_satcount(Bdd_val(r)));
}

/* ML type: bdd -> varSet */
value mlbdd_bdd_satone(value r) /* ML */
{
  return mlbdd_make(bdd_satone(Bdd_val(r)));
}

/* ML type: bdd -> int */ 
value mlbdd_bdd_nodecount(value r) /* ML */
{
  return Val_int(bdd_nodecount(Bdd_val(r)));
}



/* Some helper functions for creating variable sets, these will be
   represented as BDD's on the C side but as a different type (varSet) on
   the ML side.
*/

/* ML type: varnum vector -> varSet */
value mlbdd_makeset(value varvector) /* ML */
{
  int size, i, *v;
  value result;

  size = Wosize_val(varvector);

  /* we use stat_alloc which guarantee that we get the memory (or it
     will raise an exception). */
  v  = (int *) stat_alloc(sizeof(int) * size);
  for (i=0; i<size; i++) {
     v[i] = Int_val(Field(varvector, i));
  }

  /* we assume that vector is sorted on the ML side */
  result = mlbdd_make(bdd_makeset(v, size));
 
  /* memory allocated with stat_alloc, should be freed with
     stat_free.*/
  stat_free((char *) v);

  return result;
}

/* ML type: varSet -> varnum vector */
value mlbdd_bdd_scanset(value varset)
{
  value result;
  int *v, n, i;

  if(bdd_scanset(Bdd_val(varset), &v, &n))
    RAISE_DOMAIN;
  else {
    if(n == 0)
      result = Atom(0); /* The empty vector */
    else {
      result = n < Max_young_wosize ? alloc(n, 0) : alloc_shr(n, 0);
      for (i = 0; i < n; i++) {
	Field(result, i) = Val_long(v[i]);
      }
      free(v);
    }
  }
  return result;
}

/* ML type: bdd -> varSet */
value mlbdd_bdd_support(value b) /* ML */
{
  return mlbdd_make(bdd_support(Bdd_val(b)));
}

/* ML type: bdd -> varSet -> bdd */
value mlbdd_bdd_exist(value b1, value varset) /* ML */
{
  return mlbdd_make(bdd_exist(Bdd_val(b1),Bdd_val(varset)));
}

/* ML type: bdd -> varSet -> bdd */
value mlbdd_bdd_forall(value b1, value varset) /* ML */
{
  return mlbdd_make(bdd_forall(Bdd_val(b1),Bdd_val(varset)));
}

/* ML type: bdd -> bdd -> int -> varSet -> bdd */
value mlbdd_bdd_appall(value left, value right, 
			 value opr,  value varset) /* ML */
{
  return mlbdd_make(bdd_appall(Bdd_val(left),Bdd_val(right), 
				 Int_val(opr), Bdd_val(varset)));
}

/* ML type: bdd -> bdd -> int -> varSet -> bdd */
value mlbdd_bdd_appex(value left, value right, 
			value opr,  value varset) /* ML */
{
  return mlbdd_make(bdd_appex(Bdd_val(left),Bdd_val(right), 
				 Int_val(opr), Bdd_val(varset)));
}


/* Some helper for making BddPairs, which on the ML side is called
   pairSet. pairSet is implemented very similar to bdd, i.e. as
   finalized objects. */

#define PairSet_val(x) ((bddPair *) Field(x, 1))


void mlbdd_pair_finalize(value pairset)
{
  bdd_freepair(PairSet_val(pairset));
}

/* ML type: varnum vector -> varnum vector -> pairSet */
value mlbdd_makepairset(value oldvar, value newvar) /* ML */
{
  int size, i, *o, *n;
  bddPair *pairs;
  value result;

  size = Wosize_val(oldvar);

  /* we use stat_alloc which guarantee that we get the memory (or it
     will raise an exception). */
  o    = (int *) stat_alloc(sizeof(int) * size);
  n    = (int *) stat_alloc(sizeof(int) * size);

  for (i=0; i<size; i++) {
     o[i] = Int_val(Field(oldvar, i));
     n[i] = Int_val(Field(newvar, i));
  }

  pairs = bdd_newpair();
  bdd_setpairs(pairs, o, n, size);

  /* memory allocated with stat_alloc, should be freed with
     stat_free.*/
  stat_free((char *) o);
  stat_free((char *) n);

  result = mlbdd_alloc_final(2, &mlbdd_pair_finalize);
  PairSet_val(result) = (value) pairs;

  return result;
}

/* ML type: bdd -> pairSet -> bdd */
value mlbdd_bdd_replace(value r, value pair) /* ML */
{
  return mlbdd_make(bdd_replace(Bdd_val(r), PairSet_val(pair)));
}


/* REORDER FUNCTIONS */

/* ML type: varnum -> varnum -> fixed -> unit */
value mlbdd_bdd_intaddvarblock(value first, value last, value fixed) /* ML */
{
  bdd_intaddvarblock(Int_val(first), Int_val(last), Int_val(fixed));
  return Val_unit;
}

/* ML type:  unit -> unit */
value mlbdd_bdd_clrvarblocks(value dummy) /* ML */
{
  bdd_clrvarblocks();
  return dummy;
}

/* ML type: method -> unit  */
value mlbdd_bdd_reorder(value method) /* ML */
{
  bdd_reorder(Int_val(method));
  return Val_unit;
}

/* ML type: method -> method  */
value mlbdd_bdd_autoreorder(value method) /* ML */
{
  return Val_long(bdd_autoreorder(Int_val(method)));
}

/* ML type: method -> int -> method  */
value mlbdd_bdd_autoreorder_times(value method, value times) /* ML */
{
  return Val_long(bdd_autoreorder_times(Int_val(method), Int_val(times)));
}


/* ML type: unit -> method  */
value mlbdd_bdd_getreorder_method(value dummy) /* ML */
{
  return Val_long(bdd_getreorder_method());

}

/* ML type: unit -> int     */
value mlbdd_bdd_getreorder_times(value dummy) /* ML */
{
  return Val_long(bdd_getreorder_times());
}


/* ML type: unit -> unit  */
value mlbdd_bdd_disable_reorder(value dummy) /* ML */
{
  bdd_disable_reorder();
  return dummy;
}

/* ML type: unit -> unit  */
value mlbdd_bdd_enable_reorder(value dummy) /* ML */
{
  bdd_enable_reorder();
  return dummy;
}


/* ML type: varnum -> level  */
value mlbdd_bdd_var2level(value num) /* ML */
{
  return Val_long(bdd_var2level(Int_val(num)));
}

/* ML type: level -> varnum  */
value mlbdd_bdd_level2var(value lev) /* ML */
{
  return Val_long(bdd_level2var(Int_val(lev)));
}

/* FDD FUNCTIONS */

/* ML type: int vector -> fddvar */
value mlfdd_extdomain(value vector) /* ML */
{
  int size, i, *v,k;
  value result;

  size = Wosize_val(vector);

  /* we use stat_alloc which guarantee that we get the memory (or it
     will raise an exception). */
  v  = (int *) stat_alloc(sizeof(int) * size);
  for (i=0; i<size; i++) {
    v[i] = Int_val(Field(vector, i));
  }
  k = fdd_extdomain(v, size);
  result = Val_int(k);
 
  /* memory allocated with stat_alloc, should be freed with
     stat_free.*/
  stat_free((char *) v);

  return result;
}

/* ML type: unit -> unit */
value mlfdd_clearall(value foo) /* ML */
{
  fdd_clearall();
  
  return Val_unit;
}

/* ML type: unit -> int */
value mlfdd_domainnum(value foo) /* ML */
{
  return Val_int(fdd_domainnum());
}

/* ML type: fddvar -> int */
value mlfdd_domainsize(value var) /* ML */
{
  return Val_int(fdd_domainsize(Int_val(var)));
}

/* ML type: fddvar -> int */
value mlfdd_varnum(value var) /* ML */
{
  return Val_int(fdd_varnum(Int_val(var)));
}

/* ML type: fddvar -> varnum vector */
value mlfdd_vars(value var) /* ML */
{
  value result;
  int *v, n, i;

  n = fdd_varnum(Int_val(var));
  v = fdd_vars(Int_val(var));
  
  if(n == 0)
    result = Atom(0);  /* The empty vector */
  else {
    result = n < Max_young_wosize ? alloc(n, 0) : alloc_shr(n, 0);
    for (i = 0; i < n; i++) {
      Field(result, i) = Val_long(v[i]);
    }
    free(v);
  }

  return result;
}

/* ML type: fddvar -> varSet */
value mlfdd_ithset(value var) /* ML */
{
  return mlbdd_make(fdd_ithset(Int_val(var)));
}

/* ML type: fddvar -> bdd */
value mlfdd_domain(value var) /* ML */
{
  return mlbdd_make(fdd_domain(Int_val(var)));
}

/* ML type: fddvar vector -> varSet */
value mlfdd_makeset(value vector) /* ML */
{
  int size, i, *v;
  value result;

  size = Wosize_val(vector);

  /* we use stat_alloc which guarantee that we get the memory (or it
     will raise an exception). */
  v  = (int *) stat_alloc(sizeof(int) * size);
  for (i=0; i<size; i++) {
     v[i] = Int_val(Field(vector, i));
  }

  result = mlbdd_make(fdd_makeset(v, size));
 
  /* memory allocated with stat_alloc, should be freed with
     stat_free.*/
  stat_free((char *) v);

  return result;
}


/* ML type: fddvar vector -> fddvar vector -> pairSet */
value mlfdd_setpairs(value oldvar, value newvar) /* ML */
{
  int size, i, *o, *n;
  bddPair *pairs;
  value result;

  size = Wosize_val(oldvar);

  /* we use stat_alloc which guarantee that we get the memory (or it
     will raise an exception). */
  o    = (int *) stat_alloc(sizeof(int) * size);
  n    = (int *) stat_alloc(sizeof(int) * size);

  for (i=0; i<size; i++) {
     o[i] = Int_val(Field(oldvar, i));
     n[i] = Int_val(Field(newvar, i));
  }

  pairs = bdd_newpair();
  fdd_setpairs(pairs, o, n, size);

  /* memory allocated with stat_alloc, should be freed with
     stat_free.*/
  stat_free((char *) o);
  stat_free((char *) n);

  result = mlbdd_alloc_final(2, &mlbdd_pair_finalize);
  PairSet_val(result) = (value) pairs;

  return result;
}

/* BVEC FUNCTIONS */

#define bvecbitnum_val(x) ((int)  (Field(x, 1)))
#define bvecbitvec_val(x) ((BDD*) (Field(x, 2)))

BVEC BVEC_val(value obj) {
  BVEC t;
  t.bitnum=bvecbitnum_val(obj);
  t.bitvec=bvecbitvec_val(obj);
  return t;
}

/* When the bvec becomes unreachable from the ML process, it will be
   garbage-collected, mlbdd_finalize_bvec() will be called on the bvec,
   which will do the necessary bvec-bookkeeping.  */
void mlbdd_finalize_bvec(value obj) 
{
  bvec_free(BVEC_val(obj));
}

/* Creation of a bvec makes a finalized pair (mlbdd_finalize, bitnum, bitvec) */
value mlbdd_make_bvec(BVEC v) 
{
  value res;
  res = mlbdd_alloc_final(3, &mlbdd_finalize_bvec);
  bvecbitnum_val(res) = v.bitnum; 
  bvecbitvec_val(res) = v.bitvec;  /* Hopefully a pointer fits in a long */
  return res;
}

/* ML type: precision -> bvec */
value mlbvec_true(value bits) {
  return mlbdd_make_bvec(bvec_true(Int_val(bits)));
}

/* ML type: precision -> bvec */
value mlbvec_false(value bits) {
  return mlbdd_make_bvec(bvec_false(Int_val(bits)));
}

/* ML type: precision -> const -> bvec */
value mlbvec_con(value bits, value val) /* ML */
{
  return mlbdd_make_bvec(bvec_con(Int_val(bits), Int_val(val)));
}

/* ML type: precision -> varnum -> int -> bvec */
value mlbvec_var(value bits, value var, value step) /* ML */
{
  return mlbdd_make_bvec(bvec_var(Int_val(bits), Int_val(var), Int_val(step)));
}

/* ML type:  bvecvar -> bvec */
value mlbvec_varfdd(value var) /* ML */
{
  return mlbdd_make_bvec(bvec_varfdd(Int_val(var)));
}

/* ML type: precision -> bvec -> bvec */
value mlbvec_coerce(value bits, value v) /* ML */
{
  return mlbdd_make_bvec(bvec_coerce(Int_val(bits), BVEC_val(v)));
}

/* ML type: bvec -> bool */
value mlbvec_isconst(value v) /* ML */
{
  return bvec_isconst(BVEC_val(v)) ? Val_true : Val_false;
}

/* ML type: bvec -> bool */
value mlbvec_getconst(value v) /* ML */
{
  if(bvec_isconst(BVEC_val(v))) {
    return Val_int(bvec_val(BVEC_val(v)));
  }
  else {
    RAISE_DOMAIN;
  }
}

/* ML type: bvec -> bvec -> bvec */
value mlbvec_add(value s1, value s2) /* ML */
{
  return mlbdd_make_bvec(bvec_add(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> bvec -> bvec */
value mlbvec_sub(value s1, value s2) /* ML */
{
  return mlbdd_make_bvec(bvec_sub(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> const -> bvec */
value mlbvec_mul(value s1, value con) /* ML */
{
  return mlbdd_make_bvec(bvec_mul(BVEC_val(s1), Int_val(con)));
}

/* ML type: bvec -> const -> bvec */
value mlbvec_divi(value s1, value con) /* ML */
{
  BVEC res, rem;
  bvec_div(BVEC_val(s1), Int_val(con), &res, &rem);
  return mlbdd_make_bvec(res);
}

/* ML type: bvec -> const -> bvec */
value mlbvec_modu(value s1, value con) /* ML */
{
  BVEC res, rem;
  bvec_div(BVEC_val(s1), Int_val(con), &res, &rem);
  return mlbdd_make_bvec(rem);
}

/* ML type: bvec -> const -> bdd -> bvec */
value mlbvec_shl(value s1, value c, value b) /* ML */
{
  return mlbdd_make_bvec(bvec_shl(BVEC_val(s1), Int_val(c), Bdd_val(b)));
}

/* ML type: bvec -> const -> bdd -> bvec */
value mlbvec_shr(value s1, value c, value b) /* ML */
{
  return mlbdd_make_bvec(bvec_shr(BVEC_val(s1), Int_val(c), Bdd_val(b)));
}

/* ML type: bvec -> bvec -> bdd */
value mlbvec_lth(value s1, value s2) /* ML */
{
  return mlbdd_make(bvec_lth(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> bvec -> bdd */
value mlbvec_lte(value s1, value s2) /* ML */
{
  return mlbdd_make(bvec_lte(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> bvec -> bdd */
value mlbvec_gth(value s1, value s2) /* ML */
{
  return mlbdd_make(bvec_gth(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> bvec -> bdd */
value mlbvec_gte(value s1, value s2) /* ML */
{
  return mlbdd_make(bvec_gte(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> bvec -> bdd */
value mlbvec_equ(value s1, value s2) /* ML */
{
  return mlbdd_make(bvec_equ(BVEC_val(s1), BVEC_val(s2)));
}

/* ML type: bvec -> bvec -> bdd */
value mlbvec_neq(value s1, value s2) /* ML */
{
  return mlbdd_make(bvec_neq(BVEC_val(s1), BVEC_val(s2)));
}
