#include <stdlib.h>
#include <stdio.h>
/* ROBDD stuff */
#include <bdd.h>

/* mosml stuff */
#include <mlvalues.h> 
#include <fail.h>
#include <alloc.h>
#include <memory.h>


/* Reduced Ordered Binary Decision Diagrams: interface to
   Jørn Linds <jl@it.dtu.dk> BuDDy library.
   Made by Ken Larsen <kla@it.dtu.dk>

   The type Robdd.robdd of a Reduced Ordered Binary Decision Diagram
   is an abstract type; really an BDD structure.  This will contain an
   integer which is a root number.  The root number cannot just be
   treated as an ordinary int for two reasons:
   
   1. The gc cannot understand the root number (it would be confused
      by the untagged integer field)

   2. The (camlrunm) gc don't know how to garbage collect a robdd 
      (call bdd_delref from the bdd lib.)
   
   This raises the question how to deallocate the robdd structure when
   it is no longer reachable.  One possibility is to use finalized
   objects, calling the delref function explicitly whenever an robdd
   value is about to be garbage-collected by the camlrunm runtime.

   An robdd should be a finalized object: a pair, 

              header with Final_tag
	      0: finalization function mlrobdd_finalize
	      1: the robdd's root number

   whose component 0 is a pointer to the finalizing function
   mlrobdd_finalize, and whose component 1 is a root number.  The
   finalization function should apply bdd_delref to the second
   component of the pair: */


/* A nice macro to have */
#define Robdd_val(x) (Field(x, 1))

/* I don't want to ajust the GC so I've made my own alloc_final,
   stolen from alloc.c
*/
value mlrobdd_alloc_final(mlsize_t len, final_fun fun)
{
  value result;
  result = alloc_shr(len, Final_tag);
  Field (result, 0) = (value) fun;
  return result;
} 

/* Sometimes it is nice to raise the Domain exception
 */
#define RAISE_DOMAIN mlraise(Atom(SMLEXN_DOMAIN))

/* for buddy < 1.4
extern const char *bdd_errstring(int);
extern int      bdd_var(BDD);
extern BDD      bdd_low(BDD);
extern BDD      bdd_high(BDD);

#define bddPair BddPair
#define bddStat BddStat 
*/

void mlrobdd_errorhandler(int errorcode) 
{
  failwith(bdd_errstring(errorcode));
} 


void mlrobdd_postgc()
{
  printf("...........\n");
}

/* ML type: int -> int -> unit */
value mlrobdd_bdd_init(value nodes, value cachesize) /* ML */
{
  /* setup the our error handler */
  
  bdd_error_hook(&mlrobdd_errorhandler);
  bdd_init(Int_val(nodes), Int_val(cachesize));
  bdd_error_hook(&mlrobdd_errorhandler);
  bdd_gbc_hook(NULL);
  return Val_unit;    
}

/* ML type: unit -> unit */
value mlrobdd_bdd_done(value nill) /* ML */
{
  bdd_done();
  return Val_unit;
}

/* ML type: unit -> bool */
value mlrobdd_bdd_isrunning(value nill) /* ML */
{
  return bdd_isrunning() ? Val_true : Val_false;
}

/* ML type: int -> unit */
value mlrobdd_setvarnum(value n) /* ML */
{ 
  
  bdd_setvarnum(Int_val(n));
  return Val_unit;
}


/* When the robdd becomes unreachable from the ML process, it will be
   garbage-collected, mlrobdd_finalize() will be called on the robdd,
   which will do the necessary bdd-bookkeeping.  */
void mlrobdd_finalize(value obj) 
{
  /*  if(Robdd_val(obj) == 4781)  
    printf("del_ref: %d, low: %d\n", Robdd_val(obj), bdd_low(Robdd_val(obj)));
    */
  bdd_delref(Robdd_val(obj));
  if(Robdd_val(obj) == 4781)  
    printf("2del_ref: %d, low: %d\n", Robdd_val(obj), bdd_low(Robdd_val(obj)));
}

/* Creation of a robdd makes a finalized pair (mlrobdd_finalize, root) as
   described above. */
value mlrobdd_make(BDD root) 
{
  value res;
  bdd_addref(root);
  if(root == 4781) printf("addref: %d\n", root);
  res = mlrobdd_alloc_final(2, &mlrobdd_finalize);
  Robdd_val(res) = root;  /* Hopefully a BDD fits in a long */
  return res;
}

/* FOR INTERNAL USAGE */
/* ML type: robdd -> int */
value mlrobdd_root(value r) /* ML */
{
  return Val_int(Robdd_val(r));
}

/* ML type: int -> robdd */
value mlrobdd_bdd_ithvar(value i) /* ML */
{ 
  return mlrobdd_make(bdd_ithvar(Int_val(i)));
}

/* ML type: int -> robdd */
value mlrobdd_bdd_nithvar(value i) /* ML */
{ 
  return mlrobdd_make(bdd_nithvar(Int_val(i)));
}

/* ML type: bool -> robdd */
value mlrobdd_fromBool(value b) /* ML */
{
  return mlrobdd_make(Bool_val(b) ? bddtrue : bddfalse);
}

/* ML type: robdd -> bool */
value mlrobdd_toBool(value obj)    /* ML */
{
  BDD root;
  root = Robdd_val(obj);
  if(root == bddtrue)       return Val_true;
  else if(root == bddfalse) return Val_false;
  else RAISE_DOMAIN;
}

/* ML type: robdd -> varnum */
value mlrobdd_bdd_var(value r) /* ML */
{
  return Val_int(bdd_var(Robdd_val(r)));
}

/* ML type: robdd -> robdd */
value mlrobdd_bdd_low(value r) /* ML */
{
  return mlrobdd_make(bdd_low(Robdd_val(r)));
}

/* ML type: robdd -> robdd */
value mlrobdd_bdd_high(value r) /* ML */
{
  return mlrobdd_make(bdd_high(Robdd_val(r)));
}

/* Pass the opr constants from <bdd.h> to ML */ 
/* ML type: unit -> int * int * int * int * int * int * int * int * int *int */
value mlrobdd_constants(value unit)	/* ML */
{
  value res = alloc_tuple(10);
  Field(res, 0) = Val_long(bddop_and);
  Field(res, 1) = Val_long(bddop_xor);
  Field(res, 2) = Val_long(bddop_or);
  Field(res, 3) = Val_long(bddop_nand);
  Field(res, 4) = Val_long(bddop_nor);
  Field(res, 5) = Val_long(bddop_imp);
  Field(res, 6) = Val_long(bddop_biimp);
  Field(res, 7) = Val_long(bddop_diff);
  Field(res, 8) = Val_long(bddop_less);
  Field(res, 9) = Val_long(bddop_invimp);
  return res;
}


/* ML type: robdd -> robdd -> int -> robdd */
value mlrobdd_bdd_apply(value left, value right, value opr) /* ML */
{
  return mlrobdd_make(bdd_apply(Robdd_val(left),Robdd_val(right), 
				Int_val(opr)));
}

/* ML type: robdd -> robdd */
value mlrobdd_bdd_not(value r) /* ML */
{
  return mlrobdd_make(bdd_not(Robdd_val(r)));
}

/* ML type: robdd -> robdd -> bool */
value mlrobdd_equal(value left, value right) /* ML */
{
  return ((Robdd_val(left) == Robdd_val(right)) ? Val_true : Val_false);
}

/* ML type: robdd -> robdd -> robdd */
value mlrobdd_bdd_restrict(value r, value var) /* ML */
{
  return mlrobdd_make(bdd_restrict(Robdd_val(r),Robdd_val(var)));
}

/* ML type: robdd -> robdd -> int -> robdd */
value mlrobdd_bdd_compose(value f, value g, value var) /* ML */
{
  return mlrobdd_make(bdd_compose(Robdd_val(f),Robdd_val(g),Int_val(var)));
}



/* ML type: robdd -> robdd -> robdd */
value mlrobdd_bdd_simplify(value f, value d) /* ML */
{
  return mlrobdd_make(bdd_simplify(Robdd_val(f), Robdd_val(d)));
}

/* ML type: robdd -> unit */
value mlrobdd_bdd_printdot(value r) /* ML */
{
  bdd_printdot(Robdd_val(r));
  return Val_unit;
}

/* ML type: robdd -> unit */
value mlrobdd_bdd_printset(value r) /* ML */
{
  bdd_printset(Robdd_val(r));
  fflush(stdout);
  return Val_unit;
}

/* ML type: string -> robdd -> unit */
value mlrobdd_bdd_fnprintset(value filename, value r) /* ML */
{
  char *fname;
  FILE *ofile;
  fname = String_val(filename);
  ofile = fopen(fname, "w");
  if (ofile == NULL)
    failwith("Unable to open file");
  else {
    bdd_fprintset(ofile, Robdd_val(r));
    fclose(ofile);
  }
  return Val_unit;
}


/* ML type: string -> robdd -> unit */
value mlrobdd_bdd_fnprintdot(value filename, value r) /* ML */
{
  bdd_fnprintdot(String_val(filename), Robdd_val(r));
  return Val_unit;
}

/* ML type: unit -> unit */
value mlrobdd_bdd_printall(value nill) /* ML */
{
  bdd_printall();
  return nill;
}

/* ML type: unit -> int * int * int * int * int * int * int * int */
value mlrobdd_bdd_stats(value nill)
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

/* ML type: robdd -> real */ 
value mlrobdd_bdd_satcount(value r) /* ML */
{
  return copy_double(bdd_satcount(Robdd_val(r)));
}

/* ML type: robdd -> varSet */
value mlrobdd_bdd_satone(value r) /* ML */
{
  return mlrobdd_make(bdd_satone(Robdd_val(r)));
}

/* ML type: robdd -> int */ 
value mlrobdd_bdd_nodecount(value r) /* ML */
{
  return Val_int(bdd_nodecount(Robdd_val(r)));
}



/* Some helper functions for creating variable sets, these will be
   represented as BDD's on the C side but as a different type (varSet) on
   the ML side.
*/

/* ML type: int vector -> varSet */
value mlrobdd_makeset(value varvector) /* ML */
{
  int size, i, *v;
  value result;

  size = Wosize_val(varvector);

  /* we use stat_alloc which guarantee that we get the memory (or it
     will raise an exception). */
  v    = (int *) stat_alloc(sizeof(int) * size);
  for (i=0; i<size; i++) {
     v[i] = Int_val(Field(varvector, i));
  }

  /* we assume that vector is sorted on the ML side */
  result = mlrobdd_make(bdd_makeset(v, size));
 
  /* memory allocated with stat_alloc, should be freed with
     stat_free.*/
  stat_free((char *) v);

  return result;
}

/* ML type: varSet -> int vector */
value mlrobdd_scanset(value varset)
{
  value result;
  int *v, n, i;

  if(bdd_scanset(Robdd_val(varset), &v, &n))
    RAISE_DOMAIN;
  else {
    result = n < Max_young_wosize ? alloc(n, 0) : alloc_shr(n, 0);
    for (i = 0; i < n; i++) {
      Field(result, i) = Val_long(v[i]);
    }
    free(v);
  }
  return result;
}

/* ML type: robdd -> varSet -> robdd */
value mlrobdd_bdd_exist(value b1, value varset) /* ML */
{
  return mlrobdd_make(bdd_exist(Robdd_val(b1),Robdd_val(varset)));
}

/* ML type: robdd -> varSet -> robdd */
value mlrobdd_bdd_forall(value b1, value varset) /* ML */
{
  return mlrobdd_make(bdd_forall(Robdd_val(b1),Robdd_val(varset)));
}

/* ML type: robdd -> robdd -> int -> varSet -> robdd */
value mlrobdd_bdd_appall(value left, value right, 
			 value opr,  value varset) /* ML */
{
  return mlrobdd_make(bdd_appall(Robdd_val(left),Robdd_val(right), 
				 Int_val(opr), Robdd_val(varset)));
}

/* ML type: robdd -> robdd -> int -> varSet -> robdd */
value mlrobdd_bdd_appex(value left, value right, 
			value opr,  value varset) /* ML */
{
  return mlrobdd_make(bdd_appex(Robdd_val(left),Robdd_val(right), 
				 Int_val(opr), Robdd_val(varset)));
}


/* Some helper for making BddPairs, which on the ML side is called
   pairSet. pairSet is implemented very similar to robdd, i.e. as
   finalized objects. */

#define PairSet_val(x) ((bddPair *) Field(x, 1))


void mlrobdd_pair_finalize(value pairset)
{
  bdd_freepair(PairSet_val(pairset));
}

/* ML type: int vector -> int vector -> pairSet */
value mlrobdd_makepairset(value oldvar, value newvar) /* ML */
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

  result = mlrobdd_alloc_final(2, &mlrobdd_pair_finalize);
  PairSet_val(result) = (value) pairs;

  return result;
}

/* ML type: robdd -> pairSet -> robdd */
value mlrobdd_bdd_replace(value r, value pair) /* ML */
{
  return mlrobdd_make(bdd_replace(Robdd_val(r), PairSet_val(pair)));
}



