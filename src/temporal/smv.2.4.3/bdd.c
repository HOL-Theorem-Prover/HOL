/********************************************************************
*                                                                   *
*     Copyright (C) 1990, Carnegie-Mellon University                *
*                                                                   *
*                                                                   *
*********************************************************************/

/* BDD routines */

#include <stdio.h>
#include <storage.h>
#include <bdd.h>
#include <node.h>

#define MIN_NODES 10000

extern int KEYTABLESIZE, APPLY_CACHE_SIZE, MINI_CACHE_SIZE;
extern int nstvars,real_nstvars;

static mgr_ptr bdd_mgr;
int evalcount, evalhitcount, evalcontrolcount;
int allocatecount, disposecount, garbagecollectcount;
static keytable_rec reduce_table;
static apply_rec *apply_cache;
static int apply_cache_size;

bdd_ptr ONE,ZERO;

int             primes[] = {
			    2,
			    3,
			    7,
			    13,
			    31,
			    61,
			    127,
			    251,
			    509,
			    1021,
			    2039,
			    4093,
			    8191,
			    16381,
			    32749,
			    65521,
			    126727,	/* 359 353	 */
			    262063,	/* 503 521	 */
			    522713,	/* 719 727	 */
			    1046429,	/* 1013 1033	 */
			    2090867,	/* 1439 1453	 */
			    4186067,	/* 2039 2053	 */
			    8363639,	/* 2887 2897	 */
			    16777207,	/* 4093 4099	 */
			    33489353,	/* 5791 5783	 */
			    670757739,	/* 8171 8209	 */
			    134168873,	/* 11579 11587	 */
			    268303439,	/* 16349 16411	 */
			    536848891,	/* 23167 23173	 */
			    1073217479,	/* 32749 32771	 */
			    /* 2146654199,	 46327 46337	 */
			    /* 4294442903,	 65521 65543	 */
			    /* 8588840951	 92671 92681	 */
};


/* Create a keytable. */
/* Keytable is the hash table which allows us
   to keep BDD in reduced form
   kp -> n is the size of the table
   kp -> elements_in_table is the total number
            of BDD nodes in all hash bins
   kp -> hash_table_buf points to an array
            of pointers to BDD nodes.
	    all pointers all initialized to NULL
*/
static void create_keytable(kp, n)
register keytable_ptr kp;
register int n;
{
   {  /* Adjust n to be a number in primes[]. */
      register int i;
      for (i = 1; *(primes + i) <= n; i++) ;
      n = *(primes + (i - 1));
   }

   /* Initialize a keytable. */
   kp->n = n;
   kp->elements_in_table = 0;
   kp->hash_table_buf = (bdd_ptr *)smv_malloc(n*sizeof(bdd_ptr));

   {  /* Initialize hash bin list pointers to NULL. */
      register int i;
      for (i = 0; i < n; i++) kp->hash_table_buf[i] = NULL;
   }
}

/* Initialize the BDD package.
   This creates the keytable and the apply cache.
   Size of the keytable is given by global KEYTABLESIZE
   Size of the apply cache is given by global APPLY_CACHE_SIZE
 */
void init_bdd()
{
   bdd_mgr = new_mgr(sizeof(struct bdd));
   evalcount     = evalhitcount        = evalcontrolcount = 0;
   allocatecount = garbagecollectcount = disposecount     = 0;

   /* Create key tables. */
   create_keytable(&reduce_table, KEYTABLESIZE);
   apply_cache_size = APPLY_CACHE_SIZE;
   apply_cache = (apply_rec *)smv_malloc(sizeof(apply_rec)*apply_cache_size);
   {
     int i;
     for(i=0;i<apply_cache_size;i++)apply_cache[i].op = 0;
   }
}


bdd_ptr leaf_bdd(n)
{
  return(find_bdd(LEAFLEVEL,n,0));
}

bdd_ptr atomic_bdd(n)
{
  return(find_bdd(THE_CURRENT_VAR(n),ZERO,ONE));
}


/* find_bdd returns a BDD node whose left
   pointer is to d1, right pointer is to d2,
   and whose level is "level".
   if such a node already exists, a pointer
   to this node is returned, else a
   new node is created. This routine is
   used to keep BDD's in reduced form.
   Note also, that if d1 == d2, this node
   is redundant, so we return d1.
*/

bdd_ptr find_bdd(level,d1,d2)
register bdd_ptr d1, d2;
register int level;
{
   register int hash_num;
   register bdd_ptr *q,p,d;
   if(d1==d2 && level != LEAFLEVEL)return(d1);
   /* here we use level, d1 and d2 to hash into
      the key table */
   hash_num =
      ((((unsigned)    d1)     )  +
       (((unsigned)    d2) << 1)  +
       (((unsigned) level) << 2)) % (unsigned)reduce_table.n;
   q = reduce_table.hash_table_buf + hash_num;
   /* q is a pointer to the element in the hash table */
   p = *q;
   /* p is a pointer to the first element of the list (or NULL) */
   /* search the list. if any node matches level,d1,d2, return it */
   while (p &&
	  (p->left != d1 ||
	   p->right != d2 ||
	   GETLEVEL(p) != level))p = p->next;
   if(p)return(p);
   /* otherwise, create a new node, and fill in the fields with
      level,d1,d2 */
   d = (bdd_ptr) new_rec(bdd_mgr);
   allocatecount++;
   d->left   = d1;
   d->right  = d2;
   d->dfield = 0;
   SETLEVEL(d, level);
   /* now make the new node the first element of the list */
   d->next = *q;
   *q = d;
   reduce_table.elements_in_table += 1;  /* update count of total nodes */
   return(d);
}


/* Sweep bdds in reduce table. */
/* Deletes any BDD nodes which do not have their
   mark field set */
void sweep_reduce()
{
   register bdd_ptr *p = reduce_table.hash_table_buf;
   register int n;
   for (n = reduce_table.n; n>0; n--, p++) {
      register bdd_ptr *q = p;
      while (*q) {
         if (TESTMARK(*q)) { CLEARMARK(*q); q = &((*q)->next); }
         else {
	   free_rec(bdd_mgr,*q);
	   *q = (*q)->next;
	   disposecount++;
	   reduce_table.elements_in_table--;
	 }
       }
    }
 }




#define OP_MASK   0x7fffffff
#define SAVE_MASK 0x80000000

void save_apply(op,d1,d2)
int op;
register bdd_ptr d1,d2;
{
  register apply_rec *a = apply_cache +
     (((unsigned) d1) + ((unsigned) d2 << 1) + ((unsigned) op << 2))
       % apply_cache_size;
  if(a->arg1 == d1 && a->arg2 == d2 && (a->op & OP_MASK) == op)
    a->op |= SAVE_MASK;
}

/* Insert an apply record into the apply cache */
/* op is the op code (see bdd.h)
   d1 is the first argument
   d2 is the second argument
   d is the result */
/* opcodes below USE_BIG_CACHE use only the portion
   of the hash table below MINI_CACHE_SIZE (set by
   command line option) (USE_BIG_CACHE defined in bdd.h)
*/
void insert_apply(op,d1,d2,d)
int op;
register bdd_ptr d1,d2,d;
{
  register apply_rec *a = apply_cache +
     (((unsigned) d1) + (((unsigned) d2) << 1) + ((unsigned) op << 2))
       % ((op < USE_BIG_CACHE) ? MINI_CACHE_SIZE : apply_cache_size);
  if(!(a->op & SAVE_MASK)){
    a->op = op;
    a->arg1 = d1;
    a->arg2 = d2;
    a->res = d;
  }
}

/* Find an apply record in the apply cache */
/* op is the op code (see bdd.h)
   d1 is the first argument
   d2 is the second argument
   returns the result of the op if it is
   in the cache, else returns NULL
   (see insert_apply) */
bdd_ptr find_apply(op,d1,d2)
int op;
register bdd_ptr d1,d2;
{
  register apply_rec *a = apply_cache +
     (((unsigned) d1) + (((unsigned) d2) << 1) + ((unsigned) op << 2))
       % ((op < USE_BIG_CACHE) ? MINI_CACHE_SIZE : apply_cache_size);
  if(a->arg1 == d1 && a->arg2 == d2 && (a->op & OP_MASK) == op)
    return(a->res);
  else
    return(NULL);
}

/* empty the apply cache of all entries except
   those with SAVE bit set. This is in preparation
   for garbage collection. Call mark_bdd on all
   results with SAVE bit set to protect them
   from garbage collection */

void flush_apply()
{
  int i=apply_cache_size;
  apply_rec *a=apply_cache;
  while(i--){
    if(a->op & SAVE_MASK)mark_bdd(a->res);
    else a->op = 0;
    a++;
    }
}


/* Repair (clear) mark field. */
void repairmark(d)
register bdd_ptr d;
{
  if(!TESTMARK(d))return;
  CLEARMARK(d);
  if (ISLEAF(d)) return;
  repairmark(d->left);
  repairmark(d->right);
}

/* Redo depth-first numbering of bdd. */
void renumber(d, pcount)
register bdd_ptr d;
register int* pcount;
{
  if(TESTMARK(d))return;
  SETMARK(d);
  SETID(d, (*pcount)++);
  if (ISLEAF(d)) return;
  renumber(d->left,  pcount);
  renumber(d->right, pcount);
}

/* Return number of nodes in bdd. */
int size_bdd(d)
register bdd_ptr d;
{
   int dsize = 0;
   renumber(d, &dsize);
   repairmark(d);
   return(dsize);
}


/* Redo depth-first marking of bdd. */
/* This routine is called to mark all
   nodes in a BDD to protect them from garbage
   collection */
void mark_bdd(d)
register bdd_ptr d;
{
  if(!d)catastrophe("mark_bdd: d == 0");
  if(TESTMARK(d))return;
  SETMARK(d);
  if(!ISLEAF(d)){
    mark_bdd(d->left);
    mark_bdd(d->right);
  }
}


bdd_ptr apply_bdd(f,a,b)
int (*f)();
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(ISLEAF(a) && ISLEAF(b))return(leaf_bdd(f(a->left,b->left)));
  if(temp1=find_apply(f,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,apply_bdd(f,a->left,b->left),
		   apply_bdd(f,a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,apply_bdd(f,a->left,b),apply_bdd(f,a->right,b));
  else temp1=find_bdd(blevel,apply_bdd(f,a,b->left),apply_bdd(f,a,b->right));
  insert_apply(f,a,b,temp1);
  return(temp1);
}

#define ELSE_LEAF ((bdd_ptr) -1)
bdd_ptr if_then_bdd(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(a==ZERO)return(leaf_bdd(ELSE_LEAF));
  if(a==ONE)return(b);
  if(ISLEAF(a))type_error(a->left);
  if(temp1=find_apply(if_then_bdd,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,if_then_bdd(a->left,b->left),
		   if_then_bdd(a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,if_then_bdd(a->left,b),if_then_bdd(a->right,b));
  else temp1=find_bdd(blevel,if_then_bdd(a,b->left),if_then_bdd(a,b->right));
  insert_apply(if_then_bdd,a,b,temp1);
  return(temp1);
}

bdd_ptr else_bdd(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(ISLEAF(a)){
    if(a->left != ELSE_LEAF)return(a);
    else return(b);
  }
  if(temp1=find_apply(else_bdd,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,else_bdd(a->left,b->left),
		   else_bdd(a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,else_bdd(a->left,b),else_bdd(a->right,b));
  else temp1=find_bdd(blevel,else_bdd(a,b->left),else_bdd(a,b->right));
  insert_apply(else_bdd,a,b,temp1);
  return(temp1);
}

bdd_ptr if_then_else_bdd(a,b,c)
bdd_ptr a,b,c;
{
  return(else_bdd(if_then_bdd(a,b),c));
}

/***************************************************************************\
*function: swapwords							    *
*									    *
*swaps words pointed to by args						    *
\***************************************************************************/
static swapwords(a,b)
bdd_ptr *a,*b;
{
  bdd_ptr temp= *a;
  *a= *b;
  *b=temp;
}


/***************************************************************************\
*function: andbr							    *
*									    *
*and two bdds								    *
\***************************************************************************/
bdd_ptr and_bdd(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  /* anything AND false is false */
  if(a==ZERO || b==ZERO)return(ZERO);
  /* anything AND true is itself */
  if(a==ONE)return(b);
  if(b==ONE)return(a);
  /* AND is commutative, so if address of a >
     address of b, swap the two. This increases
     chance of hit in the apply cache */
  if(ISLEAF(a))type_error(a->left);
  if(ISLEAF(b))type_error(b->left);
  if(a==b)return(a);
  if(((int)a)>((int)b))swapwords(&a,&b);
  /* Check to see if we've solved this problem before */
  if(temp1=find_apply(AND_OP,a,b))return(temp1);
  /* if not, get the level fields of a and b */
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  /* now break the AND problems into two subproblems */
  /* if levels are the same, do AND(a->left,b->left), AND(a->right,b->right) */
  if(alevel==blevel)
    temp1=find_bdd(alevel,and_bdd(a->left,b->left),and_bdd(a->right,b->right));
  /* else if level of a is higher, split on value of a's variable */
  else if(alevel<blevel)
    temp1=find_bdd(alevel,and_bdd(a->left,b),and_bdd(a->right,b));
  /* else (level of b is higher), split on value of b's variable */
  else temp1=find_bdd(blevel,and_bdd(a,b->left),and_bdd(a,b->right));
  /* now put result in apply cache */
  insert_apply(AND_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: orbr								    *
*									    *
*or two bdds								    *
\***************************************************************************/
bdd_ptr or_bdd(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(a==ONE || b==ONE)return(ONE);
  if(a==ZERO)return(b);
  if(b==ZERO)return(a);
  if(ISLEAF(a))type_error(a->left);
  if(ISLEAF(b))type_error(b->left);
  if(a==b)return(a);
  if(((int)a)>((int)b))swapwords(&a,&b);
  if(temp1=find_apply(OR_OP,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,or_bdd(a->left,b->left),or_bdd(a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,or_bdd(a->left,b),or_bdd(a->right,b));
  else temp1=find_bdd(blevel,or_bdd(a,b->left),or_bdd(a,b->right));
  insert_apply(OR_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: xorbr							    *
*									    *
*xor two bdds								    *
\***************************************************************************/
bdd_ptr xor_bdd(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(a==ONE && b==ONE)return(ZERO);
  if(a==ZERO)return(b);
  if(b==ZERO)return(a);
  if(a==b)return(ZERO);
  if(((int)a)>((int)b))swapwords(&a,&b);
  if(temp1=find_apply(XOR_OP,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel){
    if(ISLEAF(a) && a!=ONE && a!=ZERO)type_error(a->left);
    if(ISLEAF(b) && b!=ONE && b!=ZERO)type_error(b->left);
    temp1=find_bdd(alevel,xor_bdd(a->left,b->left),xor_bdd(a->right,b->right));
  }
  else if(alevel<blevel){
    if(ISLEAF(a))type_error(a->left);
    temp1=find_bdd(alevel,xor_bdd(a->left,b),xor_bdd(a->right,b));
  }
  else{
    if(ISLEAF(b))type_error(b->left);
    temp1=find_bdd(blevel,xor_bdd(a,b->left),xor_bdd(a,b->right));
  }
  insert_apply(XOR_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: notbr							    *
*									    *
* not a bdd 								    *
\***************************************************************************/
bdd_ptr not_bdd(d)
bdd_ptr d;
{
  return(xor_bdd(ONE,d));
}


/***************************************************************************\
*function: simplify_assuming						    *
*									    *
*								    *
\***************************************************************************/
/* simplify_assuming computes a/b such that
   a-b <= a/b <= a
   trying to minimize the BDD size of the result.
   damn if I know how it works.
*/
#define DONTCARE ((bdd_ptr)(-1))
bdd_ptr simplify_assuming1(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(b==ZERO)return(DONTCARE);
  if(b==ONE || a==ONE || a==ZERO)return(a);
  if(ISLEAF(a))type_error(a->left);
  if(ISLEAF(b))type_error(b->left);
  if(a==b)return(a);
  if(temp1=find_apply(SIMP_OP,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(!(alevel>blevel)){
    if(alevel<blevel){
      temp1=simplify_assuming1(a->left,b);
      temp2=simplify_assuming1(a->right,b);
    }
    else{
      temp1=simplify_assuming1(a->left,b->left);
      temp2=simplify_assuming1(a->right,b->right);
    }
    if(temp1==DONTCARE)temp1=temp2;
    else if(temp2!=DONTCARE)temp1=find_bdd(alevel,temp1,temp2);
  }
  else
    return(simplify_assuming1(a,or_bdd(b->left,b->right)));
  insert_apply(SIMP_OP,a,b,temp1);
  return(temp1);
}

bdd_ptr simplify_assuming(a,b)
bdd_ptr a,b;
{
  bdd_ptr res = simplify_assuming1(a,b);
  if(res == DONTCARE)return(ZERO);
  return(res);
}

/***************************************************************************\
*function: sat_bdd							    *
*									    *
*returns a bdd which is <= bdd d, but has at most one node at each level    *
\***************************************************************************/
/* This function is used in finding counterexamples
   It is intended to produce one element of a set which is
   represented by the BDD d. */

bdd_ptr sat_bdd_aux(d,l)
bdd_ptr d;
int l;
{
  bdd_ptr temp1,temp2;
  int mylevel,l1 = THE_CURRENT_VAR(l);
  if(d == ZERO)return(d);
  if(l > nstvars)return(ONE);
  mylevel=GETLEVEL(d);
  if(l1 == mylevel){
    if(d->left != ZERO)return(find_bdd(mylevel,
				       sat_bdd_aux(d->left,l+1),
				       ZERO));
    return(find_bdd(mylevel,
		    ZERO,
		    sat_bdd_aux(d->right,l+1)));
  }
  if(l1 < mylevel)
    return(find_bdd(l1,sat_bdd_aux(d,l+1),ZERO));
  if(d->left != ZERO)return(sat_bdd_aux(d->left,l));
  return(sat_bdd_aux(d->right,l));
}

bdd_ptr sat_bdd(d)
bdd_ptr d;
{
  /*
   * Calling sat_bdd_aux with nstbase+1 eliminates the process
   * selection variables from the resulting bdd.  As a result, the
   * error trace cannot tell which process is executing.
   *
   * It was restored by steed.
   */
#if 0
  extern int nstbase;
  return(sat_bdd_aux(d,nstbase+1));
#else
  return(sat_bdd_aux(d,1));
#endif
}

/*
 * forsome(a,b)
 *
 */

bdd_ptr forsome(a,b)
bdd_ptr a,b;
{
  if(a == ONE || b == ONE || b == ZERO)return(b);
  if(a == ZERO)catastrophe("forsome: a == ZERO");
  {
    register bdd_ptr result = find_apply(FORSOME_OP,a,b);
    if(result)return(result);
    {
      register int alevel = GETLEVEL(a);
      register int blevel = GETLEVEL(b);
      if(alevel < blevel)
	result = forsome(a->right,b);
      else if(alevel == blevel)
	result = or_bdd(forsome(a->right,b->left),forsome(a->right,b->right));
      else
	result = find_bdd(blevel,forsome(a,b->left),forsome(a,b->right));
    }
    insert_apply(FORSOME_OP,a,b,result);
    return(result);
  }
}

bdd_ptr forall(a,b)
bdd_ptr a,b;
{
  if(a == ONE || b == ONE || b == ZERO)return(b);
  if(a == ZERO)catastrophe("forall: a == ZERO");
  {
    register bdd_ptr result = find_apply(forall,a,b);
    if(result)return(result);
    {
      register int alevel = GETLEVEL(a);
      register int blevel = GETLEVEL(b);
      if(alevel < blevel)
	result = forall(a->right,b);
      else if(alevel == blevel)
	result = and_bdd(forall(a->right,b->left),forall(a->right,b->right));
      else
	result = find_bdd(blevel,forall(a,b->left),forall(a,b->right));
    }
    insert_apply(forall,a,b,result);
    return(result);
  }
}

static bdd_ptr the_support;
static void support1(d)
bdd_ptr d;
{
  if(TESTMARK(d))return;
  SETMARK(d);
  if(ISLEAF(d))return;
  support1(d->left); support1(d->right);
  the_support = and_bdd(the_support,find_bdd(GETLEVEL(d),ZERO,ONE));
  return;
}

bdd_ptr support_bdd(d)
bdd_ptr d;
{
  the_support = ONE;
  support1(d);
  repairmark(d);
  return(the_support);
}

/***************************************************************************\
*function: count_bdd							    *
*									    *
*return as a float the number of states that satisfy a given bdd.           *
* assumes global nstates contains the total number of states                *
\***************************************************************************/
extern double nstates;

/* this routine returns the *fraction* of truth assignments
   satisfying the BDD d. If the BDD is TRUE, it returns 1.0.
   If the BDD is FALSE, it returns 0.0. Otherwise it returns
   0.5 * {fraction of assignments satisfying left branch} +
   0.5 * {fraction of assignments satisfying left branch}.
   This routine is used only for the user's amusement. */

static double auxcount_bdd(d)
bdd_ptr d;
{
  union {float a; bdd_ptr b;} temp;     /* very dangerous!!! */
  if(d==ZERO)return(0.0);
  if(d==ONE)return(1.0);
  temp.b = find_apply(COUNT_OP,d,ZERO);
  if(temp.b)return(temp.a);
  temp.a = 0.5*auxcount_bdd(d->left)+0.5*auxcount_bdd(d->right);
  insert_apply(COUNT_OP,d,ZERO,temp.b);
  return(temp.a);
}

double n_count_bdd(d,n)
bdd_ptr d;
int n;
{
  double floor();
  double pow();
  if(sizeof(float) > sizeof(bdd_ptr))
    catastrophe("count_bdd: sizeof(float) > sizeof(bdd_ptr)");
  return(floor(pow(2.0,(double)n) * (double)auxcount_bdd(d)));
}

double count_bdd(d)
bdd_ptr d;
{
  return(n_count_bdd(d,real_nstvars));
}

static node_ptr save_bdd_list=NIL;  /* list of bdds in use */
static int maxnodes=MIN_NODES;		/* garb collect threshold */
static int save_bdd_list_length = 0;

/* these routines (save_bdd and release_bdd) are used to keep a
   linked list of the top level nodes of all BDD's that are
   still in use. If you have a BDD pointer which is still in
   use, and is not on this list, it may get garbage collected
   during certain operations (any routines which call mygarbage).
   Note that there may be several occurrences on the list of
   any given node. Save_bdd always adds one occurrence, and
   release_bdd always deletes one. Save_bdd returns its argument */

bdd_ptr save_bdd(d)
bdd_ptr d;
{
  save_bdd_list_length++;
  save_bdd_list=cons(d,save_bdd_list);
  return(d);
}


static struct node *rbdd_rec(bddlist,d)
struct node *bddlist;
bdd_ptr d;
{
  if(bddlist==NIL)catastrophe("release_bdd: not on list");
  if(bddlist->left.bddtype!=d){
	bddlist->right.nodetype=rbdd_rec(bddlist->right.nodetype,d);
	return(bddlist);
  }
  else{
    struct node *temp=bddlist->right.nodetype;
    free_node(bddlist);
    return(temp);
  }
}

void release_bdd(d)
bdd_ptr d;
{
  save_bdd_list=rbdd_rec(save_bdd_list,d);
  save_bdd_list_length--;
}

static markbddlist(bddlist)
struct node *bddlist;
{
  if(bddlist==NIL)return;
  mark_bdd(bddlist->left.bddtype);
  markbddlist(bddlist->right.nodetype);
}

check_bdd(d)
bdd_ptr d;
{
  node_ptr p = save_bdd_list;
  while(p){
    if(((bdd_ptr)car(p)) == d)return;
    p = cdr(p);
  }
  catastrophe("check_bdd: failed");
}


static force_garbage()
{
  extern int verbose;
  flush_apply();
  markbddlist(save_bdd_list);
  sweep_reduce();
  maxnodes=(allocatecount-disposecount)*2;
  if(maxnodes < MIN_NODES)maxnodes = MIN_NODES;
  if(verbose)pr_status();
}

static int bdd_nodes_allocated;
int get_bdd_nodes_allocated()
{
  if(allocatecount-disposecount > bdd_nodes_allocated)
      bdd_nodes_allocated = allocatecount-disposecount;
  return(bdd_nodes_allocated);
}

mygarbage()
{
  if((allocatecount-disposecount) >= maxnodes){
    if(allocatecount-disposecount > bdd_nodes_allocated)
      bdd_nodes_allocated = allocatecount-disposecount;
    force_garbage();
  }
}

restart_bdd()
{
  save_bdd_list = NIL;
  save_bdd(ZERO);
  save_bdd(ONE);
  force_garbage();
}

pr_status()
{
  fprintf(stderr,"nodes allocated: %d\n",allocatecount-disposecount);
}


bdd_ptr r_collapse_save(a,b)
bdd_ptr a,b;
{
  bdd_ptr r = r_collapse(a,b);
  save_apply(NEXT_OP,a,b);
  return(r);
}

#define OR_BEFORE_RECURSE
/***************************************************************************\
*function: r_collapse							    *
*									    *
* collapse a bdd in reverse						    *
\***************************************************************************/
bdd_ptr r_collapse(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE)return(ONE);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(temp1=find_apply(NEXT_OP,a,b))return(temp1);
  if(alevel<blevel){
    if(IS_CURRENT_VAR(alevel)) temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(r_collapse(a->left,b),r_collapse(a->right,b));
#else
      r_collapse(or_bdd(a->left,a->right),b);
#endif
    else temp1=find_bdd(NEXT_TO_CURRENT(alevel),
			r_collapse(a->left,b),r_collapse(a->right,b));
  }
  else if(alevel==blevel){
    if(IS_CURRENT_VAR(alevel))temp1=
      or_bdd(r_collapse(a->left,b->left),r_collapse(a->right,b->right));
    else
      catastrophe("r_collapse: !IS_CURRENT_VAR(blevel)");
  }
  else {
    if(IS_CURRENT_VAR(blevel))temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(r_collapse(a,b->left),r_collapse(a,b->right));
#else
      r_collapse(a,or_bdd(b->left,b->right));
#endif
    else
      catastrophe("r_collapse: !IS_CURRENT_VAR(blevel)");
  }
  insert_apply(NEXT_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: r_shift							    *
*									    *
* shift a bdd from current vars to next vars				    *
\***************************************************************************/
bdd_ptr r_shift(a)
bdd_ptr a;
{
  int alevel;
  bdd_ptr temp1,temp2;
  if(ISLEAF(a))return(a);
  if(temp1=find_apply(r_shift,a,0))return(temp1);
  alevel = GETLEVEL(a);
  if(IS_CURRENT_VAR(alevel)){
    temp1 = find_bdd(CURRENT_TO_NEXT(alevel),
		     r_shift(a->left),r_shift(a->right));
    insert_apply(r_shift,a,0,temp1);
    return(temp1);
  }
  else
    catastrophe("r_shift: !IS_CURRENT_VAR(alevel)");
}

/***************************************************************************\
*function: f_shift							    *
*									    *
* shift a bdd from current vars to next vars				    *
\***************************************************************************/
bdd_ptr f_shift(a)
bdd_ptr a;
{
  int alevel;
  bdd_ptr temp1,temp2;
  if(ISLEAF(a))return(a);
  if(temp1=find_apply(f_shift,a,0))return(temp1);
  alevel = GETLEVEL(a);
  if(!IS_CURRENT_VAR(alevel)){
    temp1 = find_bdd(NEXT_TO_CURRENT(alevel),
		     f_shift(a->left),f_shift(a->right));
    insert_apply(f_shift,a,0,temp1);
    return(temp1);
  }
  else
    catastrophe("f_shift: IS_CURRENT_VAR(alevel)");
}


/***************************************************************************\
*function: collapse							    *
*									    *
* collapse a bdd, elimating all odd level forks 			    *
\***************************************************************************/
bdd_ptr collapse(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE)return(ONE);
  alevel=GETLEVEL(a);
  blevel=(GETLEVEL(b));
  if(IS_CURRENT_VAR(blevel))blevel=CURRENT_TO_NEXT(blevel);
  if(temp1=find_apply(PREV_OP,a,b))return(temp1);
  if(alevel<blevel){
    if(IS_NEXT_VAR(alevel)) temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(collapse(a->left,b),collapse(a->right,b));
#else
      collapse(or_bdd(a->left,a->right),b);
#endif
    else temp1=find_bdd(alevel,collapse(a->left,b),collapse(a->right,b));
  }
  else if(alevel==blevel){
    if(IS_NEXT_VAR(alevel))temp1=
      or_bdd(collapse(a->left,b->left),collapse(a->right,b->right));
    else
      catastrophe("collapse: !IS_NEXT_VAR(blevel)");
  }
  else {
    if(IS_NEXT_VAR(blevel))temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(collapse(a,b->left),collapse(a,b->right));
#else
      collapse(a,or_bdd(b->left,b->right));
#endif
    else
      catastrophe("collapse: !IS_NEXT_VAR(blevel)");
  }
  insert_apply(PREV_OP,a,b,temp1);
  return(temp1);
}

bdd_ptr collapse_no_shift(a,b)
bdd_ptr a,b;
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE && b == ONE)return(ONE);
  if(temp1=find_apply(collapse_no_shift,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel<blevel){
    if(IS_NEXT_VAR(alevel)) temp1=
      collapse_no_shift(or_bdd(a->left,a->right),b);
    else temp1=find_bdd(alevel,
			collapse_no_shift(a->left,b),
			collapse_no_shift(a->right,b));
  }
  else if(alevel==blevel){
    if(IS_NEXT_VAR(alevel))temp1=
      or_bdd(collapse_no_shift(a->left,b->left),
	     collapse_no_shift(a->right,b->right));
    else temp1 = find_bdd(alevel,
			  collapse_no_shift(a->left,b->left),
			  collapse_no_shift(a->right,b->right));
  }
  else {
    if(IS_NEXT_VAR(blevel))temp1=
      collapse_no_shift(a,or_bdd(b->left,b->right));
    else temp1=find_bdd(blevel,
			collapse_no_shift(a,b->left),
			collapse_no_shift(a,b->right));
  }
  insert_apply(collapse_no_shift,a,b,temp1);
  return(temp1);
}

bdd_ptr collapse_vars(a,b,v)
bdd_ptr a,b,v;
{
  int alevel,blevel,vlevel;
  bdd_ptr temp1;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE && b == ONE)return(ONE);
  if(temp1=find_apply(collapse_vars,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  vlevel=GETLEVEL(v);
  while(vlevel < alevel && vlevel < blevel){
    v = v->right;
    vlevel=GETLEVEL(v);
  }
  if(alevel<blevel){
    if(alevel == vlevel) temp1=
      collapse_vars(or_bdd(a->left,a->right),b,v->right);
    else temp1=find_bdd(alevel,
			collapse_vars(a->left,b,v),
			collapse_vars(a->right,b,v));
  }
  else if(alevel==blevel){
    if(alevel == vlevel)temp1=
      or_bdd(collapse_vars(a->left,b->left,v->right),
	     collapse_vars(a->right,b->right,v->right));
    else temp1 = find_bdd(alevel,
			  collapse_vars(a->left,b->left,v),
			  collapse_vars(a->right,b->right,v));
  }
  else {
    if(blevel == vlevel)temp1=
      collapse_vars(a,or_bdd(b->left,b->right),v->right);
    else temp1=find_bdd(blevel,
			collapse_vars(a,b->left,v),
			collapse_vars(a,b->right,v));
  }
  insert_apply(collapse_vars,a,b,temp1);
  return(temp1);
}

int value_bdd(a)
bdd_ptr a;
{
  int temp;
  if(ISLEAF(a))return((int)(a->left));
  temp = value_bdd(a->left);
  if(temp == (int)ELSE_LEAF) temp = value_bdd(a->right);
  return(temp);
}


static node_ptr wl_bdd(f,d)
void (*f)();
bdd_ptr d;
{
  if(TESTMARK(d))return(NIL);
  SETMARK(d);
  if(ISLEAF(d))f((node_ptr)(d->left));
  else{
    wl_bdd(f,d->left);
    wl_bdd(f,d->right);
  }
}

void walk_leaves(f,d)
void (*f)();
bdd_ptr d;
{
  wl_bdd(f,d);
  repairmark(d);
  return;
}



static int aux_lowest_var_bdd(d,n)
bdd_ptr d;
int n;
{
  int i;
  if(TESTMARK(d) || ISLEAF(d))return(n);
  SETMARK(d);
  i = VAR_NUM(GETLEVEL(d));
  if(i > n)n = i;
  return(aux_lowest_var_bdd(d->right,aux_lowest_var_bdd(d->left,n)));
}

int lowest_var_bdd(d)
bdd_ptr d;
{
  int res = aux_lowest_var_bdd(d,0);
  repairmark(d);
  return(res);
}

static bdd_ptr aux_make_var_mask(d,n,l)
bdd_ptr d;
int n,l;
{
  if(l > n)return(ONE);
  if(ISLEAF(d))
    return(find_bdd(THE_CURRENT_VAR(l),aux_make_var_mask(d,n,l+1),ZERO));
  l = VAR_NUM(GETLEVEL(d));
  return(find_bdd(THE_CURRENT_VAR(l),
		  aux_make_var_mask(d->left,n,l+1),
		  aux_make_var_mask(d->right,n,l+1)));
}

int bits_encoding_var;
bdd_ptr make_var_mask(d)
bdd_ptr d;
{
  int i = lowest_var_bdd(d);
  int j = ISLEAF(d)?1:VAR_NUM(GETLEVEL(d));
  bits_encoding_var = i - j + 1;
  return(aux_make_var_mask(d,i,j));
}

bdd_ptr varset_diff(a,b)
bdd_ptr a,b;
{
  if(a == ZERO || b == ZERO)catastrophe("varset_diff: a == ZERO || b == ZERO");
  if(a == ONE)return(a);
  if(GETLEVEL(a)<GETLEVEL(b))return(find_bdd(GETLEVEL(a),ZERO,varset_diff(a->right,b)));
  if(GETLEVEL(a)==GETLEVEL(b))return(varset_diff(a->right,b->right));
  return(varset_diff(a,b->right));
}

int check_bdd_order_aux(d)
bdd_ptr d;
{
  if(TESTMARK(d))return(GETLEVEL(d));
  SETMARK(d);
  if(!ISLEAF(d)){
    int a = check_bdd_order_aux(d->left);
    int b = check_bdd_order_aux(d->right);
    if(GETLEVEL(d) >= a || GETLEVEL(d) >= b)catastrophe("bdd vars out of order");
  }
  return(GETLEVEL(d));
}

void check_bdd_order(d)
bdd_ptr d;
{
  check_bdd_order_aux(d);
  repairmark(d);
}

void check_bdd_free_list()
{
  rec_ptr l = (bdd_mgr->free.link);
  int i = 0;
  while(l){
    rec_ptr m;
    if(l->link)m = l->link->link;
    l = l->link;
  }
}
