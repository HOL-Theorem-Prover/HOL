/*========================================================================
                            ** BuDDy **
                      BINARY DECISION DIAGRAMS
                               with
                  FINITE DOMAIN VARIABLE INTERFACE
                      Library Package ver. 1.5
                        By Jorn Lind-Nielsen

            Copyright (C) 1996-1998 by Jorn Lind-Nielsen

    Permission is hereby granted to reproduce and distribute this
    package by any means and for any fee, whether alone or as part
    of a larger distribution, in source or in binary form, provided
    this notice is included with any such distribution and is visible 
    for the end user, and is not removed from any of its header files. 

      *** I AM NOT RESPONSIBLE FOR ANY KIND OF DAMAGE TO YOUR  ***
      *** FILES, DATA, HARDWARE, LOSS OF MONEY, SYSTEM CRASHES *** 
      *** OR ANY OTHER THING YOU MIGHT COME UP WITH.           ***
      *** - USE THIS PROGRAM OF YOUR OWN FREE WILL !!!         ***

      Happy Hacking
                   Jorn Lind-Nielsen

========================================================================*/

/*************************************************************************
  $Header$
  FILE:  reorder.c
  DESCR: BDD reordering functions
  AUTH:  Jorn Lind
  DATE:  (C) january 1998
*************************************************************************/
#include <stdlib.h>
#include <time.h>
#include <assert.h>
#include "kernel.h"
#include "bddtree.h"

   /* Store for the variable relationships */
static BddTree *vartree;

   /* Store for the ref.cou. of the external roots */
static int *extroots;
static int extrootsize;

   /* Converts var. level to first entry in the node-table for that level */
static int *levellookup;
static int levellookupsize;

   /* Reordering information for the user */
static int verbose;
static bdd2inthandler reorder_handler;
#define RV(a) if (verbose) a

   /* Kernel variables needed for reordering */
extern int bddfreepos;
extern int bddfreenum;
extern int bddproduced;

   /* Count everytime the node-table has been rehashed (for various reasons) */
static int rehashcou;

   /* New node hashing function for use with reordering */
#define NODEHASH(lvl,l,h) ((PAIR((l),(h))%levellookupsize) + levellookup[lvl])

   /* Reordering prototypes */
static void blockdown(BddTree *);
static void addref_rec(int);
static void decref_rec(int);
static void reorder_gbc(int);
static void local_gbc(int);
static int  reorder_makenode(int, int, int);
static void reorder_moveup(int);
static void reorder_movedown(int);
static void reorder_swap(int);
static int  reorder_varup(int);
static int  reorder_vardown(int);
static int  reorder_init(void);
static void reorder_done(void);



/*************************************************************************
  Reordering heuristics
*************************************************************************/

/*=== Reorder using a sliding window of size 2 =========================*/

static BddTree *reorder_win2(BddTree *t)
{
   BddTree *this=t, *first=t;

   if (t == NULL)
      return t;

   while (this->next != NULL)
   {
      int best = bdd_getnodenum();
      blockdown(this);
      
      if (best < bdd_getnodenum())
      {
	 blockdown(this->prev);
	 this = this->next;
      }
      else
      if (first == this)
	 first = this->prev;
   }
   
   RV(printf("Win2: %d nodes\n", bdd_getnodenum()));

   return first;
}


static BddTree *reorder_win2ite(BddTree *t)
{
   BddTree *this, *first=t;
   int lastsize;
   int c=0;
   
   if (t == NULL)
      return t;
   
   do
   {
      lastsize = bdd_getnodenum();
      
      this = t;
      while (this->next != NULL)
      {
	 int best = bdd_getnodenum();

	 blockdown(this);
	 if (best < bdd_getnodenum())
	 {
	    blockdown(this->prev);
	    this = this->next;
	 }
	 else
	 if (first == this)
	    first = this->prev;
      }
   
      RV(printf("Win2ite %d: %d nodes\n", c++, bdd_getnodenum()));
   }
   while ((bdd_getnodenum()*100)/lastsize < 95);

   return first;
}


/*=== Reorder by sifting =============================================*/

static void reorder_sift_bestpos(BddTree *blk)
{
   int best = bdd_getnodenum();
   int maxAllowed;
   int bestpos = 0;
   int first = 1;

   if (bddmaxnodesize > 0)
      maxAllowed = MIN(2*best, bddmaxnodesize-bddmaxnodeincrease-2);
   else
      maxAllowed = 2*best;
   
      /* Move blk up to top */
   while (blk->prev != NULL  &&  bdd_getnodenum() <= maxAllowed)
   {
      blockdown(blk->prev);
      bestpos--;

      if (verbose > 1)
      {
	 printf("-");
	 fflush(stdout);
      }
      
      if (bdd_getnodenum() < best)
      {
	 best = bdd_getnodenum();
	 bestpos = 0;
      }
   }

   if (bdd_getnodenum() > maxAllowed  &&  verbose > 1)
   {
      printf("!");
      fflush(stdout);
   }
   
      /* Move blk up to bottom */
   while (blk->next != NULL  &&  (bdd_getnodenum() <= maxAllowed  ||  first))
   {
      first = 0;
      blockdown(blk);
      bestpos++;

      if (verbose > 1)
      {
	 printf("+");
	 fflush(stdout);
      }
      
      if (bdd_getnodenum() < best)
      {
	 best = bdd_getnodenum();
	 bestpos = 0;
      }
   }

   if (bdd_getnodenum() > maxAllowed  &&  verbose > 1)
   {
      printf("!");
      fflush(stdout);
   }
   
      /* Move to best pos */
   while (bestpos < 0)
   {
      blockdown(blk);
      bestpos++;
   }
   while (bestpos > 0)
   {
      blockdown(blk->prev);
      bestpos--;
   }
}


static BddTree *reorder_sift(BddTree *t)
{
   BddTree *this;
   BddTree **seq;
   int n, num=0;
   
   if (t == NULL)
      return t;

   for (this=t ; this!=NULL ; this=this->next)
      num++;
   seq = (BddTree**)malloc(sizeof(BddTree*)*num);
   for (this=t,num=0 ; this!=NULL ; this=this->next)
      seq[num++] = this;

   for (n=0 ; n<num ; n++)
   {
      long c2, c1 = clock();
   
      if (verbose > 1)
	 printf("Sift %d: ", n);
      
      reorder_sift_bestpos(seq[n]);

      if (verbose > 1)
	 printf("\n> %d nodes", bdd_getnodenum());
      else
      if (verbose > 0)
	 RV(printf("Sifted block %d: %d nodes", n, bdd_getnodenum()));

      c2 = clock();
      printf(" (%.1f sec)\n", (float)(c2-c1)/CLOCKS_PER_SEC);
   }

      /* Find first block */
   for (this=t ; this->prev != NULL ; this=this->prev)
      /* nil */;

   free(seq);

   return this;
}


static BddTree *reorder_siftite(BddTree *t)
{
   BddTree *first=t;
   int lastsize;
   int c=0;
   
   if (t == NULL)
      return t;
   
   do
   {
      lastsize = bdd_getnodenum();
      RV(printf("Siftite %d:\n", c++));
      first = reorder_sift(first);
   }
   while ((bdd_getnodenum()*100)/lastsize < 95);

   return first;
}


/*=== Random reordering (mostly for debugging and test ) =============*/

static BddTree *reorder_random(BddTree *t)
{
   BddTree *this;
   BddTree **seq;
   int n, num=0;

   if (t == NULL)
      return t;
   
   for (this=t ; this!=NULL ; this=this->next)
      num++;
   seq = (BddTree**)malloc(sizeof(BddTree*)*num);
   for (this=t,num=0 ; this!=NULL ; this=this->next)
      seq[num++] = this;
   
   for (n=0 ; n<4*num ; n++)
   {
      int blk = rand() % num;
      if (seq[blk]->next != NULL)
	 blockdown(seq[blk]);
   }

      /* Find first block */
   for (this=t ; this->prev != NULL ; this=this->prev)
      /* nil */;

   free(seq);

   RV(printf("Random order: %d nodes\n", bdd_getnodenum()));
   return this;
}


/*************************************************************************
  Swapping blocks
*************************************************************************/

static void blockdown(BddTree *left)
{
   BddTree *right = left->next;
   int n;
   int leftsize = left->last - left->first;
   int rightsize = right->last - right->first;
   int leftstart = bddvar2level[left->first];

      /* Move left past right */
   while (bddvar2level[left->first] < bddvar2level[right->last])
   {
      for (n=0 ; n<leftsize ; n++)
      {
	 if (bddvar2level[left->first+n]+1   !=  bddvar2level[left->first+n+1]
	     && bddvar2level[left->first+n]   <  bddvar2level[right->last])
	 {
	    reorder_vardown(left->first+n);
	 }
      }

      if (bddvar2level[left->last] <  bddvar2level[right->last])
      {
	 reorder_vardown(left->last);
      }
   }

      /* Move right to where left started */
   while (bddvar2level[right->first] > leftstart)
   {
      for (n=rightsize ; n>0 ; n--)
      {
	 if (bddvar2level[right->first+n]-1 != bddvar2level[right->first+n-1]
	     && bddvar2level[right->first+n] > leftstart)
	 {
	    reorder_varup(right->first+n);
	 }
      }

      if (bddvar2level[right->first] > leftstart)
	 reorder_varup(right->first);
   }

      /* Swap left and right data in the order */
   left->next = right->next;
   right->prev = left->prev;
   left->prev = right;
   right->next = left;

   if (right->prev != NULL)
      right->prev->next = right;
   if (left->next != NULL)
      left->next->prev = left;
}


/*************************************************************************
  Kernel reordering routines
*************************************************************************/

/*=== Garbage collection for reordering ================================*/

static void decref_rec(int r)
{
   if (r < 2)
      return;

   DECREF(r);
   if (bddnodes[r].refcou == 0)
   {
      bddfreenum++;

      decref_rec(bddnodes[r].low);
      decref_rec(bddnodes[r].high);
   }
}


static void addref_rec(int r)
{
   if (r < 2)
      return;
   
   if (bddnodes[r].refcou == 0)
   {
      bddfreenum--;
      addref_rec(bddnodes[r].low);
      addref_rec(bddnodes[r].high);
   }
   INCREF(r);
}


static int mark_roots(void)
{
   int n;

   for (n=2,extrootsize=0 ; n<bddnodesize ; n++)
      if (bddnodes[n].refcou > 0)
      {
	 SETMARK(n);
	 extrootsize++;
      }

   if ((extroots=(int*)(malloc(sizeof(int)*extrootsize))) == NULL)
      return bdd_error(BDD_MEMORY);

   for (n=2,extrootsize=0 ; n<bddnodesize ; n++)
   {
      if (MARKED(n))
      {
	 UNMARK(n);
	 
	 extroots[extrootsize++] = n;
	 addref_rec(bddnodes[n].low);
	 addref_rec(bddnodes[n].high);
      }
   }

   bddnodes[0].hash = 0;
   bddnodes[1].hash = 0;
   
   return 0;
}


static void reorder_gbc(int dozero)
{
   int n;

   bddfreepos = 0;
   bddfreenum = 0;

   if (dozero)
      for (n=2 ; n<bddnodesize ; n++)
	 bddnodes[n].hash = 0;
   
   for (n=bddnodesize-1 ; n>=2 ; n--)
   {
      register BddNode *node = &bddnodes[n];

      if (node->refcou > 0)
      {
	 register unsigned int hash;

	 hash = NODEHASH(node->level & MARKHIDE, node->low, node->high);
	 node->next = bddnodes[hash].hash;
	 bddnodes[hash].hash = n;
      }
      else
      {
	 node->low = -1;
	 node->next = bddfreepos;
	 bddfreepos = n;
	 bddfreenum++;
      }
   }

   rehashcou++;
}


static void local_gbc(int level)
{
   int n;
   int ll0 = levellookup[level];
   
   for (n=0 ; n<levellookupsize ; n++)
   {
      register unsigned int hash = n+ll0;
      register int r = bddnodes[hash].hash;
      bddnodes[hash].hash = 0;

      while (r != 0)
      {
	 register BddNode *node = &bddnodes[r];
	 register int next = node->next;

	 UNMARKp(node);
	 
	 if (node->refcou > 0)
	 {
	    node->next = bddnodes[hash].hash;
	    bddnodes[hash].hash = r;
	 }
	 else
	 {
	    node->low = -1;
	    node->next = bddfreepos;
	    bddfreepos = r;
	 }

	 r = next;
      }
   }
}


/*=== Unique table handling for reordering =============================*/

static void rehash_all(void)
{
   int n;
   
   levellookupsize = bddnodesize / bddvarnum;
   for (n=0 ; n<bddvarnum ; n++)
      levellookup[n] = n*levellookupsize;

   reorder_gbc(0);
}


static int reorder_makenode(int level, int low, int high)
{
   register BddNode *node;
   register unsigned int hash;
   register int res;

      /* check whether childs are equal */
   if (low == high)
      return low;

      /* Try to find an existing node of this kind */
   hash = NODEHASH(level, low, high);
   res = bddnodes[hash].hash;
      
   while(res != 0)
   {
      if (bddnodes[res].low == low  &&  bddnodes[res].high == high)
	 return res;

      res = bddnodes[res].next;
   }
   
      /* No existing node -> build one */

      /* Any free nodes to use ? */
   if (bddfreepos == 0)
   {
      if (bdderrorcond)
	 return 0;
      
         /* Try to allocate more nodes */
      bdd_noderesize(rehash_all);
      hash = NODEHASH(level, low, high);
      
         /* Panic if that is not possible */
      if (bddfreepos == 0)
      {
	 bdderrorcond = abs(BDD_NODENUM);
	 return 0;
      }
   }

      /* Build new node */
   res = bddfreepos;
   bddfreepos = bddnodes[bddfreepos].next;
   bddproduced++;
   
   node = &bddnodes[res];
   node->level = level;
   node->low = low;
   node->high = high;

      /* Insert node */
   node->next = bddnodes[hash].hash;
   bddnodes[hash].hash = res;

   return res;
}


/*=== Swapping two adjacent variables ==================================*/

static void reorder_moveup(int level)
{
   register int n;
   int ll0 = levellookup[level-1];
   int ll1 = levellookup[level];
   
   for (n=0 ; n<levellookupsize ; n++)
   {
      unsigned int hash = n + ll0;
      register int r = bddnodes[n + ll1].hash;
      bddnodes[n + ll1].hash = 0;

      while (r != 0)
      {
	 register BddNode *node = &bddnodes[r];
	 register int next = node->next;

	 node->level--;
	 SETMARKp(node);
	 
	 node->next = bddnodes[hash].hash;
	 bddnodes[hash].hash = r;

	 r = next;
      }
   }
}


/* Move live nodes at level to level+1 (in some cases).
*/
static void reorder_movedown(int level)
{
   register int n;
   int level1 = level+1;
   int ll0 = levellookup[level];
   int ll1 = levellookup[level+1];
   
   for (n=0 ; n<levellookupsize ; n++)
   {
      register int r;

      r = bddnodes[n + ll0].hash;
      bddnodes[n + ll0].hash = 0;

      while (r != 0)
      {
	 register BddNode *node = &bddnodes[r];
	 register unsigned int hash = n +ll0;
	 register int next=node->next;
	 
	 if (!MARKEDp(node))
	 {
	    if ((bddnodes[node->low].level & MARKHIDE) > level1  &&
		(bddnodes[node->high].level & MARKHIDE) > level1)
	    {
	       node->level++;
	       hash = n + ll1;
	    }
	 }

	 node->next = bddnodes[hash].hash;
	 bddnodes[hash].hash = r;

	 r = next;
      }
   }
}


static void reorder_swap(int level)
{
   int prc;
   
   do
   {
      int n, ll0=levellookup[level];
      prc = rehashcou;
   
      for (n=0 ; n<levellookupsize && rehashcou==prc ; n++)
      {
	 register unsigned int hash;
	 register int r = bddnodes[n + ll0].hash;
	 bddnodes[n + ll0].hash = 0;
	 
	 while (r != 0  &&  rehashcou==prc)
	 {
	    register BddNode *node = &bddnodes[r];
	    register int next=node->next;
	    
	    if (node->refcou > 0  && !MARKEDp(node))
	    {
	       register f0 = node->low;
	       register f1 = node->high;
	       register f00, f01, f10, f11;
	       
	       if ((bddnodes[f0].level & MARKHIDE) == level)
	       {
		  f00 = bddnodes[f0].low;
		  f01 = bddnodes[f0].high;
	       }
	       else
		  f00 = f01 = f0;
	       
	       if ((bddnodes[f1].level & MARKHIDE) == level)
	       {
		  f10 = bddnodes[f1].low;
		  f11 = bddnodes[f1].high;
	       }
	       else
		  f10 = f11 = f1;
	       
	       addref_rec(f0 = reorder_makenode(level+1, f00, f10));
	       addref_rec(f1 = reorder_makenode(level+1, f01, f11));
	       node = &bddnodes[r];  /* Might change in makenode */
	       
	       decref_rec(node->low);
	       decref_rec(node->high);
	       
	       SETMARKp(node);
	       node->low = f0;
	       node->high = f1;
	    }

	    if (prc == rehashcou)
	    {
	       hash = NODEHASH(node->level & MARKHIDE, node->low, node->high);
	       node->next = bddnodes[hash].hash;
	       bddnodes[hash].hash = r;
	    }
	    
	    r = next;
	 }
      }
   }
   while (prc != rehashcou);
}


static int reorder_varup(int var)
{
   if (var < 0  ||  var >= bddvarnum)
      return bdd_error(BDD_VAR);
   if (bddvar2level[var] == 0)
      return 0;
   return reorder_vardown( bddlevel2var[bddvar2level[var]-1]);
}


static int reorder_vardown(int var)
{
   int level;
   int n;

   if (var < 0  ||  var >= bddvarnum)
      return bdd_error(BDD_VAR);
   if (bddvar2level[var] >= bddvarnum-1)
      return 0;

   level = bddvar2level[var];
   
      /* Update those in 'level+1' */
   reorder_moveup(level+1);
   
      /* Update those in 'level' with both childs.level>level+1 */
   reorder_movedown(level);
   
      /* Update the rest in 'level' */
   reorder_swap(level);
   
      /* Garbage collect and remove marks on this level */
   local_gbc(level);
   
      /* Swap the var<->level tables */
   n = bddlevel2var[level];
   bddlevel2var[level] = bddlevel2var[level+1];
   bddlevel2var[level+1] = n;

   n = bddvar2level[var];
   bddvar2level[var] = bddvar2level[ bddlevel2var[level] ];
   bddvar2level[ bddlevel2var[level] ] = n;

      /* Update all rename pairs */
   bdd_pairs_vardown(level);

   return 0;
}


/*************************************************************************
  User reordering interface
*************************************************************************/

void bdd_default_reohandler(int prestate, int n)
{
   static long c1;
   
   if (prestate)
   {
      printf("Start reordering (%d nodes)\n", n);
      c1 = clock();
   }
   else
   {
      long c2 = clock();
      printf("End reordering (%d nodes, %.1f sec)\n", n,
	     (float)(c2-c1)/CLOCKS_PER_SEC);
   }
}


void bdd_reorder_auto(void)
{
   if (bddreordermethod == BDD_REORDER_NONE  ||  vartree == NULL)
      return;
   
   if (reorder_handler != NULL)
      reorder_handler(1, bdd_getnodenum());

   bdd_reorder(bddreordermethod);

   if (reorder_handler != NULL)
      reorder_handler(0, bdd_getnodenum());
}


static int reorder_init(void)
{
   int n;

   if ((levellookup=(int*)(malloc(sizeof(int)*bddvarnum))) == NULL)
      return -1;
   levellookupsize = bddnodesize / bddvarnum;
   for (n=0 ; n<bddvarnum ; n++)
      levellookup[n] = n*levellookupsize;
   
   if (mark_roots() < 0)
      return -1;
   reorder_gbc(1);

   return 0;
}


static void reorder_done(void)
{
   int n;
   
   for (n=0 ; n<extrootsize ; n++)
      SETMARK(extroots[n]);
   for (n=2 ; n<bddnodesize ; n++)
   {
      if (MARKED(n))
	 UNMARK(n);
      else
	 bddnodes[n].refcou = 0;
   }
   
   free(extroots);
   free(levellookup);
   bdderrorcond = 0;
   bdd_gbc();
}


static BddTree *reorder_block(BddTree *t, int method)
{
   BddTree *this;
   
   if (t == NULL)
      return NULL;

   if (t->fixed == BDD_REORDER_FREE  &&  t->nextlevel!=NULL)
   {
      switch(method)
      {
      case BDD_REORDER_WIN2:
	 t->nextlevel = reorder_win2(t->nextlevel);
	 break;
      case BDD_REORDER_WIN2ITE:
	 t->nextlevel = reorder_win2ite(t->nextlevel);
	 break;
      case BDD_REORDER_SIFT:
	 t->nextlevel = reorder_sift(t->nextlevel);
	 break;
      case BDD_REORDER_SIFTITE:
	 t->nextlevel = reorder_siftite(t->nextlevel);
	 break;
      case BDD_REORDER_RANDOM:
	 t->nextlevel = reorder_random(t->nextlevel);
	 break;
      }
   }

   for (this=t->nextlevel ; this ; this=this->next)
      reorder_block(this, method);

   return t;
}



/*
NAME    {* bdd\_reorder *}
SECTION {* reorder *}
SHORT   {* start dynamic reordering *}
PROTO   {* void bdd_reorder(int method) *}
DESCR   {* This function initiates dynamic reordering using the heuristic
           defined by {\tt method}, which may be one of the following
	   \begin{description}
	     \item {\tt BDD\_REORDER\_WIN2}\\
	       Reordering using a sliding window of size 2. This algorithm
	       swaps two adjacent variable blocks and if this results in
	       more nodes then the two blocks are swapped back again.
	       Otherwise the result is kept in the variable order. This is
	       then repeated for all variable blocks.
	     \item {\tt BDD\_REORDER\_WIN2ITE}\\
	       The same as above but the process is repeated until no further
	       progress is done. Usually a fast and efficient method.
	     \item {\tt BDD\_REORDER\_SIFT}\\
	       Reordering where each block is moved through all possible
	       positions. The best of these is then used as the new position.
	       Potentially a very slow but good method.
	     \item {\tt BDD\_REORDER\_SIFTITE}\\
	       The same as above but the process is repeated until no further
	       progress is done. Can be extremely slow.
	     \item {\tt BDD\_REORDER\_RANDOM}\\
	       Mostly used for debugging purpose, but may be usefull for
	       others. Selects a random position for each variable.
	   \end{description}
	   *}
ALSO    {* bdd\_autoreorder, bdd\_reorder\_verbose, bdd\_addvarblock, bdd\_clrvarblocks *}
*/
void bdd_reorder(int method)
{
   BddTree *top;

   if ((top=bddtree_new()) == NULL)
      return;
   
   if (reorder_init() < 0)
      return;

   top->first = 0;
   top->last = bdd_varnum()-1;
   top->fixed = 0;
   top->next = NULL;
   top->nextlevel = vartree;

   reorder_block(top, method);
   vartree = top->nextlevel;
   free(top);
   
   reorder_done();
}


/*
NAME    {* bdd\_reorder\_hook *}
SECTION {* reorder *}
SHORT   {* sets a handler for automatic reorderings *}
PROTO   {* bdd2inthandler bdd_reorder_hook(bdd2inthandler handler) *}
DESCR   {* Whenever automatic reordering is done, a check is done to see
           if the user has supplied a handler for that event. If so then
	   it is called with the argument {\tt prestate} being 1 if the
	   handler is called immediately {\em before} reordering and
	   {\tt prestate} being 0 if it is called immediately after. The
	   argument {\tt n} holds the number of bdd nodes in use at the
	   time of calling the handler. The default handler is
	   {\tt bdd\_default\_reohandler} which will print information
	   about the reordering.

	   Any handler should look like this:
	   \begin{verbatim}
void my_reorder_handler(int prestate, int n)
{
   ...
}
\end{verbatim} *}
RETURN  {* The previous handler *}
ALSO    {* bdd\_reorder, bdd\_autoreorder, bdd\_resize\_hook *}
*/
bdd2inthandler bdd_reorder_hook(bdd2inthandler handler)
{
   bdd2inthandler tmp = reorder_handler;
   reorder_handler = handler;
   return tmp;
}


/*
NAME    {* bdd\_autoreorder *}
SECTION {* reorder *}
SHORT   {* enables automatic reordering *}
PROTO   {* int bdd_autoreorder(int method) *}
DESCR   {* Enables automatic reordering using {\tt method} as the reordering
           method. If {\tt method} is {\tt BDD\_REORDER\_NONE} then
           automatic reordering is disabled. Automatic
	   reordering is done every time the nodetable has been resized
	   {\em and} immediately after the conclusion of the bdd operation
	   that resulted in the resize. So this is some sort of "poor man's"
	   automatic reordering as it tries to solve the memory problem after
	   it was needed. *}
RETURN  {* Returns the old value of {\tt method} *}
ALSO    {* bdd\_reorder *}
*/
int bdd_autoreorder(int method)
{
   int tmp = bddreordermethod;
   bddreordermethod = method;
   return tmp;
}


/*
NAME    {* bdd\_reorder\_verbose *}
SECTION {* reorder *}
SHORT   {* enables verbose information about reorderings *}
PROTO   {* int bdd_reorder_verbose(int v) *}
DESCR   {* If {\tt v} is not zero then more information about the reordering
           is printed. If {\tt v} is zero then no information is printed. *}
RETURN  {* The old verbose value *}
ALSO    {* bdd\_reorder *}
*/
int bdd_reorder_verbose(int v)
{
   int tmp = verbose;
   verbose = v;
   return tmp;
}



/*
NAME    {* bdd\_clrvarblocks *}
SECTION {* reorder *}
SHORT   {* clears all variable blocks *}
PROTO   {* void bdd_clrvarblocks(void) *}
DESCR   {* Clears all the variable blocks that has been defined by calls
           to bdd\_addvarblock. *}
ALSO    {* bdd\_addvarblock *}
*/
void bdd_clrvarblocks(void)
{
   bddtree_del(vartree);
   vartree = NULL;
}


/*
NAME    {* bdd\_addvarblock *}
SECTION {* reorder *}
SHORT   {* adds a new variable block for reordering *}
PROTO   {* int bdd_addvarblock(BDD var, int fixed)
int bdd_intaddvarblock(int first, int last, int fixed) *}
DESCR   {* Creates a new variable block with the variables in the variable
           set {\tt var}. The variables in {\tt var} must be contiguous.
	   In the second form the argument {\tt first} is the first variable
	   included in the block and {\tt last} is the last variable included
	   in the block.

	   The variable blocks are ordered as a tree, with the largest
	   ranges at top and the smallest at the bottom. Example: Assume
	   the block 0-9 is added as the first block and then the block 0-6.
	   This yields the 0-9 block at the top, with the 0-6 block as a
	   child. If now the block 2-4 was added, it would become a child
	   of the 0-6 block. A block of 0-8 would be a child of the 0-9
	   block and have the 0-6 block as a child. Partially overlapping
	   blocks are not allowed.

	   The {\tt fixed}
	   parameter sets the block to be fixed (no reordering of its
	   childs is allowed) or free, using the constants
	   {\tt BDD\_REORDER\_FIXED} and {\tt BDD\_REORDER\_FREE}.

	   Reordering is always done on the top most blocks first and then
	   recursively downwards. *}
RETURN  {* Zero on success, otherwise a negative error code. *}
ALSO    {* fdd\_intaddvarblock, bdd\_clrvarblocks *}
*/
int bdd_addvarblock(BDD b, int fixed)
{
   BddTree *t;
   int n, *v, size;

   if ((n=bdd_scanset(b, &v, &size)) < 0)
      return n;
   if (size < 1)
      return bdd_error(BDD_VARBLK);
   
   for (n=1 ; n<size ; n++)
      if (bddvar2level[v[n-1]]+1 != bddvar2level[v[n]])
      {
	 free(v);
	 return bdd_error(BDD_VARSET);
      }

   if ((t=bddtree_addrange(vartree, v[0], v[size-1], fixed)) == NULL)
      return bdd_error(BDD_VARBLK);

   vartree = t;
   return 0;
}


int bdd_intaddvarblock(int first, int last, int fixed)
{
   BddTree *t;
   
   if ((t=bddtree_addrange(vartree, first, last, fixed)) == NULL)
      return bdd_error(BDD_VARBLK);

   vartree = t;
   return 0;
}


/*
NAME    {* bdd\_printorder *}
SECTION {* reorder *}
SHORT   {* prints the current order *}
PROTO   {* void bdd_printorder(void)
bdd_fprint_order(FILE *f)*}
DESCR   {* Prints an indented list of the variable blocks, showing the top
           most blocks to the left and the lower blocks to the right.
	   Example:\\
	   \begin{verbatim}
0
   0
      0
      2
      3
      6
   6
   7
   9
9
\end{verbatim}
           This shows 5 variable blocks. The top most is 0-9. This consists of
	   two blocks 0-6 and 7-9, where the first block again consists of
	   two blocks 0-2 and 3-6. *}
ALSO    {* bdd\_reorder, bdd\_addvarblock *}
*/
void bdd_printorder(void)
{
   bdd_fprintorder(stdout);
}


void bdd_fprintorder(FILE *ofile)  /*FIXME: also streams*/
{
   bddtree_print(ofile, vartree, 0);
}


/* EOF */
