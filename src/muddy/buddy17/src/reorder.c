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
#include <math.h>
#include <assert.h>
#include "kernel.h"
#include "bddtree.h"

   /* Current auto reord. method and number of automatic reorderings left */
static int bddreordermethod;
static int bddreordertimes;

static int reorderdisabled;

   /* Store for the variable relationships */
static BddTree *vartree;
static int blockid;

   /* Store for the ref.cou. of the external roots */
static int *extroots;
static int extrootsize;

   /* Converts var. level to first entry in the node-table for that level */
static int *levellookup;
static int levellookupsize;

   /* Reordering information for the user */
static int verbose;
static bddinthandler reorder_handler;
static bddfilehandler reorder_filehandler;

static int usednum_before;
static int usednum_after;

#define RV(a) if (verbose) a

static bddsizehandler reorder_nodenum;
	    
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
static void decref(int);
static void addref(int);
static void addref_rec(int);
static void reorder_gbc(int);
static void local_gbc(int);
static int  reorder_makenode(int, int, int);
static void reorder_moveup(int);
static int  reorder_movedown(int);
static void reorder_swap(int);
static int  reorder_varup(int);
static int  reorder_vardown(int);
static int  reorder_init(void);
static void reorder_done(void);


#define random(a) (rand() % (a))

typedef struct s_sizePair
{
   int val;
   BddTree *block;
} sizePair;


/*************************************************************************
  Initialize and shutdown
*************************************************************************/

void bdd_reorder_init(void)
{
   rehashcou = 0;
   reorderdisabled = 0;
   vartree = NULL;
   
   bdd_clrvarblocks();
   bdd_reorder_hook(bdd_default_reohandler);
   bdd_reorder_verbose(0);
   bdd_autoreorder_times(BDD_REORDER_NONE, 0);
   reorder_nodenum = bdd_getnodenum;
   usednum_before = usednum_after = 0;
   blockid = 0;
}


void bdd_reorder_done(void)
{
   bddtree_del(vartree);
   vartree = NULL;
}


/*************************************************************************
  Reordering heuristics
*************************************************************************/

/*=== Reorder using a sliding window of size 2 =========================*/

static BddTree *reorder_win2(BddTree *t)
{
   BddTree *this=t, *first=t;

   if (t == NULL)
      return t;

   RV(printf("Win2 start: %d nodes\n", reorder_nodenum()));
   fflush(stdout);

   while (this->next != NULL)
   {
      int best = reorder_nodenum();
      blockdown(this);
      
      if (best < reorder_nodenum())
      {
	 blockdown(this->prev);
	 this = this->next;
      }
      else
      if (first == this)
	 first = this->prev;
   }
   
   RV(printf("Win2 end: %d nodes\n", reorder_nodenum()));
   fflush(stdout);

   return first;
}


static BddTree *reorder_win2ite(BddTree *t)
{
   BddTree *this, *first=t;
   int lastsize;
   int c=1;
   
   if (t == NULL)
      return t;
   
   RV(printf("Win2ite start: %d nodes\n", reorder_nodenum()));

   do
   {
      lastsize = reorder_nodenum();

      if (verbose > 1)
	 printf("Win2ite %d ", c);
      
      this = t;
      while (this->next != NULL)
      {
	 int best = reorder_nodenum();

	 blockdown(this);

	 if (best < reorder_nodenum())
	 {
	    blockdown(this->prev);
	    this = this->next;
	 }
	 else
	 if (first == this)
	    first = this->prev;
	 if (verbose > 1)
	 {
	    printf(".");
	    fflush(stdout);
	 }
      }

      if (verbose == 1)
	 printf("Win2ite %d: %d nodes\n", c, reorder_nodenum());
      else if (verbose > 1)
	 printf(" %d nodes\n", reorder_nodenum());
      c++;
   }
   while (reorder_nodenum() != lastsize);
   /*while ((reorder_nodenum()*100)/lastsize < 100);*/

   return first;
}


/*=== Reorder by sifting =============================================*/

/* Move a specific block up and down in the order and place at last in
   the best position
*/
static void reorder_sift_bestpos(BddTree *blk, int middlePos)
{
   int best = reorder_nodenum();
   int maxAllowed;
   int bestpos = 0;
   int dirIsUp = 1;
   int n;
   
#if 0
   if (bddmaxnodesize > 0)
      maxAllowed = MIN(best + 2*bddmaxnodeincrease,
		       bddmaxnodesize - bddmaxnodeincrease - 2);
   else
      maxAllowed = best + 2*bddmaxnodeincrease;
#elif 0
   if (bddmaxnodesize > 0)
      maxAllowed = MIN(2*best, bddmaxnodesize-bddmaxnodeincrease-2);
   else
      maxAllowed = 2*best;
#else
   if (bddmaxnodesize > 0)
      maxAllowed = MIN(best/5+best, bddmaxnodesize-bddmaxnodeincrease-2);
   else
      maxAllowed = best/5+best;
#endif

      /* Determine initial direction */
   if (blk->pos > middlePos)
      dirIsUp = 0;
   
      /* Move block back and forth */
   for (n=0 ; n<2 ; n++)
   {
      int first = 1;
      
      if (dirIsUp)
      {
	 while (blk->prev != NULL  &&
		(reorder_nodenum() <= maxAllowed || first))
	 {
	    first = 0;
	    blockdown(blk->prev);
	    bestpos--;
	    
	    if (verbose > 1)
	    {
	       printf("-");
	       fflush(stdout);
	    }
	    
	    if (reorder_nodenum() < best)
	    {
	       best = reorder_nodenum();
	       bestpos = 0;
	    }
	 }
      }
      else
      {
	 while (blk->next != NULL  &&
		(reorder_nodenum() <= maxAllowed  ||  first))
	 {
	    first = 0;
	    blockdown(blk);
	    bestpos++;
	    
	    if (verbose > 1)
	    {
	       printf("+");
	       fflush(stdout);
	    }
	    
	    if (reorder_nodenum() < best)
	    {
	       best = reorder_nodenum();
	       bestpos = 0;
	    }
	 }
      }
	 
      if (reorder_nodenum() > maxAllowed  &&  verbose > 1)
      {
	 printf("!");
	 fflush(stdout);
      }

      dirIsUp = !dirIsUp;
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


/* Go through all blocks in a specific sequence and find best
   position for each of them
*/
static BddTree *reorder_sift_seq(BddTree *t, BddTree **seq, int num)
{
   BddTree *this;
   int n;
   
   if (t == NULL)
      return t;

   for (n=0 ; n<num ; n++)
   {
      long c2, c1 = clock();
   
      if (verbose > 1)
      {
	 printf("Sift ");
	 if (reorder_filehandler)
	    reorder_filehandler(stdout, seq[n]->id);
	 else
	    printf("%d", seq[n]->id);
	 printf(": ");
      }
      
      reorder_sift_bestpos(seq[n], num);

      if (verbose > 1)
	 printf("\n> %d nodes", reorder_nodenum());
      else
      if (verbose > 0)
	 RV(printf("Sifted block %d: %d nodes", n, reorder_nodenum()));

      c2 = clock();
      if (verbose > 0)
	 printf(" (%.1f sec)\n", (float)(c2-c1)/CLOCKS_PER_SEC);
   }

      /* Find first block */
   for (this=t ; this->prev != NULL ; this=this->prev)
      /* nil */;

   return this;
}


/* Compare function for sorting sifting sequence
 */
static int siftTestCmp(const void *aa, const void *bb)
{
   const sizePair *a = (sizePair*)aa;
   const sizePair *b = (sizePair*)bb;

   if (a->val < b->val)
      return -1;
   if (a->val > b->val)
      return 1;
   return 0;
}

#if 1

/* Find sifting sequence based on the number of nodes at each level
 */
static BddTree *reorder_sift(BddTree *t)
{
   BddTree *this, **seq;
   sizePair *p;
   int n, num;
   int *levelcount;

   if ((levelcount=(NEW(int,bddvarnum))) == NULL)
      return t;

      /* Count number of nodes at each level */
   for (n=0 ; n<bddvarnum ; n++)
      levelcount[n] = 0;
   for (n=2 ; n<bddnodesize ; n++)
      if (bddnodes[n].refcou > 0)
	 levelcount[bddnodes[n].level]++;
   
   for (this=t,num=0 ; this!=NULL ; this=this->next)
      this->pos = num++;
   
   p = NEW(sizePair,num);
   seq = NEW(BddTree*,num);

   for (this=t,n=0 ; this!=NULL ; this=this->next,n++)
   {
      int v;

         /* Accumulate number of nodes for each block */
      p[n].val = 0;
      for (v=this->first ; v<=this->last ; v++)
	 p[n].val -= levelcount[bddvar2level[v]];
      /*printf("Blk %d -> %d\n", n, p[n].val);*/

      p[n].block = this;
   }

      /* Sort according to the number of nodes at each level */
   qsort(p, num, sizeof(sizePair), siftTestCmp);
   
      /* Create sequence */
   for (n=0 ; n<num ; n++)
      seq[n] = p[n].block;

      /* Do the sifting on this sequence */
   t = reorder_sift_seq(t, seq, num);
   
   free(seq);
   free(p);
   free(levelcount);
   
   return t;
}

#elif 1

/* Find sifting sequence based on a block swap probing
 */
static BddTree *reorder_sift(BddTree *t)
{
   BddTree *this, **seq;
   sizePair *p;
   int n, num;

   for (this=t,num=0 ; this!=NULL ; this=this->next)
      this->pos = num++;
   
   p = NEW(sizePair,num);
   seq = NEW(BddTree*,num);

   for (this=t,n=0 ; this!=NULL ; this=this->next,n++)
   {
         /* Try all blocks except for the last */
      if (this->next != NULL)
      {
	 int a,b;

	    /* Swap block down and up again and store change in
	       the number of nodes */
	 a = reorder_nodenum();
	 blockdown(this);
	 b = reorder_nodenum();
	 p[n].val = b-a;
	 blockdown(this->prev);
      }
      else
	 p[n].val = 0;

      p[n].block = this;
   }

      /* Sort according to the swap probe */
   qsort(p, num, sizeof(sizePair), siftTestCmp);

      /* Create sequence */
   for (n=0 ; n<num ; n++)
      seq[n] = p[n].block;

      /* Do the sifting on this sequence */
   t = reorder_sift_seq(t, seq, num);
   
   free(seq);
   free(p);
   
   return t;
}

#else


static BddTree *reorder_sift(BddTree *t)
{
   BddTree *this, **seq;
   int n, num;

   for (this=t,num=0 ; this!=NULL ; this=this->next)
      this->pos = num++;
   
   seq = NEW(BddTree*,num);

      /* Create sequence */
   for (this=t,n=0 ; this!=NULL ; this=this->next, n++)
      seq[n] = this;

      /* Do the sifting on this sequence */
   t = reorder_sift_seq(t, seq, num);
   
   free(seq);
   
   return t;
}

#endif

/* Do sifting iteratively until no more improvement can be found
 */
static BddTree *reorder_siftite(BddTree *t)
{
   BddTree *first=t;
   int lastsize;
   int c=1;
   
   if (t == NULL)
      return t;
   
   do
   {
      lastsize = reorder_nodenum();
      RV(printf("Siftite %d:\n", c++));
      first = reorder_sift(first);
   }
   while (reorder_nodenum() != lastsize);

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
   seq = NEW(BddTree*,num);
   for (this=t,num=0 ; this!=NULL ; this=this->next)
      seq[num++] = this;
   
   for (n=0 ; n<4*num ; n++)
   {
      int blk = random(num);
      if (seq[blk]->next != NULL)
	 blockdown(seq[blk]);
   }

      /* Find first block */
   for (this=t ; this->prev != NULL ; this=this->prev)
      /* nil */;

   free(seq);

   RV(printf("Random order: %d nodes\n", reorder_nodenum()));
   return this;
}


/*************************************************************************
  Swapping adjacent blocks
*************************************************************************/

#if 0
static void pp(BddTree *l, BddTree *r)
{
   int n;

   for (n=0 ; n<=l->last-l->first ; n++)
      if (n==0)
	 printf("%d/%d", l->seq[n], bddvar2level[l->seq[n]]);
      else
	 printf(":%d/%d", l->seq[n], bddvar2level[l->seq[n]]);

   printf(" ~ ");

   for (n=0 ; n<=r->last-r->first ; n++)
      if (n==0)
	 printf("%d/%d", r->seq[n], bddvar2level[r->seq[n]]);
      else
	 printf(":%d/%d", r->seq[n], bddvar2level[r->seq[n]]);

   printf("\n");
}
#endif

static void blockdown(BddTree *left)
{
   BddTree *right = left->next;
   int n;
   int leftsize = left->last - left->first;
   int rightsize = right->last - right->first;
   int leftstart = bddvar2level[left->seq[0]];
   int *lseq = left->seq;
   int *rseq = right->seq;

   /*printf("Swap 1#  ");   pp(left, right);*/
   
      /* Move left past right */
   while (bddvar2level[lseq[0]] < bddvar2level[rseq[rightsize]])
   {
      for (n=0 ; n<leftsize ; n++)
      {
	 if (bddvar2level[lseq[n]]+1  !=  bddvar2level[lseq[n+1]]
	     && bddvar2level[lseq[n]]  <  bddvar2level[rseq[rightsize]])
	 {
	    reorder_vardown(lseq[n]);
	 }
      }

      if (bddvar2level[lseq[leftsize]] <  bddvar2level[rseq[rightsize]])
      {
	 reorder_vardown(lseq[leftsize]);
      }
   }

      /* Move right to where left started */
   while (bddvar2level[rseq[0]] > leftstart)
   {
      for (n=rightsize ; n>0 ; n--)
      {
	 if (bddvar2level[rseq[n]]-1 != bddvar2level[rseq[n-1]]
	     && bddvar2level[rseq[n]] > leftstart)
	 {
	    reorder_varup(rseq[n]);
	 }
      }

      if (bddvar2level[rseq[0]] > leftstart)
	 reorder_varup(rseq[0]);
   }

   /*printf("Swap 2#  ");   pp(left, right);*/
   
      /* Swap left and right data in the order */
   left->next = right->next;
   right->prev = left->prev;
   left->prev = right;
   right->next = left;

   if (right->prev != NULL)
      right->prev->next = right;
   if (left->next != NULL)
      left->next->prev = left;

   n = left->pos;
   left->pos = right->pos;
   right->pos = n;
}


/*************************************************************************
  Kernel reordering routines
*************************************************************************/

/*=== Garbage collection for reordering ================================*/

/* We know that reorder_swap() never frees nodes on more than exactly
   one level, so decref() is not recursive.
*/
static void decref(int r)
{
   if (r < 2)
      return;

   DECREF(r);
   if (bddnodes[r].refcou == 0)
   {
      bddfreenum++;

      DECREF(bddnodes[r].low);
      DECREF(bddnodes[r].high);
   }
}


static void addref(int r)
{
   if (r < 2)
      return;
   
   if (bddnodes[r].refcou == 0)
   {
      bddfreenum--;
      INCREF(bddnodes[r].low);
      INCREF(bddnodes[r].high);
   }
   INCREF(r);
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


/* NOTE: Nodes may be marked when reorder_gbc is called!
   This function is also used to rehash everything.
 */
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


/* NOTE: Nodes may be marked when makenode is called!
 */
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

#if 0 /* Currently not used */
/* Note: make the real interaction matrix some day */
static int dependsOnNextLevel(int level)
{
   register int n;
   register int last = levellookup[level+1];

   for (n=levellookup[level] ; n<last ; n++)
   {
      register int r;

      for (r=bddnodes[n].hash ; r ; r=bddnodes[r].next)
	 if (bddnodes[bddnodes[r].low].level == level+1
	     || bddnodes[bddnodes[r].high].level == level+1)
	    return 1;
   }

   return 0;
}
#endif

static void reorder_fastVardown(int level)
{
   int n;
   int ll0 = levellookup[level];
   int ll1 = levellookup[level+1];
   
   for (n=0 ; n<levellookupsize ; n++)
   {
      register int tmp;

         /* Go through each chain and update level */
      for (tmp=bddnodes[n+ll0].hash ; tmp ; tmp=bddnodes[tmp].next)
	 bddnodes[tmp].level++;
      
      for (tmp=bddnodes[n+ll1].hash ; tmp ; tmp=bddnodes[tmp].next)
	 bddnodes[tmp].level--;
      
         /* Swap first elements in the chains */
      tmp = bddnodes[n+ll0].hash;
      bddnodes[n+ll0].hash = bddnodes[n+ll1].hash;
      bddnodes[n+ll1].hash = tmp;
   }
}


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
static int reorder_movedown(int level)
{
   register int n;
   int level1 = level+1;
   int ll0 = levellookup[level];
   int ll1 = levellookup[level+1];
   int allmoved = 1;
   
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
	    else
	       allmoved = 0;
	 }

	 node->next = bddnodes[hash].hash;
	 bddnodes[hash].hash = r;

	 r = next;
      }
   }

   return allmoved;
}


static void reorder_swap(int level)
{
   int prc;

      /* Be carefull  - lots of nontrivial global dependencies here! */

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
	       register BDD f0 = node->low;
	       register BDD f1 = node->high;
	       register BDD f00, f01, f10, f11;

  	          /* Note that moveup() has decrease all level-values */
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

	          /* We know that f00..f11 has a refcou greater than zero, so
		     there is no need to addref() *recursively* */
	       addref(f0 = reorder_makenode(level+1, f00, f10));
	       addref(f1 = reorder_makenode(level+1, f01, f11));
	       node = &bddnodes[r];  /* Might change in makenode */

	          /* We know that the refcou of the grandchilds of this node
		     is greater than one (these are f00...f11), so there is
		     no need to do a *recursive* refcou decrease. */
	       decref(node->low);
	       decref(node->high);
	       
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
   int level, allmoved;
   int n;
   
   if (var < 0  ||  var >= bddvarnum)
      return bdd_error(BDD_VAR);
   if ((level=bddvar2level[var]) >= bddvarnum-1)
      return 0;

   if (1)  /* Note: here is room for an interaction test */
   {
         /* Update those in 'level+1' */
      reorder_moveup(level+1);
   
         /* Update those in 'level' with both childs.level>level+1 */
      allmoved = reorder_movedown(level);
   
         /* Update the rest in 'level' */
      if (!allmoved)
	 reorder_swap(level);

         /* Garbage collect and remove marks on this level */
      local_gbc(level);
   }
   else
      reorder_fastVardown(level);
   
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

/*
NAME    {* bdd\_swapvar *}
SECTION {* reorder *}
SHORT   {* Swap two BDD variables *}
PROTO   {* int bdd_swapvar(int v1, int v2) *}
DESCR   {* Use {\tt bdd\_swapvar} to swap the position (in the current
           variable order) of the two BDD
           variables {\tt v1} and {\tt v2}. There are no constraints on the
	   position of the two variables before the call. This function may
	   {\em not} be used together with user defined variable blocks.
	   The swap is done by a series of adjacent variable swaps and
	   requires the whole node table to be rehashed twice for each call
	   to {\tt bdd\_swapvar}. It should therefore not be used were
	   efficiency is a major concern. *}
RETURN  {* Zero on succes and a negative error code otherwise. *}
ALSO    {* bdd\_reorder, bdd\_addvarblock *}
*/
int bdd_swapvar(int v1, int v2)
{
   int l1, l2;

      /* Do not swap when variable-blocks are used */
   if (vartree != NULL)
      return bdd_error(BDD_VARBLK);
	 
      /* Don't bother swapping x with x */
   if (v1 == v2)
      return 0;

      /* Make sure the variable exists */
   if (v1 < 0  ||  v1 >= bddvarnum  ||  v2 < 0  ||  v2 >= bddvarnum)
      return bdd_error(BDD_VAR);

   l1 = bddvar2level[v1];
   l2 = bddvar2level[v2];

      /* Make sure v1 is before v2 */
   if (l1 > l2)
   {
      int tmp = v1;
      v1 = v2;
      v2 = tmp;
      l1 = bddvar2level[v1];
      l2 = bddvar2level[v2];
   }

   reorder_init();
   
      /* Move v1 to v2's position */
   while (bddvar2level[v1] < l2)
      reorder_vardown(v1);

      /* Move v2 to v1's position */
   while (bddvar2level[v2] > l1)
      reorder_varup(v2);

   reorder_done();
   
   return 0;
}


void bdd_default_reohandler(int prestate)
{
   static long c1;

   if (verbose > 0)
   {
      if (prestate)
      {
	 printf("Start reordering\n");
	 c1 = clock();
      }
      else
      {
	 long c2 = clock();
	 printf("End reordering (%.1f sec)\n", (float)(c2-c1)/CLOCKS_PER_SEC);
      }
   }
}


/*
NAME    {* bdd\_disable\_reorder *}
SECTION {* reorder *}
SHORT   {* Disable automatic reordering *}
PROTO   {* void bdd_disable_reorder(void) *}
DESCR   {* Disables automatic reordering until {\tt bdd\_enable\_reorder}
           is called. Reordering is enabled by default as soon as any variable
	   blocks have been defined. *}
ALSO    {* bdd\_enable\_reorder *}
*/
void bdd_disable_reorder(void)
{
   reorderdisabled = 1;
}


/*
NAME    {* bdd\_enable\_reorder *}
SECTION {* reorder *}
SHORT   {* Enables automatic reordering *}
PROTO   {* void bdd_enable_reorder(void) *}
DESCR   {* Re-enables reordering after a call to {\tt bdd\_disable\_reorder}. *}
ALSO    {* bdd\_disable\_reorder *}
*/
void bdd_enable_reorder(void)
{
   reorderdisabled = 0;
}


int bdd_reorder_ready(void)
{
   if (bddreordermethod == BDD_REORDER_NONE  ||  vartree == NULL  ||
       bddreordertimes == 0  ||  reorderdisabled)
      return 0;
   return 1;
}

   
void bdd_reorder_auto(void)
{
   if (!bdd_reorder_ready)
      return;
   
   if (reorder_handler != NULL)
      reorder_handler(1);

   bdd_reorder(bddreordermethod);
   bddreordertimes--;
   
   if (reorder_handler != NULL)
      reorder_handler(0);
}


static int reorder_init(void)
{
   int n;

   if ((levellookup=NEW(int,bddvarnum)) == NULL)
      return -1;
   
   levellookupsize = bddnodesize / bddvarnum;
   for (n=0 ; n<bddvarnum ; n++)
   {
      levellookup[n] = n*levellookupsize;
   }
   
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


static int varseqCmp(const void *aa, const void *bb)
{
   int a = bddvar2level[*((const int*)aa)];
   int b = bddvar2level[*((const int*)bb)];

   if (a < b)
      return -1;
   if (a > b)
      return 1;
   return 0;
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

   if (t->seq != NULL)
      qsort(t->seq, t->last-t->first+1, sizeof(int), varseqCmp);
	 
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
   int savemethod = bddreordermethod;
   int savetimes = bddreordertimes;
   
   bddreordermethod = method;
   bddreordertimes = 1;
   
   if ((top=bddtree_new(-1)) == NULL)
      return;
   if (reorder_init() < 0)
      return;

   usednum_before = bddnodesize - bddfreenum;
   
   top->first = 0;
   top->last = bdd_varnum()-1;
   top->fixed = 0;
   top->next = NULL;
   top->nextlevel = vartree;

   reorder_block(top, method);
   vartree = top->nextlevel;
   free(top);
   
   usednum_after = bddnodesize - bddfreenum;
   
   reorder_done();
   bddreordermethod = savemethod;
   bddreordertimes = savetimes;
}


/*
NAME    {* bdd\_reorder\_gain *}
SECTION {* reorder *}
SHORT   {* Calculate the gain in size after a reordering *}
PROTO   {* int bdd_reorder_gain(void) *}
DESCR   {* Returns the gain in percent of the previous number of used
           nodes. The value returned is
	   \[ (100 * (A - B)) / A \]
	   Where $A$ is previous number of used nodes and $B$ is current
	   number of used nodes.
	*}
*/
int bdd_reorder_gain(void)
{
   if (usednum_before == 0)
      return 0;
   
   return (100*(usednum_before - usednum_after)) / usednum_before;
}


/*
NAME    {* bdd\_reorder\_hook *}
SECTION {* reorder *}
SHORT   {* sets a handler for automatic reorderings *}
PROTO   {* bddinthandler bdd_reorder_hook(bddinthandler handler) *}
DESCR   {* Whenever automatic reordering is done, a check is done to see
           if the user has supplied a handler for that event. If so then
	   it is called with the argument {\tt prestate} being 1 if the
	   handler is called immediately {\em before} reordering and
	   {\tt prestate} being 0 if it is called immediately after.
	   The default handler is
	   {\tt bdd\_default\_reohandler} which will print information
	   about the reordering.

	   A typical handler could look like this:
	   \begin{verbatim}
void reorderhandler(int prestate)
{
   if (prestate)
      printf("Start reordering");
   else
      printf("End reordering");
}
\end{verbatim} *}
RETURN  {* The previous handler *}
ALSO    {* bdd\_reorder, bdd\_autoreorder, bdd\_resize\_hook *}
*/
bddinthandler bdd_reorder_hook(bddinthandler handler)
{
   bddinthandler tmp = reorder_handler;
   reorder_handler = handler;
   return tmp;
}


/*
NAME    {* bdd\_blockfile\_hook *}
SECTION {* reorder *}
SHORT   {* Specifies a printing callback handler *}
PROTO   {* bddfilehandler bdd_blockfile_hook(bddfilehandler handler) *}
DESCR   {* A printing callback handler is used to convert the variable
           block identifiers into something readable by the end user. Use
	   {\tt bdd\_blockfile\_hook} to pass a handler to BuDDy. A typical
	   handler could look like this:
\begin{verbatim}
void printhandler(FILE *o, int block)
{
   extern char **blocknames;
   fprintf(o, "%s", blocknames[block]);
}
\end{verbatim}
           \noindent
           The handler is then called from {\tt bdd\_printorder} and
	   {\tt bdd\_reorder} (depending on the verbose level) with
           the block numbers returned by {\tt bdd\_addvarblock} as arguments.
	   No default handler is supplied. The argument {\tt handler} may be
	   NULL if no handler is needed. *}
RETURN  {* The old handler *}
ALSO    {* bdd\_printorder *}
*/
bddfilehandler bdd_blockfile_hook(bddfilehandler handler)
{
   bddfilehandler tmp = reorder_filehandler;
   reorder_filehandler = handler;
   return tmp;
}


/*
NAME    {* bdd\_autoreorder *}
EXTRA   {* bdd\_autoreorder\_times *}
SECTION {* reorder *}
SHORT   {* enables automatic reordering *}
PROTO   {* int bdd_autoreorder(int method)
int bdd_autoreorder_times(int method, int num) *}
DESCR   {* Enables automatic reordering using {\tt method} as the reordering
           method. If {\tt method} is {\tt BDD\_REORDER\_NONE} then
           automatic reordering is disabled. Automatic
	   reordering is done every time the number of active nodes in the
	   node table has been doubled and works by interrupting the current
	   BDD operation, doing the reordering and the retrying the operation.

	   In the second form the argument {\tt num} specifies the allowed
	   number of reorderings. So if for example a "one shot" reordering
	   is needed, then the {\tt num} argument would be set to one.

	   Values for {\tt method} can be found under {\tt bdd\_reorder}.
	   *}
RETURN  {* Returns the old value of {\tt method} *}
ALSO    {* bdd\_reorder *}
*/
int bdd_autoreorder(int method)
{
   int tmp = bddreordermethod;
   bddreordermethod = method;
   bddreordertimes = -1;
   return tmp;
}


int bdd_autoreorder_times(int method, int num)
{
   int tmp = bddreordermethod;
   bddreordermethod = method;
   bddreordertimes = num;
   return tmp;
}


/*
NAME    {* bdd\_var2level *}
SECTION {* reorder *}
SHORT   {* Fetch the level of a specific BDD variable *}
PROTO   {* int bdd_var2level(int var) *}
DESCR   {* Returns the position of the variable {\tt var} in the current
           variable order. *}
ALSO    {* bdd\_reorder, bdd\_level2var *}
*/
int bdd_var2level(int var)
{
   if (var < 0  ||  var >= bddvarnum)
      return bdd_error(BDD_VAR);

   return bddvar2level[var];
}


/*
NAME    {* bdd\_level2var *}
SECTION {* reorder *}
SHORT   {* Fetch the variable number of a specific level *}
PROTO   {* int bdd_level2var(int level) *}
DESCR   {* Returns the variable placed at position {\tt level} in the
           current variable order. *}
ALSO    {* bdd\_reorder, bdd\_var2level *}
*/
int bdd_level2var(int level)
{
   if (level < 0  ||  level >= bddvarnum)
      return bdd_error(BDD_VAR);

   return bddlevel2var[level];
}


/*
NAME    {* bdd\_getreorder\_times *}
SECTION {* reorder *}
SHORT   {* Fetch the current number of allowed reorderings *}
PROTO   {* int bdd_getreorder_times(void) *}
DESCR   {* Returns the current number of allowed reorderings left. This
           value can be defined by {\tt bdd\_autoreorder\_times}. *}
ALSO    {* bdd\_reorder\_times, bdd\_getreorder\_method *}
*/
int bdd_getreorder_times(void)
{
   return bddreordertimes;
}


/*
NAME    {* bdd\_getreorder\_method *}
SECTION {* reorder *}
SHORT   {* Fetch the current reorder method *}
PROTO   {* int bdd_getreorder_method(void) *}
DESCR   {* Returns the current reorder method as defined by
           {\tt bdd\_autoreorder}. *}
ALSO    {* bdd\_reorder, bdd\_getreorder\_times *}
*/
int bdd_getreorder_method(void)
{
   return bddreordermethod;
}


/*
NAME    {* bdd\_reorder\_verbose *}
SECTION {* reorder *}
SHORT   {* enables verbose information about reorderings *}
PROTO   {* int bdd_reorder_verbose(int v) *}
DESCR   {* With {\tt bdd\_reorder\_verbose} it is possible to set the level
           of information which should be printed during reordering. A value
	   of zero means no information, a value of one means some information
	   and any greater value will result in a lot of reordering
	   information. The default value is zero. *}
RETURN  {* The old verbose level *}
ALSO    {* bdd\_reorder *}
*/
int bdd_reorder_verbose(int v)
{
   int tmp = verbose;
   verbose = v;
   return tmp;
}


/*
NAME    {* bdd\_reorder\_probe *}
SECTION {* reorder *}
SHORT   {* Define a handler for minimization of BDDs *}
PROTO   {* bddsizehandler bdd_reorder_probe(bddsizehandler handler) *}
DESCR   {* Reordering is typically done to minimize the global number of
           BDD nodes in use, but it may in some cases be usefull to minimize
	   with respect to a specific BDD. With {\tt bdd\_reorder\_probe} it
	   is possible to define a callback function that calculates the
	   size of a specific BDD (or anything else in fact). This handler
	   will then be called by the reordering functions to get the current
	   size information. A typical handle could look like this:
\begin{verbatim}
int sizehandler(void)
{
   extern BDD mybdd;
   return bdd_nodecount(mybdd);
}
\end{verbatim}
	   No default handler is supplied. The argument {\tt handler} may be
	   NULL if no handler is needed. *}
	   *}
RETURN  {* The old handler *}
ALSO    {* bdd\_reorder *}
*/
bddsizehandler bdd_reorder_probe(bddsizehandler handler)
{
   bddsizehandler old = reorder_nodenum;
   if (handler == NULL)
      return reorder_nodenum;
   reorder_nodenum = handler;
   return old;
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
   blockid = 0;
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
	   in the block. This order does not depend on current variable
	   order.

	   The variable blocks are ordered as a tree, with the largest
	   ranges at top and the smallest at the bottom. Example: Assume
	   the block 0-9 is added as the first block and then the block 0-6.
	   This yields the 0-9 block at the top, with the 0-6 block as a
	   child. If now the block 2-4 was added, it would become a child
	   of the 0-6 block. A block of 0-8 would be a child of the 0-9
	   block and have the 0-6 block as a child. Partially overlapping
	   blocks are not allowed.

	   The {\tt fixed} parameter sets the block to be fixed (no
	   reordering of its child {\em blocks} is allowed) or free, using the
	   constants {\tt BDD\_REORDER\_FIXED} and {\tt
	   BDD\_REORDER\_FREE}.  Reordering is always done on the top
	   most blocks first and then recursively downwards.

	   The return value is an integer that can be used to identify
	   the block later on - with for example {\tt bdd\_blockfile\_hook}.
	   The values returned will be in the sequence $0,1,2,3,\ldots$.
	   *}
RETURN  {* A non-negative identifier on success, otherwise a negative error code. *}
ALSO {* fdd\_intaddvarblock, bdd\_clrvarblocks *} */
int bdd_addvarblock(BDD b, int fixed)
{
   BddTree *t;
   int n, *v, size;
   int first, last;
   
   if ((n=bdd_scanset(b, &v, &size)) < 0)
      return n;
   if (size < 1)
      return bdd_error(BDD_VARBLK);

   first = last = v[0];
   
   for (n=0 ; n<size ; n++)
   {
      if (v[n] < first)
	 first = v[n];
      if (v[n] > last)
	 last = v[n];
   }

   if ((t=bddtree_addrange(vartree, first,last, fixed,blockid)) == NULL)
      return bdd_error(BDD_VARBLK);
   
   vartree = t;
   return blockid++;
}


int bdd_intaddvarblock(int first, int last, int fixed)
{
   BddTree *t;

   if (first < 0  ||  first >= bddvarnum  ||  last < 0  ||  last >= bddvarnum)
      return bdd_error(BDD_VAR);
   
   if ((t=bddtree_addrange(vartree, first,last, fixed,blockid)) == NULL)
      return bdd_error(BDD_VARBLK);

   vartree = t;
   return blockid++;
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
  2{
     0
     1
  2}
  3
  4
\end{verbatim}
           This shows 5 variable blocks. The first one added is block zero,
	   which is on the same level as block one. These two blocks are then
	   sub-blocks of block two and block two is on the same level as
	   block three and four. The numbers are the identifiers returned
	   from {\tt bdd\_addvarblock}. The block levels depends on the
	   variables included in the blocks.
	   *}
ALSO    {* bdd\_reorder, bdd\_addvarblock *}
*/
void bdd_printorder(void)
{
   bdd_fprintorder(stdout);
}


static void print_order_rec(FILE *o, BddTree *t, int level)
{
   if (t == NULL)
      return;

   if (t->nextlevel)
   {
      fprintf(o, "%*s", level*3, "");
      if (reorder_filehandler)
	 reorder_filehandler(o,t->id);
      else
	 fprintf(o, "%3d", t->id);
      fprintf(o, "{\n");
      
      print_order_rec(o, t->nextlevel, level+1);
      
      fprintf(o, "%*s", level*3, "");
      if (reorder_filehandler)
	 reorder_filehandler(o,t->id);
      else
	 fprintf(o, "%3d", t->id);
      fprintf(o, "}\n");
      
      print_order_rec(o, t->next, level);
   }
   else
   {
      fprintf(o, "%*s", level*3, "");
      if (reorder_filehandler)
	 reorder_filehandler(o,t->id);
      else
	 fprintf(o, "%3d", t->id);
      fprintf(o, "\n");
      
      print_order_rec(o, t->next, level);
   }
}



void bdd_fprintorder(FILE *ofile)
{
   print_order_rec(ofile, vartree, 0);
}



/* EOF */
