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
  FILE:  tree.c
  DESCR: Trees for BDD variables
  AUTH:  Jorn Lind
  DATE:  (C) march 1998
*************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include "kernel.h"
#include "bddtree.h"

/*************************************************************************
*************************************************************************/

BddTree *bddtree_addrange_rec(BddTree *, BddTree *, int, int, int, int);


/*======================================================================*/

static void update_seq(BddTree *t)
{
   int n;
   int low = t->first;
   
   for (n=t->first ; n<=t->last ; n++)
      if (bddvar2level[n] < bddvar2level[low])
	 low = n;

   for (n=t->first ; n<=t->last ; n++)
      t->seq[bddvar2level[n]-bddvar2level[low]] = n;
}


BddTree *bddtree_new(int id)
{
   BddTree *t = NEW(BddTree,1);
   if (t == NULL)
      return NULL;

   t->first = t->last = -1;
   t->fixed = 1;
   t->next = t->prev = t->nextlevel = NULL;
   t->seq = NULL;
   t->id = id;
   return t;
}


void bddtree_del(BddTree *t)
{
   if (t == NULL)
      return;
   
   bddtree_del(t->nextlevel);
   bddtree_del(t->next);
   if (t->seq != NULL)
      free(t->seq);
   free(t);
}


BddTree *bddtree_addrange_rec(BddTree *t, BddTree *prev,
			      int first, int last, int fixed, int id)
{
   if (first < 0  ||  last < 0  ||  last < first)
      return NULL;

      /* Empty tree -> build one */
   if (t == NULL)
   {
      if ((t=bddtree_new(id)) == NULL)
	 return NULL;
      t->first = first;
      t->fixed = fixed;
      t->seq = NEW(int,last-first+1);
      t->last = last;
      update_seq(t);
      t->prev = prev;
      return t;
   }

      /* Check for identity */
   if (first == t->first  &&  last == t->last)
      return t;
   
      /* Before this section -> insert */
   if (last < t->first)
   {
      BddTree *tnew = bddtree_new(id);
      if (tnew == NULL)
	 return NULL;
      tnew->first = first;
      tnew->last = last;
      tnew->fixed = fixed;
      tnew->seq = NEW(int,last-first+1);
      update_seq(tnew);
      tnew->next = t;
      tnew->prev = t->prev;
      t->prev = tnew;
      return tnew;
   }

      /* After this this section -> go to next */
   if (first > t->last)
   {
      t->next = bddtree_addrange_rec(t->next, t, first, last, fixed, id);
      return t;
   }

      /* Inside this section -> insert in next level */
   if (first >= t->first  &&  last <= t->last)
   {
      t->nextlevel =
	 bddtree_addrange_rec(t->nextlevel,NULL,first,last,fixed,id);
      return t;
   }

      /* Covering this section -> insert above this level */
   if (first <= t->first)
   {
      BddTree *tnew;
      BddTree *this = t;

      while (1)
      {
	    /* Partial cover ->error */
	 if (last >= this->first  &&  last < this->last)
	    return NULL;

	 if (this->next == NULL  ||  last < this->next->first)
	 {
	    tnew = bddtree_new(id);
	    if (tnew == NULL)
	       return NULL;
	    tnew->first = first;
	    tnew->last = last;
	    tnew->fixed = fixed;
	    tnew->seq = NEW(int,last-first+1);
	    update_seq(tnew);
	    tnew->nextlevel = t;
	    tnew->next = this->next;
	    tnew->prev = t->prev;
	    if (this->next != NULL)
	       this->next->prev = tnew;
	    this->next = NULL;
	    t->prev = NULL;
	    return tnew;
	 }
	 
	 this = this->next;
      }
      
   }
      
   return NULL;
}


BddTree *bddtree_addrange(BddTree *t, int first, int last, int fixed,int id)
{
   return bddtree_addrange_rec(t,NULL,first,last,fixed,id);
}


#if 0
int main(void)
{
   BddTree *t = NULL;

   t = bddtree_addrange(t, 8,10,1);
   printf("A\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 2,99,1);
   printf("B\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 11,50,1);
   printf("C\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 5,7,1);
   printf("D\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 5,10,1);
   printf("E\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 100,150,1);
   printf("F\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 60,65,1);
   printf("G\n"); bddtree_print(stdout, t, 0);
   t = bddtree_addrange(t, 3,200,1);

   printf("H\n"); bddtree_print(stdout, t, 0);
   bddtree_del(t);
   return 0;
}
#endif

/* EOF */
