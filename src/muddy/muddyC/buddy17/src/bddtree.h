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
  FILE:  tree.h
  DESCR: Trees for BDD variables
  AUTH:  Jorn Lind
  DATE:  (C) march 1998
*************************************************************************/

#ifndef _TREE_H
#define _TREE_H

typedef struct s_BddTree
{
   int first, last;  /* First and last variable in this block */
   int pos;          /* Sifting position */
   int *seq;         /* Sequence of first...last in the current order */
   char fixed;       /* Are the sub-blocks fixed or may they be reordered */
   int id;           /* A sequential id number given by addblock */
   struct s_BddTree *next, *prev;
   struct s_BddTree *nextlevel;
} BddTree;

BddTree *bddtree_new(int);
void     bddtree_del(BddTree *);
BddTree *bddtree_addrange(BddTree *, int, int, int, int);
void     bddtree_print(FILE *, BddTree *, int);

#endif /* _TREE_H */


/* EOF */
