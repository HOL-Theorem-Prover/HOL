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
  FILE:  cache.c
  DESCR: Cache class for caching apply/exist etc. results in BDD package
  AUTH:  Jorn Lind
  DATE:  (C) june 1997
*************************************************************************/
#include <stdlib.h>
#include "kernel.h"
#include "cache.h"

/*************************************************************************
*************************************************************************/

int BddCache_init(BddCache *cache, int size)
{
   int n;
   
   if ((cache->table=(BddCacheData*)malloc(sizeof(BddCacheData)*size)) == NULL)
      return bdd_error(BDD_MEMORY);
   
   for (n=0 ; n<size ; n++)
      cache->table[n].a = -1;
   cache->tablesize = size;
   
   return 0;
}


void BddCache_done(BddCache *cache)
{
   free(cache->table);
   cache->table = NULL;
   cache->tablesize = 0;
}


void BddCache_reset(BddCache *cache)
{
   register BddCacheData *n;
   for (n=cache->table+cache->tablesize-1 ; n>=cache->table ; n--)
      n->a = -1;
}


/* EOF */
