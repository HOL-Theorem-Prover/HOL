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
  FILE:  cppext.cxx
  DESCR: C++ extension of BDD package
  AUTH:  Jorn Lind
  DATE:  (C) august 1997
*************************************************************************/
#include <string.h>
#include <iomanip.h>
#include "kernel.h"


   /* Formatting objects for iostreams */
#define IOFORMAT_SET   0
#define IOFORMAT_TABLE 1
#define IOFORMAT_DOT   2
#define IOFORMAT_ALL   3

int bdd_ioformat::curformat = IOFORMAT_SET;
bdd_ioformat bddset(IOFORMAT_SET);
bdd_ioformat bddtable(IOFORMAT_TABLE);
bdd_ioformat bdddot(IOFORMAT_DOT);
bdd_ioformat bddall(IOFORMAT_ALL);

   /* Constant true and false extension */
const bdd bddtruepp = bdd_true();
const bdd bddfalsepp = bdd_false();

   /* Internal prototypes */
static void bdd_printset_rec(ostream&, int, int*);
static void bdd_printdot_rec(ostream&, int);


/*************************************************************************
  BDD C++ functions
*************************************************************************/

int bdd_setbddpairs(bddPair *pair, int *oldvar, const bdd *newvar, int size)
{
   if (pair == NULL)
      return 0;
   
   for (int n=0,e=0 ; n<size ; n++)
      if ((e=bdd_setbddpair(pair, oldvar[n], newvar[n].root)) < 0)
	 return e;
   
   return 0;
}


/*************************************************************************
  BDD class functions
*************************************************************************/

bdd bdd::operator=(const bdd &r)
{
   if (root != r.root)
   {
      bdd_delref(root); root = r.root;
      bdd_addref(root);
   }
   return *this;
}


bdd bdd::operator=(int r)
{
   if (root != r)
   {
      bdd_delref(root);
      root = r;
      bdd_addref(root);
   }
   return *this;
}


/*************************************************************************
  C++ iostream operators
*************************************************************************/

ostream &operator<<(ostream &o, const bdd &r)
{
   if (bdd_ioformat::curformat == IOFORMAT_SET)
   {
      if (r.root < 2)
      {
	 o << (r.root == 0 ? "F" : "T") << "\n";
	 return o;
      }
      
      int *set = new int[bddvarnum];
      if (set == NULL)
      {
	 bdd_error(BDD_MEMORY);
	 return o;
      }
      
      memset(set, 0, sizeof(int) * bddvarnum);
      bdd_printset_rec(o, r.root, set);
      delete[] set;
   }
   else
   if (bdd_ioformat::curformat == IOFORMAT_TABLE)
   {
      o << "ROOT: " << r.root << "\n";
      if (r.root < 2)
	 return o;
      
      bdd_mark(r.root);

      for (int n=0 ; n<bddnodesize ; n++)
      {
	 if (bddnodes[n].level & MARKON)
	 {
	    BddNode &node = bddnodes[n];
	 
	    node.level &= MARKOFF;

	    o << "[" << setw(5) << n << "] " << setw(2) << node.level << " :";
	    o << " " << setw(3) << node.low;
	    o << " " << setw(3) << node.high;
	    o << "\n";
	 }
      }
   }
   else
   if (bdd_ioformat::curformat == IOFORMAT_DOT)
   {
      o << "digraph G {\n";
      o << "0 [shape=box, label=\"1\", style=filled, shape=box, height=0.3, width=0.3];\n";
      o << "1 [shape=box, label=\"0\", style=filled, shape=box, height=0.3, width=0.3];\n";
      
      bdd_printdot_rec(o, r.root);
      
      o << "}\n";
      
      for (int n=0 ; n<bddnodesize ; n++)
	 if (bddnodes[n].level & MARKON)
	    bddnodes[n].level &= MARKOFF;
   }

   return o;
}


ostream &operator<<(ostream &o, const bdd_ioformat &f)
{
   if (f.format == IOFORMAT_SET  ||  f.format == IOFORMAT_TABLE  ||
       f.format == IOFORMAT_DOT)
      bdd_ioformat::curformat = f.format;
   else
   if (f.format == IOFORMAT_ALL)
   {
      for (int n=0 ; n<bddnodesize ; n++)
      {
	 const BddNode &node = bddnodes[n];
	 
	 if (node.low != -1)
	 {
	    o << "[" << setw(5) << n << "] " << setw(2) << node.level << " :";
	    o << " " << setw(3) << node.low;
	    o << " " << setw(3) << node.high;
	    o << "\n";
	 }
      }
   }
   
   return o;
}


static void bdd_printset_rec(ostream& o, int r, int* set)
{
   int n;
   int first;
   
   if (r == 0)
      return;
   else
   if (r == 1)
   {
      o << "<";
      first = 1;
      
      for (n=0 ; n<bddvarnum ; n++)
      {
	 if (set[n] > 0)
	 {
	    if (!first)
	       o << ", ";
	    first = 0;
	    o << n << ":" << (set[n]==2 ? 1 : 0);
	 }
      }

      o << ">";
   }
   else
   {
      set[bddnodes[r].level] = 1;
      bdd_printset_rec(o, bddnodes[r].low, set);
      
      set[bddnodes[r].level] = 2;
      bdd_printset_rec(o, bddnodes[r].high, set);
      
      set[bddnodes[r].level] = 0;
   }
}


static void bdd_printdot_rec(ostream& o, int r)
{
   if (r < 2 || (bddnodes[r].level & MARKON))
      return;

   o << r << "[label=\"" << bddnodes[r].level << "\"];\n";
   o << r << " -> " << bddnodes[r].low << "[style=dotted];\n";
   o << r << " -> " << bddnodes[r].high << "[style=filled];\n";

   bddnodes[r].level |= MARKON;
   
   bdd_printdot_rec(o, bddnodes[r].low);
   bdd_printdot_rec(o, bddnodes[r].high);
}


/* EOF */
