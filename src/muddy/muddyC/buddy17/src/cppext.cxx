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
#include <stdlib.h>
#include <iomanip.h>
#include "kernel.h"
#include "bvec.h"

   /* Formatting objects for iostreams */
#define IOFORMAT_SET    0
#define IOFORMAT_TABLE  1
#define IOFORMAT_DOT    2
#define IOFORMAT_ALL    3
#define IOFORMAT_FDDSET 4

int bdd_ioformat::curformat = IOFORMAT_SET;
bdd_ioformat bddset(IOFORMAT_SET);
bdd_ioformat bddtable(IOFORMAT_TABLE);
bdd_ioformat bdddot(IOFORMAT_DOT);
bdd_ioformat bddall(IOFORMAT_ALL);
bdd_ioformat fddset(IOFORMAT_FDDSET);

   /* Constant true and false extension */
const bdd bddtruepp = bdd_true();
const bdd bddfalsepp = bdd_false();

   /* Internal prototypes */
static void bdd_printset_rec(ostream&, int, int*);
static void bdd_printdot_rec(ostream&, int);
static void fdd_printset_rec(ostream &, int, int *);


static bddstrmhandler strmhandler_bdd;
static bddstrmhandler strmhandler_fdd;


/*************************************************************************
  Setup (and shutdown)
*************************************************************************/

#undef bdd_init

int bdd_cpp_init(int n, int c)
{
   int ok = bdd_init(n,c);
   
   strmhandler_bdd = NULL;
   strmhandler_fdd = NULL;

   return ok;
}


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
      bdd_delref(root);
      root = r.root;
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

/*
NAME    {* bdd\_strm\_hook *}
SECTION {* kernel *}
SHORT   {* Specifies a printing callback handler *}
PROTO   {* bddstrmhandler bdd_strm_hook(bddstrmhandler handler) *}
DESCR   {* A printing callback handler for use with BDDs is used to
           convert the BDD variable number into something readable by the
	   end user. Typically the handler will print a string name
	   instead of the number. A handler could look like this:
	   \begin{verbatim}
void printhandler(ostream &o, int var)
{
   extern char **names;
   o << names[var];
}
\end{verbatim}

           \noindent
           The handler can then be passed to BuDDy like this:
	   {\tt bdd\_strm\_hook(printhandler)}.

	   No default handler is supplied. The argument {\tt handler} may be
	   NULL if no handler is needed. *}
RETURN  {* The old handler *}
ALSO    {* bdd\_printset, bdd\_file\_hook, fdd\_strm\_hook *}
*/
bddstrmhandler bdd_strm_hook(bddstrmhandler handler)
{
   bddstrmhandler old = strmhandler_bdd;
   strmhandler_bdd = handler;
   return old;
}


ostream &operator<<(ostream &o, const bdd &r)
{
   if (bdd_ioformat::curformat == IOFORMAT_SET)
   {
      if (r.root < 2)
      {
	 o << (r.root == 0 ? "F" : "T");
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

	    o << "[" << setw(5) << n << "] ";
	    if (strmhandler_bdd)
	       strmhandler_bdd(o,bddlevel2var[node.level]);
	    else
	       o << setw(3) << bddlevel2var[node.level];
	    o << " :";
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
   else
   if (bdd_ioformat::curformat == IOFORMAT_FDDSET)
   {
      if (ISCONST(r.root))
      {
	 o << (r == 0 ? "F" : "T");
	 return o;
      }
      
      int *set = new int[bddvarnum];
      if (set == NULL)
      {
	 bdd_error(BDD_MEMORY);
	 return o;
      }
      
      memset(set, 0, sizeof(int) * bddvarnum);
      fdd_printset_rec(o, r.root, set);
      delete[] set;
   }
   
   return o;
}


/*
NAME    {* operator{\tt<<} *}
SECTION {* fileio *}
SHORT   {* C++ output operator for BDDs *}
PROTO   {* ostream &operator<<(ostream &o, const bdd_ioformat &f)
ostream &operator<<(ostream &o, const bdd &r) *}
DESCR   {* BDDs can be printed in various formats using the C++ iostreams
           library. The formats are the those used in {\tt bdd\_printset},
	   {\tt bdd\_printtable}, {\tt fdd\_printset} and {\tt bdd\_printdot}.
	   The format can be specified with the following format objects:
	   \begin{tabular}{ll}\\
	     {\tt bddset } & BDD level set format \\
	     {\tt bddtable } & BDD level table format \\
	     {\tt bdddot }   & Output for use with Dot \\
	     {\tt bddall }   & The whole node table \\
	     {\tt fddset }   & FDD level set format \\
	   \end{tabular}\\

	   \noindent
	   So a BDD {\tt x} can for example be printed as a table with the
	   command\\

	   \indent {\tt cout << bddtable << x << endl}.
	   *}
RETURN  {* The specified output stream *}
ALSO    {* bdd\_strm\_hook, fdd\_strm\_hook *}
*/
ostream &operator<<(ostream &o, const bdd_ioformat &f)
{
   if (f.format == IOFORMAT_SET  ||  f.format == IOFORMAT_TABLE  ||
       f.format == IOFORMAT_DOT  ||  f.format == IOFORMAT_FDDSET)
      bdd_ioformat::curformat = f.format;
   else
   if (f.format == IOFORMAT_ALL)
   {
      for (int n=0 ; n<bddnodesize ; n++)
      {
	 const BddNode &node = bddnodes[n];
	 
	 if (node.low != -1)
	 {
	    o << "[" << setw(5) << n << "] ";
	    if (strmhandler_bdd)
	       strmhandler_bdd(o,bddlevel2var[node.level]);
	    else
	       o << setw(3) << bddlevel2var[node.level] << " :";
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
	    if (strmhandler_bdd)
	       strmhandler_bdd(o,bddlevel2var[n]);
	    else
	       o << bddlevel2var[n];
	    o << ":" << (set[n]==2 ? 1 : 0);
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
   if (ISCONST(r) || MARKED(r))
      return;

   o << r << "[label=\"";
   if (strmhandler_bdd)
      strmhandler_bdd(o,bddlevel2var[bddnodes[r].level]);
   else
      o << bddlevel2var[bddnodes[r].level];
   o << "\"];\n";
   o << r << " -> " << bddnodes[r].low << "[style=dotted];\n";
   o << r << " -> " << bddnodes[r].high << "[style=filled];\n";

   bddnodes[r].level |= MARKON;
   
   bdd_printdot_rec(o, bddnodes[r].low);
   bdd_printdot_rec(o, bddnodes[r].high);
}


static void fdd_printset_rec(ostream &o, int r, int *set)
{
   int n,m,i;
   int used = 0;
   int *binval;
   int ok, first;
   
   if (r == 0)
      return;
   else
   if (r == 1)
   {
      o << "<";
      first=1;
      int fdvarnum = fdd_domainnum();
	 
      for (n=0 ; n<fdvarnum ; n++)
      {
	 int firstval=1;
	 used = 0;
	 int binsize = fdd_varnum(n);
	 int *vars = fdd_vars(n);
	 
	 for (m=0 ; m<binsize ; m++)
	    if (set[vars[m]] != 0)
	       used = 1;
	 
	 if (used)
	 {
	    if (!first)
	       o << ", ";
	    first = 0;
	    if (strmhandler_fdd)
	       strmhandler_fdd(o, n);
	    else
	       o << n;
	    o << ":";

	    for (m=0 ; m<(1<<binsize) ; m++)
	    {
	       binval = fdddec2bin(n, m);
	       ok=1;
	       
	       for (i=0 ; i<binsize && ok ; i++)
		  if (set[vars[i]] == 1  &&  binval[i] != 0)
		     ok = 0;
		  else
		  if (set[vars[i]] == 2  &&  binval[i] != 1)
		     ok = 0;

	       if (ok)
	       {
		  if (firstval)
		     o << m;
		  else
		     o << "/" << m;
		  firstval = 0;
	       }

	       free(binval);
	    }
	 }
      }

      o << ">";
   }
   else
   {
      set[bddlevel2var[bddnodes[r].level]] = 1;
      fdd_printset_rec(o, bddnodes[r].low, set);
      
      set[bddlevel2var[bddnodes[r].level]] = 2;
      fdd_printset_rec(o, bddnodes[r].high, set);
      
      set[bddlevel2var[bddnodes[r].level]] = 0;
   }
}


/*=[ FDD I/O functions ]================================================*/

/*
NAME    {* fdd\_strm\_hook *}
SECTION {* fdd *}
SHORT   {* Specifies a printing callback handler *}
PROTO   {* bddstrmhandler fdd_strm_hook(bddstrmhandler handler) *}
DESCR   {* A printing callback handler for use with FDDs is used to
           convert the FDD integer identifier into something readable by the
	   end user. Typically the handler will print a string name
	   instead of the identifier. A handler could look like this:
	   \begin{verbatim}
void printhandler(ostream &o, int var)
{
   extern char **names;
   o << names[var];
}
\end{verbatim}

           \noindent
           The handler can then be passed to BuDDy like this:
	   {\tt fdd\_strm\_hook(printhandler)}.

	   No default handler is supplied. The argument {\tt handler} may be
	   NULL if no handler is needed. *}
RETURN  {* The old handler *}
ALSO    {* fdd\_printset, bdd\_file\_hook *}
*/
bddstrmhandler fdd_strm_hook(bddstrmhandler handler)
{
   bddstrmhandler old = strmhandler_fdd;
   strmhandler_fdd = handler;
   return old;
}


/*************************************************************************
   bvec functions
*************************************************************************/

bvec bvec::operator=(const bvec &src)
{
   if (&src != this)
   {
      bvec_free(roots);
      roots = bvec_copy(src.roots);
   }
   return *this;
}


void bvec::set(int bitnum, const bdd &b)
{
   bdd_delref(roots.bitvec[bitnum]);
   roots.bitvec[bitnum] = b.root;
   bdd_addref(roots.bitvec[bitnum]);
}


/*======================================================================*/

bvec bvec_map1(const bvec &a,
	       bdd (*fun)(const bdd &))
{
   bvec res;
   int n;

   res = bvec_false(a.bitnum());
   for (n=0 ; n < a.bitnum() ; n++)
      res.set(n, fun(a[n]));

   return res;
}


bvec bvec_map2(const bvec &a, const bvec &b,
	       bdd (*fun)(const bdd &, const bdd &))
{
   bvec res;
   int n;

   if (a.bitnum() != b.bitnum())
   {
      bdd_error(BVEC_SIZE);
      return res;
   }
   
   res = bvec_false(a.bitnum());
   for (n=0 ; n < a.bitnum() ; n++)
      res.set(n, fun(a[n], b[n]));

   return res;
}


bvec bvec_map3(const bvec &a, const bvec &b, const bvec &c,
	       bdd (*fun)(const bdd &, const bdd &, const bdd &))
{
   bvec res;
   int n;

   if (a.bitnum() != b.bitnum()  ||  b.bitnum() != c.bitnum())
   {
      bdd_error(BVEC_SIZE);
      return res;
   }
   
   res = bvec_false(a.bitnum());
   for (n=0 ; n < a.bitnum() ; n++)
      res.set(n, fun(a[n], b[n], c[n]) );

   return res;
}


int bvec_div(const bvec &e, int c, bvec &res, bvec &rem)
{
   bvec_free(res.roots);
   bvec_free(rem.roots);
   return bvec_div(e.roots, c, &res.roots, &rem.roots);
}


/* EOF */
