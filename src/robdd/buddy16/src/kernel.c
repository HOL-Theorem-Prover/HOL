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
  FILE:  kernel.c
  DESCR: implements the bdd kernel functions.
  AUTH:  Jorn Lind
  DATE:  (C) june 1997

  WARNING: Do not use pointers to nodes across makenode calls,
           as makenode may resize/move the nodetable.

*************************************************************************/
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <assert.h>

#include "kernel.h"
#include "cache.h"

/*************************************************************************
  Various definitions and global variables
*************************************************************************/

/*=== EXTERNAL VARIABLES FOR PACKAGE USERS =============================*/

/*
NAME    {* bddtrue *}
SECTION {* kernel *}
SHORT   {* the constant true bdd *}
PROTO   {* extern const BDD bddtrue; *}
DESCR   {* This bdd holds the constant true value *}
ALSO    {* bddfalse, bdd\_true, bdd\_false *}
*/
const BDD bddtrue=1;                     /* The constant true bdd */

/*
NAME    {* bddfalse*}
SECTION {* kernel *}
SHORT   {* the constant false bdd *}
PROTO   {* extern const BDD bddfalse; *}
DESCR   {* This bdd holds the constant false value *}
ALSO    {* bddtrue, bdd\_true, bdd\_false *}
*/
const BDD bddfalse=0;                    /* The constant false bdd */


/*=== INTERNAL DEFINITIONS =============================================*/

/* Min. number of nodes (%) that has to be left after a garbage collect
   unless a resize should be done. */
static int minfreenodes=20;


/*=== KERNEL VARIABLES =================================================*/

int          bddrunning;            /* Flag - package initialized */
int          bdderrorcond;          /* Some error condition */
int          bddnodesize;           /* Number of allocated nodes */
int          bddmaxnodesize;        /* Maximum allowed number of nodes */
int          bddmaxnodeincrease;    /* Max. # of nodes used to inc. table */
BddNode*     bddnodes;              /* All of the bdd nodes */
int          bddfreepos;            /* First free node */
int          bddfreenum;            /* Number of free nodes */
long int     bddproduced;           /* Number of new nodes ever produced */
int          bddvarnum;             /* Number of defined BDD variables */
int*         bddrefstack;           /* Internal node reference stack */
int*         bddrefstacktop;        /* Internal node reference stack top */
int*         bddvar2level;          /* Variable -> level table */
int*         bddlevel2var;          /* Level -> variable table */
int          bddreordermethod;      /* Current auto reord. method */
int          bddtryreordering;      /* Flag, auto reord. should be tried now */


/*=== PRIVATE KERNEL VARIABLES =========================================*/

static BDD*     bddvarset;            /* Set of defined BDD variables */
static int      gbcollectnum;         /* Number of garbage collections */
static int      cachesize;            /* Size of the operator caches */
static long int gbcclock;             /* Clock ticks used in GBC */
static bddinthandler  err_handler;    /* Error handler */
static bddgbchandler  gbc_handler;    /* Garbage collection handler */
static bdd2inthandler resize_handler; /* Node-table-resize handler */


   /* Strings for all error mesages */
static char *errorstrings[BDD_ERRNUM] =
{ "Out of memory", "Unknown variable", "Value out of range",
  "Unknown BDD root dereferenced", "bdd_init() called twice",
  "File operation failed", "Incorrect file format",
  "Variables not in ascending order", "User called break",
  "Mismatch in size of variable sets",
  "Cannot allocate fewer nodes than already in use",
  "Unknown operator", "Illegal variable set",
  "Bad variable block",
  "Trying to decrease the number of variables",
  "Trying to replace with variables already in the bdd",
  "Number of nodes reached user defined maximum",
  "Unknown BDD - was not in node table",
  "Bad size argument" };


/*=== OTHER INTERNAL DEFINITIONS =======================================*/

#define xNODEHASH(lvl,l,h) (((lvl<<1)+((l<<1)+h)) % bddnodesize)
#define NODEHASH(lvl,l,h) (TRIPLE(lvl,l,h) % bddnodesize)


/*************************************************************************
  BDD misc. user operations
*************************************************************************/

/*
NAME   {* bdd\_init *}
SECTION {* kernel *}
SHORT  {* initializes the BDD package *}
PROTO  {* int bdd_init(int nodesize, int cachesize) *}
DESCR  {* This function initiates the bdd package and {\em must} be called
          before any bdd operations are done. The argument {\tt nodesize}
	  is the initial number of nodes in the nodetable and {\tt cachesize}
	  is the fixed size of the internal caches. Typical values for
	  {\tt nodesize} are 10000 nodes for small test examples and up to
	  1000000 nodes for large examples. A cache size of 10000 seems to
	  work good even for large examples, but lesser values should do it
	  for smaller examples.

	  The initial number of nodes is not critical for any bdd operation
	  as the table will be resized whenever there are to few nodes left
	  after a garbage collection. But it does have some impact on the
	  efficency of the operations. *}
RETURN {* If no errors occur then 0 is returned, otherwise
          a negative error code. *}
ALSO   {* bdd\_done, bdd\_resize\_hook *}
*/
int bdd_init(int initnodesize, int cs)
{
   int n, err;
   
   if (bddrunning)
      return bdd_error(BDD_RUNNING);
   
   if ((bddnodes=(BddNode*)malloc(sizeof(BddNode)*initnodesize)) == NULL)
      return bdd_error(BDD_MEMORY);
   bddnodesize = initnodesize;
   
   for (n=0 ; n<bddnodesize ; n++)
   {
      bddnodes[n].refcou = 0;
      bddnodes[n].low = -1;
      bddnodes[n].hash = 0;
      bddnodes[n].level = 0;
      bddnodes[n].next = n+1;
   }
   bddnodes[bddnodesize-1].next = 0;

   bddnodes[0].refcou = bddnodes[1].refcou = MAXREF;
   bddnodes[0].low = bddnodes[0].high = 0;
   bddnodes[1].low = bddnodes[1].high = 1;
   
   if ((err=bdd_operator_init(cs)) < 0)
   {
      bdd_done();
      return err;
   }

   bddfreepos = 2;
   bddfreenum = bddnodesize-2;
   bddrunning = 1;
   bddvarnum = 0;
   gbcollectnum = 0;
   gbcclock = 0;
   cachesize = cs;
   bddreordermethod = 0;
   bddtryreordering = 0;
   bddmaxnodeincrease = DEFAULTMAXNODEINC;
   
   bdd_fddinit();
   bdd_gbc_hook(bdd_default_gbchandler);
   bdd_error_hook(bdd_default_errhandler);
   bdd_resize_hook(NULL);
   bdd_clrvarblocks();
   bdd_reorder_hook(bdd_default_reohandler);
   bdd_reorder_verbose(0);
   
   bdd_pairs_init();
   
   return 0;
}


/*
NAME    {* bdd\_done*}
SECTION {* kernel *}
SHORT {* resets the bdd package *}
PROTO {* void bdd_done(void) *}
DESCR {* This function frees all memory used by the bdd package and resets
         the package to it's initial state.*}
ALSO  {* bdd\_init *}
*/
void bdd_done(void)
{
   bdd_pairs_done();
   bdd_fdddone();
   
   free(bddnodes);
   free(bddrefstack);
   free(bddvarset);
   
   bddnodes = NULL;
   bddrefstack = NULL;
   bddvarset = NULL;

   bdd_operator_done();

   bddrunning = 0;
   bddnodesize = 0;
   bddmaxnodesize = 0;
   bddvarnum = 0;
   bddproduced = 0;
   
   err_handler = NULL;
   gbc_handler = NULL;
   resize_handler = NULL;
}


/*
NAME    {* bdd\_setvarnum *}
SECTION {* kernel *}
SHORT   {* set the number of used bdd variables *}
PROTO   {* int bdd_setvarnum(int num) *}
DESCR   {* This function is used to define the number of variables used in
           the bdd package. It may be called more than one time, but only
	   to increase the number of variables. The argument
	   {\tt num} is the number of variables to use. *}
RETURN  {* Zero on succes, otherwise a negative error code. *}
ALSO    {* bdd\_ithvar, bdd\_varnum, bdd\_extvarnum *}
*/
int bdd_setvarnum(int num)
{
   int bdv;
   int oldbddvarnum = bddvarnum;
   
   if (num < 1  ||  num > MAXVAR)
   {
      bdd_error(BDD_RANGE);
      return bddfalse;
   }

   if (num < bddvarnum)
      return bdd_error(BDD_DECVNUM);
   if (num == bddvarnum)
      return 0;

   if (bddvarset == NULL)
   {
      if ((bddvarset=(BDD*)malloc(sizeof(BDD)*num*2)) == NULL)
	 return bdd_error(BDD_MEMORY);
      if ((bddlevel2var=(int*)malloc(sizeof(int)*num)) == NULL)
      {
	 free(bddvarset);
	 return bdd_error(BDD_MEMORY);
      }
      if ((bddvar2level=(int*)malloc(sizeof(int)*num)) == NULL)
      {
	 free(bddvarset);
	 free(bddlevel2var);
	 return bdd_error(BDD_MEMORY);
      }
   }
   else
   {
      if ((bddvarset=(BDD*)realloc(bddvarset,sizeof(BDD)*num*2)) == NULL)
	 return bdd_error(BDD_MEMORY);
      if ((bddlevel2var=(int*)realloc(bddlevel2var,sizeof(int)*num)) == NULL)
      {
	 free(bddvarset);
	 return bdd_error(BDD_MEMORY);
      }
      if ((bddvar2level=(int*)realloc(bddvar2level,sizeof(int)*num)) == NULL)
      {
	 free(bddvarset);
	 free(bddlevel2var);
	 return bdd_error(BDD_MEMORY);
      }
   }

   if (bddrefstack != NULL)
      free(bddrefstack);
   bddrefstack = bddrefstacktop = (int*)malloc(sizeof(int)*(num*2+4));

   for(bdv=bddvarnum ; bddvarnum < num; bddvarnum++)
   {
      bddvarset[bddvarnum*2] = PUSHREF( bdd_makenode(bddvarnum, 0, 1) );
      bddvarset[bddvarnum*2+1] = bdd_makenode(bddvarnum, 1, 0);
      POPREF(1);
      
      if (bdderrorcond)
      {
	 bddvarnum = bdv;
	 return -bdderrorcond;
      }
      
      bddnodes[bddvarset[bddvarnum*2]].refcou = MAXREF;
      bddnodes[bddvarset[bddvarnum*2+1]].refcou = MAXREF;
      bddlevel2var[bddvarnum] = bddvarnum;
      bddvar2level[bddvarnum] = bddvarnum;
   }
   
   bddnodes[0].level = num;
   bddnodes[1].level = num;

   bdd_pairs_resize(oldbddvarnum, bddvarnum);
   bdd_operator_resize();
   
   return 0;
}


/*
NAME    {* bdd\_extvarnum *}
SECTION {* kernel *}
SHORT   {* add extra BDD variables *}
PROTO   {* int bdd_extvarnum(int num) *}
DESCR   {* Extends the current number of allocated BDD variables with
           {\tt num} extra variables. *}
RETURN  {* The old number of allocated variables or a negative error code. *}
ALSO    {* bdd\_setvarnum, bdd\_ithvar, bdd\_nithvar *}
*/
int bdd_extvarnum(int num)
{
   int start = bddvarnum;
   
   if (num < 0  ||  num > 0x3FFFFFFF)
      return bdd_error(BDD_RANGE);

   bdd_setvarnum(bddvarnum+num);
   return start;
}


/*
NAME  {* bdd\_error\_hook *}
SECTION {* kernel *}
SHORT {* set a handler for error conditions *}
PROTO {* bddinthandler bdd_error_hook(bddinthandler handler) *}
DESCR {* Whenever an error occurs in the bdd package a test is done to
        see if an error handler is supplied by the user and if such exists
	then it will be called
	with an error code in the variable {\tt errcode}. The handler may
	then print any usefull information and return or exit afterwards.

	This function sets the handler to be {\tt handler}. If a {\tt NULL}
	argument is supplied then no calls are made when an error occurs.
	Possible error codes are found in {\tt bdd.h}. The default handler
	is {\tt bdd\_default\_errhandler} which will use {\tt exit()} to
	terminate the program.

	Any handler should be defined like this:
	\begin{verbatim}
void my_error_handler(int errcode)
{
   ...
}
\end{verbatim} *}
RETURN {* The previous handler *}
ALSO  {* bdd\_errstring *}
*/
bddinthandler bdd_error_hook(bddinthandler handler)
{
   bddinthandler tmp = err_handler;
   err_handler = handler;
   return tmp;
}


/*
NAME  {* bdd\_gbc\_hook *}
SECTION {* kernel *}
SHORT {* set a handler for garbage collections *}
PROTO {* bddgbchandler bdd_gbc_hook(bddgbchandler handler) *}
DESCR {* Whenever a garbage collection is required, a test is done to
         see if a handler for this event is supplied by the user and if such
	 exists then it is called, both before and after the garbage collection
	 takes places. This is indicated by an integer flag {\tt pre} passed to
	 the handler, which will be one before garbage collection and zero
	 after garbage collection.

	 This function sets the handler to be {\tt handler}. If a {\tt
	 NULL} argument is supplied then no calls are made when a
	 garbage collection takes place. The argument {\tt pre}
	 indicates pre vs. post garbage collection and the argument
	 {\tt stat} contains information about the garbage
	 collection. No default handler is installed.

	 Any handler should be defined like this:
	 \begin{verbatim}
void my_gbc_handler(int pre, bddGbcStat *stat)
{
   ...
}
\end{verbatim} *}
RETURN {* The previous handler *}
ALSO {* bdd\_resize\_hook, bdd\_reorder\_hook *} */
bddgbchandler bdd_gbc_hook(bddgbchandler handler)
{
   bddgbchandler tmp = gbc_handler;
   gbc_handler = handler;
   return tmp;
}


/*
NAME  {* bdd\_resize\_hook  *}
SECTION {* kernel *}
SHORT {* set a handler for nodetable resizes *}
PROTO {* bdd2inthandler bdd_resize_hook(bdd2inthandler handler) *}
DESCR {* Whenever it is impossible to get enough free nodes by a garbage
         collection then the node table is resized and a test is done to see
	 if a handler is supllied by the user for this event. If so then
	 it is called with {\tt oldsize} being the old nodetable size and
	 {\tt newsize} being the new nodetable size.

	 This function sets the handler to be {\tt handler}. If a {\tt NULL}
	 argument is supplied then no calls are made when a table resize
	 is done. No default handler is supplied.

	 Any handler should be defined like this:
	 \begin{verbatim}
void my_resize_handler(int oldsize, int newsize)
{
   ...
}
\end{verbatim} *}
RETURN {* The previous handler *}
ALSO  {* bdd\_gbc\_hook, bdd\_reorder\_hook, bdd\_setminfreenodes  *}
*/
bdd2inthandler bdd_resize_hook(bdd2inthandler handler)
{
   bdd2inthandler tmp = handler;
   resize_handler = handler;
   return tmp;
}


/*
NAME    {* bdd\_setmaxincrease *}
SECTION {* kernel *}
SHORT   {* set max. number of nodes used to increase node table *}
PROTO   {* int bdd_setmaxincrease(int size) *}
DESCR   {* The node table is expanded by doubling the size of the table
           when no more free nodes can be found, but a maximum for the
	   number of new nodes added can be set with {\tt bdd\_maxincrease}
	   to {\tt size} nodes. The default is 50000 nodes (1 Mb). *}
RETURN  {* The old threshold on succes, otherwise a negative error code. *}
ALSO    {* bdd\_setmaxnodenum, bdd\_setminfreenodes *}
*/
int bdd_setmaxincrease(int size)
{
   int old = bddmaxnodeincrease;
   
   if (size < 0)
      return bdd_error(BDD_SIZE);

   bddmaxnodeincrease = size;
   return old;
}

/*
NAME    {* bdd\_setmaxnodenum *}
SECTION {* kernel *}
SHORT {* set the maximum available number of bdd nodes *}
PROTO {* int bdd_setmaxnodenum(int size) *}
DESCR {* This function sets the maximal number of bdd nodes the package may
         allocate before it gives up a bdd operation. The
	 argument {\tt size} is the absolute maximal number of nodes there
	 may be allocated for the nodetable. Any attempt to allocate more
	 nodes results in the constant false being returned and the error
	 handler being called until some nodes are deallocated.
	 A value of 0 is interpreted as an unlimited amount.
	 It is {\em not} possible to specify
	 fewer nodes than there has already been allocated. *}
RETURN {* The old threshold on succes, otherwise a negative error code. *}
ALSO   {* bdd\_setmaxincrease, bdd\_setminfreenodes *}
*/
int bdd_setmaxnodenum(int size)
{
   if (size > bddnodesize  ||  size == 0)
   {
      int old = bddmaxnodesize;
      bddmaxnodesize = size;
      return old;
   }

   return bdd_error(BDD_NODES);
}


/*
NAME    {* bdd\_setminfreenodes *}
SECTION {* kernel *}
SHORT   {* set min. no. of nodes to be reclaimed after GBC. *}
PROTO   {* int bdd_setminfreenodes(int n) *}
DESCR   {* Whenever a garbage collection is executed the number of free
           nodes left are checked to see if a resize of the nodetable is
	   required. If $X = (bddfreenum*100)/maxnum$ is less than or
	   equal to {\tt n} then a resize is initiated. The range of
	   {\tt n} is of course $0\ldots 100$ and has some influence
	   on how fast the package is. A low number means harder attempts
	   to avoid resizing and saves space, and a high number reduces
	   the time used in garbage collections. The default value is
	   20. *}
RETURN  {* The old threshold on succes, otherwise a negative error code. *}
ALSO    {* bdd\_setmaxnodenum, bdd\_setmaxincrease *}
*/
int bdd_setminfreenodes(int mf)
{
   int old = minfreenodes;
   
   if (mf<0 || mf>100)
      return bdd_error(BDD_RANGE);

   minfreenodes = mf;
   return old;
}


/*
NAME    {* bdd\_getnodenum *}
SECTION {* kernel *}
SHORT   {* get the number of active nodes in use *}
PROTO   {* int bdd_getnodenum(void) *}
DESCR   {* Returns the number of nodes in the nodetable that are
           currently in use. *}
RETURN  {* The number of nodes. *}
ALSO    {* bdd\_setmaxnodenum *}
*/
int bdd_getnodenum(void)
{
   return bddnodesize - bddfreenum;
}


/*
NAME    {* bdd\_isrunning *}
SECTION {* kernel *}
SHORT   {* test whether the package is started or not *}
PROTO   {* void bdd_isrunning(void) *}
DESCR   {* This function tests the internal state of the package and returns
          a status. *}
RETURN  {* 1 (true) if the package has been started, otherwise 0. *}
ALSO    {* bdd\_init, bdd\_done *}
*/
int bdd_isrunning(void)
{
   return bddrunning;
}


/*
NAME    {* bdd\_versionstr *}
SECTION {* kernel *}
SHORT   {* returns a text string with version information *}
PROTO   {* char* bdd_versionstr(void) *}
DESCR   {* This function returns a text string with information about the
           version of the bdd package. *}
ALSO    {* bdd\_versionnum *}
*/
char *bdd_versionstr(void)
{
   static char str[100];
   sprintf(str, "BuDDy -  release %d.%d", VERSION/10, VERSION%10);
   return str;
}


/*
NAME    {* bdd\_versionnum *}
SECTION {* kernel *}
SHORT   {* returns the version number of the bdd package *}
PROTO   {* int bdd_versionnum(void) *}
DESCR   {* This function returns the version number of the bdd package. The
           number is in the range 10-99 for version 1.0 to 9.9. *}
ALSO    {* bdd\_versionstr *}
*/
int bdd_versionnum(void)
{
   return VERSION;
}


/*
NAME    {* bdd\_stats *}
SECTION {* kernel *}
SHORT   {* returns some status information about the bdd package *}
PROTO   {* void bdd_stats(bddStat* stat) *}
DESCR   {* This function acquires information about the internal state of
           the bdd package. The status information is written into the
	   {\tt stat} argument. *}
ALSO    {* bddStat *}
*/
void bdd_stats(bddStat *s)
{
   s->produced = bddproduced;
   s->nodenum = bddnodesize;
   s->maxnodenum = bddmaxnodesize;
   s->freenodes = bddfreenum;
   s->minfreenodes = minfreenodes;
   s->varnum = bddvarnum;
   s->cachesize = cachesize;
   s->gbcnum = gbcollectnum;
}


/*************************************************************************
  Error handler
*************************************************************************/

/*
NAME    {* bdd\_errstring *}
SECTION {* kernel *}
SHORT   {* converts an error code to a string*}
PROTO   {* const char *bdd_errstring(int errorcode) *}
DESCR   {* Converts a negative error code {\tt errorcode} to a descriptive
           string that can be used for error handling. *}
RETURN  {* An error description string if {\tt e} is known, otherwise {\tt NULL}. *}
ALSO    {* bdd\_err\_hook *}
*/
const char *bdd_errstring(int e)
{
   e = abs(e);
   if (e<1 || e>BDD_ERRNUM)
      return NULL;
   return errorstrings[e-1];
}


void bdd_default_errhandler(int e)
{
   fprintf(stderr, "BDD error: %s\n", bdd_errstring(e));
   exit(1);
}


int bdd_error(int e)
{
   if (err_handler != NULL)
      err_handler(e);
   
   return e;
}


/*************************************************************************
  BDD primitives
*************************************************************************/

/*
NAME    {* bdd\_true *}
SECTION {* kernel *}
SHORT   {* returns the constant true bdd *}
PROTO   {* BDD bdd_true(void) *}
DESCR   {* This function returns the constant true bdd and can freely be
           used together with the {\tt bddtrue} and {\tt bddfalse}
	   constants. *}
RETURN  {* The constant true bdd *}
ALSO    {* bdd\_false, bddtrue, bddfalse *}
*/
BDD bdd_true(void)
{
   return 1;
}


/*
NAME    {* bdd\_false *}
SECTION {* kernel *}
SHORT   {* returns the constant false bdd *}
PROTO   {* BDD bdd_false(void) *}
DESCR   {* This function returns the constant false bdd and can freely be
           used together with the {\tt bddtrue} and {\tt bddfalse}
	   constants. *}
RETURN  {* The constant false bdd *}
ALSO    {* bdd\_true, bddtrue, bddfalse *}
*/
BDD bdd_false(void)
{
   return 0;
}


/*
NAME    {* bdd\_ithvar *}
SECTION {* kernel *}
SHORT   {* returns a bdd representing the I'th variable *}
PROTO   {* BDD bdd_ithvar(int var) *}
DESCR   {* This function is used to get a bdd representing the I'th
           variable (one node with the childs true and false). The requested
	   variable must be in the range define by {\tt bdd\_setvarnum}
	   starting with 0 being the first. For ease of use then the bdd
	   returned from {\tt bdd\_ithvar} does not have to be referenced
	   counted with a call to {\tt bdd\_addref}. *}
RETURN  {* The I'th variable on succes, otherwise the constant false bdd *}
ALSO    {* bdd\_setvarnum, bdd\_nithvar, bddtrue, bddfalse *}
*/
BDD bdd_ithvar(int var)
{
   if (var < 0  ||  var >= bddvarnum)
   {
      bdd_error(BDD_VAR);
      return bddfalse;
   }
   
   return bddvarset[var*2];
}


/*
NAME    {* bdd\_nithvar *}
SECTION {* kernel *}
SHORT   {* returns a bdd representing the negation of the I'th variable *}
PROTO   {* BDD bdd_nithvar(int var) *}
DESCR   {* This function is used to get a bdd representing the negation of
           the I'th variable (one node with the childs false and true).
	   The requested variable must be in the range define by
	   {\tt bdd\_setvarnum} starting with 0 being the first. For ease of
	   use then the bdd returned from {\tt bdd\_nithvar} does not have
	   to be referenced counted with a call to {\tt bdd\_addref}. *}
RETURN  {* The negated I'th variable on succes, otherwise the constant false bdd *}	   
ALSO    {* bdd\_setvarnum, bdd\_ithvar, bddtrue, bddfalse *}
*/
BDD bdd_nithvar(int var)
{
   if (var < 0  ||  var >= bddvarnum)
   {
      bdd_error(BDD_VAR);
      return bddfalse;
   }
   
   return bddvarset[var*2+1];
}


/*
NAME    {* bdd\_varnum *}
SECTION {* kernel *}
SHORT   {* returns the number of defined variables *}
PROTO   {* int bdd_varnum(void) *}
DESCR   {* This function returns the number of variables defined by
           a call to {\tt bdd\_setvarnum}.*}
RETURN  {* The number of defined variables *}
ALSO    {* bdd\_setvarnum, bdd\_ithvar *}
*/
int bdd_varnum(void)
{
   return bddvarnum;
}


/*
NAME    {* bdd\_var *}
SECTION {* info *}
SHORT   {* gets the variable labeling the bdd *}
PROTO   {* int bdd_var(BDD r) *}
DESCR   {* Gets the variable labeling the bdd {\tt r}. *}
RETURN  {* The variable number. *}
*/
int bdd_var(BDD root)
{
   CHECK(root);
   if (root < 2)
      return bdd_error(BDD_ILLBDD);

   return (bddlevel2var[bddnodes[root].level]);
}


/*
NAME    {* bdd\_low *}
SECTION {* info *}
SHORT   {* gets the false branch of a bdd  *}
PROTO   {* BDD bdd_low(BDD r) *}
DESCR   {* Gets the false branch of the bdd {\tt r}.  *}
RETURN  {* The bdd of the false branch *}
ALSO    {* bdd\_high *}
*/
BDD bdd_low(BDD root)
{
   CHECK(root);
   if (root < 2)
      return bdd_error(BDD_ILLBDD);

   return (bddnodes[root].low);
}


/*
NAME    {* bdd\_high *}
SECTION {* info *}
SHORT   {* gets the true branch of a bdd  *}
PROTO   {* BDD bdd_high(BDD r) *}
DESCR   {* Gets the true branch of the bdd {\tt r}.  *}
RETURN  {* The bdd of the true branch *}
ALSO    {* bdd\_low *}
*/
BDD bdd_high(BDD root)
{
   CHECK(root);
   if (root < 2)
      return bdd_error(BDD_ILLBDD);

   return (bddnodes[root].high);
}



/*************************************************************************
  Garbage collection and node referencing
*************************************************************************/

void bdd_default_gbchandler(int pre, bddGbcStat *s)
{
   if (!pre)
   {
      printf("Garbage collection #%d: %d nodes / %d free",
	     s->num, s->nodes, s->freenodes);
      printf(" / %.1fs / %.1fs total\n",
	     (float)s->time/(float)(CLOCKS_PER_SEC),
	     (float)s->sumtime/(float)CLOCKS_PER_SEC);
   }
}


void bdd_gbc(void)
{
   int *r;
   int n;
   long int c2, c1 = clock();

   if (gbc_handler != NULL)
   {
      bddGbcStat s;
      s.nodes = bddnodesize;
      s.freenodes = bddfreenum;
      s.time = 0;
      s.sumtime = gbcclock;
      s.num = gbcollectnum;
      gbc_handler(1, &s);
   }
   
   for (r=bddrefstack ; r<bddrefstacktop ; r++)
      bdd_mark(*r);

   for (n=0 ; n<bddnodesize ; n++)
   {
      if (bddnodes[n].refcou > 0)
	 bdd_mark(n);
      bddnodes[n].hash = 0;
   }
   
   bddfreepos = 0;
   bddfreenum = 0;

   for (n=2 ; n<bddnodesize ; n++)
   {
      register BddNode *node = &bddnodes[n];

      if ((node->level & MARKON)  &&  node->low != -1)
      {
	 register unsigned int hash;

	 node->level &= MARKOFF;
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

   bdd_operator_reset();

   c2 = clock();
   gbcclock += c2-c1;
   gbcollectnum++;

   if (gbc_handler != NULL)
   {
      bddGbcStat s;
      s.nodes = bddnodesize;
      s.freenodes = bddfreenum;
      s.time = c2-c1;
      s.sumtime = gbcclock;
      s.num = gbcollectnum;
      gbc_handler(0, &s);
   }
}


/*
NAME    {* bdd\_addref *}
SECTION {* kernel *}
SHORT   {* increases the reference count on a node *}
PROTO   {* BDD bdd_addref(BDD r) *}
DESCR   {* Reference counting is done on externaly referenced nodes only
           and the count for a specific node {\tt r} can and must be
	   increased using this function to avoid loosing the node in the next
	   garbage collection. *}
ALSO    {* bdd\_delref *}
RETURN  {* The BDD node {\tt r}. *}
*/
BDD bdd_addref(BDD root)
{
   if (root < 2  ||  !bddrunning)
      return root;
   if (root >= bddnodesize)
      return bdd_error(BDD_ILLBDD);
   if (bddnodes[root].low == -1)
      return bdd_error(BDD_ILLBDD);
      
   INCREF(root);
   return root;
}


/*
NAME    {* bdd\_delref *}
SECTION {* kernel *}
SHORT   {* decreases the reference count on a node *}
PROTO   {* BDD bdd_delref(BDD r) *}
DESCR   {* Reference counting is done on externaly referenced nodes only
           and the count for a specific node {\tt r} can and must be
	   decreased using this function to make it possible to reclaim the
	   node in the next garbage collection. *}
ALSO    {* bdd\_addref *}
RETURN  {* The BDD node {\tt r}. *}
*/
BDD bdd_delref(BDD root)
{
   if (root < 2  ||  !bddrunning)
      return root;
   if (root >= bddnodesize)
      return bdd_error(BDD_ILLBDD);
   if (bddnodes[root].low == -1)
      return bdd_error(BDD_ILLBDD);

   DECREF(root);
   return root;
}


/*=== RECURSIVE MARK / UNMARK ==========================================*/

void bdd_mark(int i)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];
   if (node->level & MARKON  ||  node->low == -1)
      return;
   
   node->level |= MARKON;
   
   bdd_mark(node->low);
   bdd_mark(node->high);
}


void bdd_mark_upto(int i, int level)
{
   BddNode *node = &bddnodes[i];
   
   if (i < 2)
      return;
   
   if (node->level & MARKON  ||  node->low == -1)
      return;
   
   if (node->level > level)
      return;

   node->level |= MARKON;

   bdd_mark_upto(node->low, level);
   bdd_mark_upto(node->high, level);
}


void bdd_markcount(int i, int *cou)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];
   if (node->level & MARKON  ||  node->low == -1)
      return;
   
   node->level |= MARKON;
   *cou += 1;
   
   bdd_markcount(node->low, cou);
   bdd_markcount(node->high, cou);
}


void bdd_unmark(int i)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];

   if ((node->level & MARKON) != MARKON  ||  node->low == -1)
      return;
   node->level &= MARKOFF;
   
   bdd_unmark(node->low);
   bdd_unmark(node->high);
}


void bdd_unmark_upto(int i, int level)
{
   BddNode *node = &bddnodes[i];

   if (i < 2)
      return;
   
   if (!(node->level & MARKON))
      return;
   
   node->level &= MARKOFF;
   
   if (node->level > level)
      return;

   bdd_unmark_upto(node->low, level);
   bdd_unmark_upto(node->high, level);
}


/*************************************************************************
  Unique node table functions
*************************************************************************/

int bdd_makenode(int level, int low, int high)
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
      if (bddnodes[res].level == level &&
	  bddnodes[res].low == low  &&
	  bddnodes[res].high == high)
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
      bdd_gbc();
      if ((bddfreenum*100) / bddnodesize <= minfreenodes)
      {
	 bdd_noderesize(bdd_gbc);
	 bddtryreordering = 1;
	 hash = NODEHASH(level, low, high);
      }

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
   bddfreenum--;
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


int bdd_noderesize( void(rehashfunc)(void) )
{
   BddNode *newnodes;
   int oldsize = bddnodesize;
   int n;

   if (bddnodesize >= bddmaxnodesize  &&  bddmaxnodesize > 0)
      return bdd_error(BDD_NODENUM);
   
   bddnodesize = bddnodesize << 1;

   if (bddnodesize > oldsize + bddmaxnodeincrease)
      bddnodesize = oldsize + bddmaxnodeincrease;
   
   if (bddnodesize > bddmaxnodesize  &&  bddmaxnodesize > 0)
      bddnodesize = bddmaxnodesize;

   if (resize_handler != NULL)
      resize_handler(oldsize, bddnodesize);

   newnodes = (BddNode*)realloc(bddnodes, sizeof(BddNode)*bddnodesize);
   if (newnodes == NULL)
      return bdd_error(BDD_MEMORY);
   bddnodes = newnodes;

   for (n=0 ; n<oldsize ; n++)
      bddnodes[n].hash = 0;
   for (n=oldsize ; n<bddnodesize ; n++)
   {
      bddnodes[n].refcou = 0;
      bddnodes[n].hash = 0;
      bddnodes[n].level = 0;
      bddnodes[n].low = -1;
      bddnodes[n].next = n+1;
   }
   bddnodes[bddnodesize-1].next = bddfreepos;
   bddfreepos = oldsize;

   rehashfunc();
   
   return 0;
}


/*************************************************************************
  Variable sets
*************************************************************************/

/*
NAME    {* bdd\_scanset*}
SECTION {* kernel *}
SHORT   {* returns an integer representation of a variable set *}
PROTO   {* int bdd_scanset(BDD r, int **v, int *n) *}
DESCR   {* Scans a variable set {\tt r} and copies the stored variables into
           an integer array of variable numbers. The argument {\tt v} is
	   the address of an integer pointer where the array is stored and
	   {\tt n} is a pointer to an integer where the number of elements
	   are stored. It is the users responsibility to make sure the
	   array is deallocated by a call to {\tt free(v)}. The numbers
	   returned are guaranteed to be in ascending order. *}
ALSO    {* bdd\_makeset *}
RETURN  {* Zero on success, otherwise a negative error code. *}
*/
int bdd_scanset(BDD r, int **varset, int *varnum)
{
   int n, num;

   CHECK(r);
   if (r < 2)
   {
      *varnum = 0;
      *varset = NULL;
      return 0;
   }
   
   for (n=r, num=0 ; n > 1 ; n=bddnodes[n].high)
      num++;

   if (((*varset) = (int *)malloc(sizeof(int)*num)) == NULL)
      return bdd_error(BDD_MEMORY);
   
   for (n=r, num=0 ; n > 1 ; n=bddnodes[n].high)
      (*varset)[num++] = bddlevel2var[bddnodes[n].level];

   *varnum = num;

   return 0;
}


/*
NAME    {* bdd\_makeset *}
SECTION {* kernel *}
SHORT   {* builds a BDD variable set from an integer array *}
PROTO   {* BDD bdd_makeset(int *v, int n) *}
DESCR   {* Reads a set of variable numbers from the integer array {\tt v}
           which must hold exactly {\tt n} integers and then builds a BDD
	   representing the variable set.

	   The BDD variable set is represented as the conjunction of
	   all the variables in their positive form and may just as
	   well be made that way by the user. The user should keep a
	   reference to the returned BDD instead of building it every
	   time the set is needed. *}
ALSO    {* bdd\_scanset *}
RETURN {* A BDD variable set. *} */
BDD bdd_makeset(int *varset, int varnum)
{
   int v, res=1;
   
   for (v=varnum-1 ; v>=0 ; v--)
   {
      BDD tmp;
      bdd_addref(res);
      tmp = bdd_apply(res, bdd_ithvar(varset[v]), bddop_and);
      bdd_delref(res);
      res = tmp;
   }

   return res;
}


/*************************************************************************
  Kernel reordering functions
*************************************************************************/


/*
NAME    {* bdd\_varlevel *}
SECTION {* info *}
SHORT   {* gets the level for a specific variable *}
PROTO   {* int bdd_varlevel(int var) *}
DESCR   {* Finds the global level for {\tt var} starting from level zero
           being first in the order. *}
RETURN  {* The level or a negative error code if {\tt var}
           is not allocated by a call to {\tt bdd\_setvarnum}. *}
ALSO    {* bdd\_setvarnum, bdd\_getvarnum, bdd\_reorder *}
*/
int bdd_varlevel(int var)
{
   if (var < 0  ||  var >= bddvarnum)
      return bdd_error(BDD_VAR);
   return bddvar2level[var];
}


/* EOF */
