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
  FILE:  bvec.h
  DESCR: Boolean (BDD) vector handling
  AUTH:  Jorn Lind
  DATE:  (C) may 1999
*************************************************************************/

#ifndef _BVEC_H
#define _BVEC_H

#include "fdd.h"

   /* Boolean (BDD) vector */
/*
NAME    {* bvec *}
SECTION {* bvec *}
SHORT   {* A boolean vector *}
PROTO   {* typedef struct s_bvec
{
   int bitnum;
   BDD *bitvec;
} BVEC;

typedef BVEC bvec; *}
DESCR   {* This data structure is used to store boolean vectors. The field
           {\tt bitnum} is the number of elements in the vector and the
	   field {\tt bitvec} contains the actual BDDs in the vector.
	   The C++ version of {\tt bvec} is documented at the beginning of
	   this document *}
*/
typedef struct s_bvec
{
   int bitnum;
   BDD *bitvec;
} BVEC;

#ifndef CPLUSPLUS
typedef BVEC bvec;
#endif


#ifdef CPLUSPLUS
extern "C" {
#endif
   
   /* Prototypes for bvec.c */
extern BVEC bvec_copy(BVEC v);
extern BVEC bvec_true(int bitnum);
extern BVEC bvec_false(int bitnum);
extern BVEC bvec_con(int bitnum, int val);
extern BVEC bvec_var(int bitnum, int offset, int step);
extern BVEC bvec_varfdd(int var);
extern BVEC bvec_varvec(int bitnum, int *var);
extern BVEC bvec_coerce(int bitnum, BVEC v);
extern int  bvec_isconst(BVEC e);   
extern int  bvec_val(BVEC e);   
extern void bvec_free(BVEC v);
extern BVEC bvec_addref(BVEC v);
extern BVEC bvec_delref(BVEC v);
extern BVEC bvec_map1(BVEC a, BDD (*fun)(BDD));
extern BVEC bvec_map2(BVEC a, BVEC b, BDD (*fun)(BDD,BDD));
extern BVEC bvec_map3(BVEC a, BVEC b, BVEC c, BDD (*fun)(BDD,BDD,BDD));
extern BVEC bvec_add(BVEC left, BVEC right);
extern BVEC bvec_sub(BVEC left, BVEC right);
extern BVEC bvec_mul(BVEC e, int c);
extern int  bvec_div(BVEC e, int c, BVEC *res, BVEC *rem);
extern BVEC bvec_shl(BVEC e, int pos, BDD c);
extern BVEC bvec_shr(BVEC e, int pos, BDD c);
extern BDD  bvec_lth(BVEC left, BVEC right);
extern BDD  bvec_lte(BVEC left, BVEC right);
extern BDD  bvec_gth(BVEC left, BVEC right);
extern BDD  bvec_gte(BVEC left, BVEC right);
extern BDD  bvec_equ(BVEC left, BVEC right);
extern BDD  bvec_neq(BVEC left, BVEC right);

#ifdef CPLUSPLUS
}
#endif


/*************************************************************************
   If this file is included from a C++ compiler then the following
   classes, wrappers and hacks are supplied.
*************************************************************************/
#ifdef CPLUSPLUS

/*=== User BVEC class ==================================================*/

class bvec
{
 public:

   bvec(void)             { roots.bitvec=NULL; roots.bitnum=0; }
   bvec(int bitnum)       { roots=bvec_false(bitnum); }
   bvec(const bvec &v)    { roots=bvec_copy(v.roots); }
   ~bvec(void)            { bvec_free(roots); }

   void set(int i, const bdd &b);
   bdd operator[](int i)  const { return roots.bitvec[i]; }
   int bitnum(void) const       { return roots.bitnum; }
   int empty(void) const        { return roots.bitnum==0; }
   bvec operator=(const bvec &src);
   
private:
   BVEC roots;

   bvec(const BVEC &v) { roots=v; } /* NOTE: Must be a shallow copy! */

   friend bvec bvec_truepp(int bitnum);
   friend bvec bvec_falsepp(int bitnum);
   friend bvec bvec_conpp(int bitnum, int val);
   friend bvec bvec_varpp(int bitnum, int offset, int step);
   friend bvec bvec_varfddpp(int var);
   friend bvec bvec_varvecpp(int bitnum, int *var);
   friend bvec bvec_coerce(int bitnum, const bvec &v);
   friend int  bvec_isconst(const bvec &e);   
   friend int  bvec_val(const bvec &e);   
   friend bvec bvec_copy(const bvec &v);
   friend bvec bvec_map1(const bvec &a,
			 bdd (*fun)(const bdd &));
   friend bvec bvec_map2(const bvec &a, const bvec &b,
			 bdd (*fun)(const bdd &, const bdd &));
   friend bvec bvec_map3(const bvec &a, const bvec &b, const bvec &c,
			 bdd (*fun)(const bdd &, const bdd &, const bdd &));
   friend bvec bvec_add(const bvec &left, const bvec &right);
   friend bvec bvec_sub(const bvec &left, const bvec &right);
   friend bvec bvec_mul(const bvec &e, int c);
   friend int  bvec_div(const bvec &e, int c, bvec &res, bvec &rem);
   friend bvec bvec_shl(const bvec &e, int pos, const bdd &c);
   friend bvec bvec_shr(const bvec &e, int pos, const bdd &c);
   friend bdd  bvec_lth(const bvec &left, const bvec &right);
   friend bdd  bvec_lte(const bvec &left, const bvec &right);
   friend bdd  bvec_gth(const bvec &left, const bvec &right);
   friend bdd  bvec_gte(const bvec &left, const bvec &right);
   friend bdd  bvec_equ(const bvec &left, const bvec &right);
   friend bdd  bvec_neq(const bvec &left, const bvec &right);

public:
   bvec operator&(const bvec &a) const { return bvec_map2(*this, a, bdd_and); }
   bvec operator^(const bvec &a) const { return bvec_map2(*this, a, bdd_xor); }
   bvec operator|(const bvec &a) const { return bvec_map2(*this, a, bdd_or); }
   bvec operator!(void) const          { return bvec_map1(*this, bdd_not); }
   bvec operator<<(int a)   const      { return bvec_shl(*this,a,bddfalse); }
   bvec operator>>(int a)   const      { return bvec_shr(*this,a,bddfalse); }
   bvec operator+(const bvec &a) const { return bvec_add(*this, a); }
   bvec operator-(const bvec &a) const { return bvec_sub(*this, a); }
   bvec operator*(int a)    const      { return bvec_mul(*this, a); }
   bdd operator<(const bvec &a) const  { return bvec_lth(*this, a); }
   bdd operator<=(const bvec &a) const { return bvec_lte(*this, a); }
   bdd operator>(const bvec &a) const  { return bvec_gth(*this, a); }
   bdd operator>=(const bvec &a) const { return bvec_gte(*this, a); }
   bdd operator==(const bvec &a) const { return bvec_equ(*this, a); }
   bdd operator!=(const bvec &a) const { return bvec_neq(*this, a); }
};


inline bvec bvec_truepp(int bitnum)
{ return bvec_true(bitnum); }

inline bvec bvec_falsepp(int bitnum)
{ return bvec_false(bitnum); }

inline bvec bvec_conpp(int bitnum, int val)
{ return bvec_con(bitnum, val); }

inline bvec bvec_varpp(int bitnum, int offset, int step)
{ return bvec_var(bitnum, offset, step); }

inline bvec bvec_varfddpp(int var)
{ return bvec_varfdd(var); }

inline bvec bvec_varvecpp(int bitnum, int *var)
{ return bvec_varvec(bitnum, var); }

inline bvec bvec_coerce(int bitnum, const bvec &v)
{ return bvec_coerce(bitnum, v.roots); }

inline int  bvec_isconst(const bvec &e)
{ return bvec_isconst(e.roots); }

inline int  bvec_val(const bvec &e)
{ return bvec_val(e.roots); }

inline bvec bvec_copy(const bvec &v)
{ return bvec_copy(v.roots); }

inline bvec bvec_add(const bvec &left, const bvec &right)
{ return bvec_add(left.roots, right.roots); }

inline bvec bvec_sub(const bvec &left, const bvec &right)
{ return bvec_sub(left.roots, right.roots); }

inline bvec bvec_mul(const bvec &e, int c)
{ return bvec_mul(e.roots, c); }

inline bvec bvec_shl(const bvec &e, int pos, const bdd &c)
{ return bvec_shl(e.roots, pos, c.root); }

inline bvec bvec_shr(const bvec &e, int pos, const bdd &c)
{ return bvec_shr(e.roots, pos, c.root); }

inline bdd  bvec_lth(const bvec &left, const bvec &right)
{ return bvec_lth(left.roots, right.roots); }

inline bdd  bvec_lte(const bvec &left, const bvec &right)
{ return bvec_lte(left.roots, right.roots); }

inline bdd  bvec_gth(const bvec &left, const bvec &right)
{ return bvec_gth(left.roots, right.roots); }

inline bdd  bvec_gte(const bvec &left, const bvec &right)
{ return bvec_gte(left.roots, right.roots); }

inline bdd  bvec_equ(const bvec &left, const bvec &right)
{ return bvec_equ(left.roots, right.roots); }

inline bdd  bvec_neq(const bvec &left, const bvec &right)
{ return bvec_neq(left.roots, right.roots); }


   /* Hack to allow for overloading */
#define bvec_var(a,b,c)  bvec_varpp(a,b,c)
#define bvec_varfdd(a)   bvec_varfddpp(a)
#define bvec_varvec(a,b) bvec_varvecpp(a,b)
#define bvec_true(a)     bvec_truepp(a)
#define bvec_false(a)    bvec_falsepp(a)
#define bvec_con(a,b)    bvec_conpp((a),(b))

   
#endif /* CPLUSPLUS */

#endif /* _BVEC_H */

/* EOF */
