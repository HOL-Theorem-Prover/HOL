(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)
signature bvec =
sig
    type bvec
    type const = int
	
    val bvectrue: fdd.precision -> bvec 
    val bvecfalse: fdd.precision -> bvec 
    val con: fdd.precision -> const -> bvec
    val var: fdd.precision -> bdd.varnum -> int -> bvec
    val varfdd: fdd.fddvar -> bvec
	
    val coerce: fdd.precision -> bvec -> bvec
	
    val isConst: bvec -> bool
    val getConst: bvec -> const
    val lookupConst: bvec -> const option
	
    val add: bvec * bvec -> bvec
    val sub: bvec * bvec -> bvec

    val mul     : bvec * bvec -> bvec
    val mulfixed: bvec * const -> bvec

    val div     : bvec * bvec -> bvec * bvec
    val divfixed: bvec * const -> bvec * bvec

    val divi     : bvec * bvec -> bvec
    val divifixed: bvec * const -> bvec
 
    val modu     : bvec * bvec -> bvec
    val modufixed: bvec * const -> bvec

    val shl     : bvec -> bvec -> bdd.bdd -> bvec
    val shlfixed: bvec -> int -> bdd.bdd -> bvec

    val shr     : bvec -> bvec -> bdd.bdd -> bvec
    val shrfixed: bvec -> int -> bdd.bdd -> bvec
	
    val lth: bvec * bvec -> bdd.bdd
    val lte: bvec * bvec -> bdd.bdd
    val gth: bvec * bvec -> bdd.bdd
    val gte: bvec * bvec -> bdd.bdd
    val equ: bvec * bvec -> bdd.bdd
    val neq: bvec * bvec -> bdd.bdd
end

(* Structure bvec implements BuDDy's bvec functions.

  Documentation is not available currently.  see the Buddy
  documentation.


  The following table shows how ML types and values in this modules
  relates to C types and function declarations in bvec.h:
  
  MuDDy       BuDDy                   Comment
  -----------------------------------------------------------------
  Types:
  bvec        BVEC
  const       int
  
  Values:
  ?	      bvec_copy
  bvectrue    bvec_true
  bvecfalse   bvec_false
  con	      bvec_con
  var	      bvec_var
  varfdd      bvec_varfdd
  ?	      bvec_varvec
  coerce      bvec_coerce
  isConst     bvec_isconst
  getConst    bvec_val
  lookupConst ?                       Uses isConst and getConst
  ?	      bvec_free
  ?	      bvec_addref
  ?	      bvec_delref
  ?	      bvec_map1
  ?	      bvec_map2
  ?	      bvec_map3
  add	      bvec_add
  sub	      bvec_sub
  mul	      bvec_mul
  div         bvec_div
  divi	      bvec_div                (See also modu)
  modu	      bvec_div                (See also divi)
  shl	      bvec_shl
  shr	      bvec_shr
  lth	      bvec_lth
  lte	      bvec_lte
  gth	      bvec_gth
  gte	      bvec_gte
  equ	      bvec_equ
  neq	      bvec_neq
  
*)
