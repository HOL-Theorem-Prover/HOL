local 

  open bdd fdd

in

  type bvec
  type const = int

  val bvectrue: precision -> bvec 
  val bvecfalse: precision -> bvec 
  val con: precision -> const -> bvec
  val var: precision -> varnum -> int -> bvec
  val varfdd: fddvar -> bvec

  val coerce: precision -> bvec -> bvec

  val isConst: bvec -> bool
  val getConst: bvec -> const
  val lookupConst: bvec -> const option


  val add: bvec * bvec -> bvec
  val sub: bvec * bvec -> bvec
  val mul: bvec * const -> bvec
  val divi: bvec * const -> bvec
  val modu: bvec * const -> bvec
  val shl: bvec -> int -> bdd -> bvec
  val shr: bvec -> int -> bdd -> bvec

  val lth: bvec * bvec -> bdd
  val lte: bvec * bvec -> bdd
  val gth: bvec * bvec -> bdd
  val gte: bvec * bvec -> bdd
  val equ: bvec * bvec -> bdd
  val neq: bvec * bvec -> bdd

end

(* bvec 

Implements BuDDy's bvec functions.

The following table shows how ML types and values in this modules
relates to C types and function declarations in bvec.h:

MuDDy       BuDDy                   Comment
-----------------------------------------------------------------
Types:
bvec        BVEC
const       int

Values:
?	    bvec_copy
bvectrue    bvec_true
bvecfalse   bvec_false
con	    bvec_con
var	    bvec_var
varfdd	    bvec_varfdd
?	    bvec_varvec
coerce	    bvec_coerce
isConst	    bvec_isconst
getConst    bvec_val
lookupConst ?                       Uses isConst and getConst
?	    bvec_free
?	    bvec_addref
?	    bvec_delref
?	    bvec_map1
?	    bvec_map2
?	    bvec_map3
add	    bvec_add
sub	    bvec_sub
mul	    bvec_mul
divi	    bvec_div               (See also modu)
modu	    bvec_div               (See also divi)
shl	    bvec_shl
shr	    bvec_shr
lth	    bvec_lth
lte	    bvec_lte
gth	    bvec_gth
gte	    bvec_gte
equ	    bvec_equ
neq	    bvec_neq

*)
