(* ------------------------------------------------------------------------- *)
(* A real simpset (includes Peano arithmetic and pairs).                     *)
(* ------------------------------------------------------------------------- *)

structure realSimps :> realSimps =
struct

open HolKernel boolLib realTheory;

val arith_ss =
  simpLib.++
    (simpLib.++(boolSimps.bool_ss, pairSimps.PAIR_ss),numSimps.ARITH_ss);

val real_SS = simpLib.SIMPSET
  {ac = [],
   congs = [],
   convs = [],
   dprocs = [],
   filter = NONE,
   rewrs = [(* addition *)
            REAL_ADD_LID, REAL_ADD_RID,
            (* subtraction *)
            REAL_SUB_REFL, REAL_SUB_RZERO,
            (* multiplication *)
            REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_LZERO, REAL_MUL_RZERO,
            (* division *)
            REAL_OVER1, REAL_DIV_ADD,
            (* less than or equal *)
            REAL_LE_REFL, REAL_LE_01, REAL_LE_RADD,
            (* less than *)
            REAL_LT_01, REAL_LT_INV_EQ,
            (* pushing out negations *)
            REAL_NEGNEG, REAL_LE_NEG2, REAL_SUB_RNEG, REAL_NEG_SUB,
            REAL_MUL_RNEG, REAL_MUL_LNEG,
            (* cancellations *)
            REAL_SUB_ADD2, REAL_MUL_SUB1_CANCEL, REAL_MUL_SUB2_CANCEL,
            REAL_LE_SUB_CANCEL2, REAL_ADD_SUB, REAL_SUB_ADD, REAL_ADD_SUB_ALT,
            REAL_SUB_SUB2,
            (* halves *)
            REAL_LT_HALF1, REAL_HALF_BETWEEN, REAL_NEG_HALF,
            REAL_DIV_DENOM_CANCEL2, REAL_DIV_INNER_CANCEL2,
            REAL_DIV_OUTER_CANCEL2, REAL_DIV_REFL2,
            (* thirds *)
            REAL_NEG_THIRD, REAL_DIV_DENOM_CANCEL3, REAL_THIRDS_BETWEEN,
            REAL_DIV_INNER_CANCEL3, REAL_DIV_OUTER_CANCEL3, REAL_DIV_REFL3,
            (* injections to the naturals *)
            REAL_INJ, REAL_ADD, REAL_LE, REAL_LT, REAL_MUL,
            (* pos *)
            REAL_POS_EQ_ZERO, REAL_POS_POS, REAL_POS_INFLATE,
            REAL_POS_LE_ZERO,
            (* min *)
            REAL_MIN_REFL, REAL_MIN_LE1, REAL_MIN_LE2, REAL_MIN_ADD,
            REAL_MIN_SUB,
            (* max *)
            REAL_MAX_REFL, REAL_LE_MAX1, REAL_LE_MAX2, REAL_MAX_ADD,
            REAL_MAX_SUB]};

val real_ss = simpLib.++ (arith_ss, real_SS);

val real_ac_SS = simpLib.SIMPSET {
  ac = [(SPEC_ALL REAL_ADD_ASSOC, SPEC_ALL REAL_ADD_SYM),
        (SPEC_ALL REAL_MUL_ASSOC, SPEC_ALL REAL_MUL_SYM)],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = [],
  congs = []};

val real_ac_ss = simpLib.++ (real_ss, real_ac_SS);

(* ----------------------------------------------------------------------
    simple calculation over the reals
   ---------------------------------------------------------------------- *)

(* there are a whole bunch of theorems at the bottom of realScript designed
   to be used as calculational rewrites, but they are too general: with
   a rewrite with a LHS such as x * (y/z), you will get far too many rewrites
   happening.  Instead we need to specialise these variables so that the
   rewrites only apply when the variables look as if they're literals.

   To do this, we specialise with terms of the form &v and ~&v.
   We could go "the whole hog" here and further specialise the v's to be
   one of either NUMERAL (NUMERAL_BIT1 v), NUMERAL (NUMERAL_BIT2 v) or 0,
   but this seems over the top.
*)

val num_eq_0 = prove(
  ``~(NUMERAL (NUMERAL_BIT1 n) = 0) /\ ~(NUMERAL (NUMERAL_BIT2 n) = 0)``,
  REWRITE_TAC [numeralTheory.numeral_distrib, numeralTheory.numeral_eq]);

fun two_nats  rv nv th = let
  open realSyntax numSyntax
  val nb1_t = mk_injected (mk_comb(numeral_tm, mk_comb(numeral_bit1, nv)))
  val nb2_t = mk_injected (mk_comb(numeral_tm, mk_comb(numeral_bit2, nv)))
in
  [INST [rv |-> nb1_t] th, INST [rv |-> nb2_t] th]
end

fun posnegonly rv nv th = let
  open realSyntax
  val injected = mk_injected nv
in
  [INST [rv |-> injected] th, INST [rv |-> mk_negated injected] th]
end


fun transform vs th = let
  val simp = REWRITE_RULE [REAL_INJ, REAL_NEGNEG, REAL_NEG_EQ0, num_eq_0]
  open realSyntax
  val nvs = map (fn (t,_) => mk_var(#1 (dest_var t), numSyntax.num)) vs

  fun recurse vs nvs th =
      if null vs then [th]
      else let
          val (v,split) = hd vs
          val nv = hd nvs
          val f = if split then posnegonly else two_nats
          val newths = map simp (f v nv th)
        in
          List.concat (map (recurse (tl vs) (tl nvs)) newths)
        end
in
  recurse vs nvs th
end

val x = mk_var("x", realSyntax.real_ty)
val y = mk_var("y", realSyntax.real_ty)
val z = mk_var("z", realSyntax.real_ty)
val u = mk_var("u", realSyntax.real_ty)
val v = mk_var("v", realSyntax.real_ty)

val add_rats = transform [(x, true), (y, false), (u, true), (v, false)] add_rat
val add_ratls = transform [(x, true), (y,false), (z, true)] add_ratl
val add_ratrs = transform [(x, true), (y, true), (z, false)] add_ratr

val mult_rats =
    transform [(x,true), (y, false), (u, true), (v, false)] mult_rat
val mult_ratls = transform [(x, true), (y, false), (z, true)] mult_ratl
val mult_ratrs = transform [(x, true), (y, true), (z, false)] mult_ratr

val neg_ths = transform [(y, false)] neg_rat

val sub1 = SPECL [realSyntax.mk_div(x,y), realSyntax.mk_div(u,v)] real_sub
val sub1 = transform [(x, true), (y, false), (u, true), (v, false)] sub1
val sub2 = SPECL [x, realSyntax.mk_div(u,v)] real_sub
val sub2 = transform [(x, true), (u, true), (v, false)] sub2
val sub3 = SPECL [realSyntax.mk_div(x,y), z] real_sub
val sub3 = transform [(x, true), (y, false), (z, true)] sub3
val sub4 = transform [(x, true), (y, true)] (SPEC_ALL real_sub)

val eq_rats = transform [(x, true), (y, false), (u, true), (v, false)] eq_rat
val eq_ratls = transform [(x, true), (y, false), (z, true)] eq_ratl

val rwts = [mult_ints, add_ints, eq_ints, REAL_DIV_LZERO] @ neg_ths @
           add_rats @ add_ratls @ add_ratrs @
           mult_rats @ mult_ratls @ mult_ratrs @
           sub1 @ sub2 @ sub3 @ sub4 @
           eq_rats @ eq_ratls





end;
