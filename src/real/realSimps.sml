(* ------------------------------------------------------------------------- *)
(* A real simpset (includes Peano arithmetic and pairs).                     *)
(* ------------------------------------------------------------------------- *)

structure realSimps :> realSimps =
struct

open HolKernel boolLib realTheory simpLib

val arith_ss = boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ numSimps.ARITH_ss

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

val real_ac_SS = simpLib.SIMPSET {
  ac = [(SPEC_ALL REAL_ADD_ASSOC, SPEC_ALL REAL_ADD_SYM),
        (SPEC_ALL REAL_MUL_ASSOC, SPEC_ALL REAL_MUL_SYM)],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = [],
  congs = []};


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

val div_rats = transform [(x, true), (y, false), (u, true), (v, false)] div_rat
val div_ratls = transform [(x, true), (y, false), (z, false)] div_ratl
val div_ratrs = transform [(x, true), (z, false), (y, true)] div_ratr

val max_ints = transform [(x, true), (y, true)] (SPEC_ALL max_def)
val min_ints = transform [(x, true), (y, true)] (SPEC_ALL min_def)
val max_rats =
    transform [(x, true), (y, false), (u, true), (v, false)]
              (SPECL [realSyntax.mk_div(x,y), realSyntax.mk_div(u,v)] max_def)
val max_ratls =
    transform [(x, true), (y, false), (u, true)]
              (SPECL [realSyntax.mk_div(x,y), u] max_def)
val max_ratrs =
    transform [(x, true), (y, false), (u, true)]
              (SPECL [u, realSyntax.mk_div(x,y)] max_def)
val min_rats =
    transform [(x, true), (y, false), (u, true), (v, false)]
              (SPECL [realSyntax.mk_div(x,y), realSyntax.mk_div(u,v)] min_def)
val min_ratls =
    transform [(x, true), (y, false), (u, true)]
              (SPECL [realSyntax.mk_div(x,y), u] min_def)
val min_ratrs =
    transform [(x, true), (y, false), (u, true)]
              (SPECL [u, realSyntax.mk_div(x,y)] min_def)


val op_rwts = [mult_ints, add_ints, eq_ints, REAL_DIV_LZERO] @ neg_ths @
              add_rats @ add_ratls @ add_ratrs @
              mult_rats @ mult_ratls @ mult_ratrs @
              sub1 @ sub2 @ sub3 @ sub4 @ div_rats @ div_ratls @ div_ratrs @
              max_ratls @ max_ratrs @ max_rats @ max_ints @
              min_ratls @ min_ratrs @ min_rats @ min_ints


fun nat2nat th = let
  val simp = REWRITE_RULE [REAL_INJ, REAL_NEGNEG, REAL_NEG_EQ0, num_eq_0]
  val th0 =
    map simp ([INST [``n:num`` |-> ``NUMERAL (NUMERAL_BIT1 n)``] th,
               INST [``n:num`` |-> ``NUMERAL (NUMERAL_BIT2 n)``] th])
in
  List.concat
    (map (fn th => map simp
                       [INST [``m:num`` |-> ``NUMERAL(NUMERAL_BIT1 m)``] th,
                        INST [``m:num`` |-> ``NUMERAL(NUMERAL_BIT2 m)``] th])
         th0)
end

val lt_rats = nat2nat lt_rat
val lt_ratls = nat2nat lt_ratl
val lt_ratrs = nat2nat lt_ratr

val le_rats = nat2nat le_rat
val le_ratls = nat2nat le_ratl
val le_ratrs = nat2nat le_ratr

val eq_rats = transform [(x, true), (y, false), (u, true), (v, false)] eq_rat
val eq_ratls = transform [(x, true), (y, false), (z, true)] eq_ratl
val eq_ratrs = transform [(x, true), (y, false), (z, true)] eq_ratr

val real_gts = transform [(x, true), (y, true)] (SPEC_ALL real_gt)
val real_ges = transform [(x, true), (y, true)] (SPEC_ALL real_ge)

val rel_rwts = [eq_ints, le_int, lt_int] @ eq_rats @ eq_ratls @ eq_ratrs @
               lt_rats @ lt_ratls @ lt_ratrs @ le_rats @ le_ratrs @ le_ratls @
               real_gts @ real_ges


val rwts = op_rwts @ rel_rwts

val REAL_REDUCE_ss = simpLib.rewrites rwts

val real_ss = arith_ss ++ real_SS ++ REAL_REDUCE_ss

val real_ac_ss = real_ss ++ real_ac_SS

fun real_compset () = let
  open computeLib
  val compset = reduceLib.num_compset()
  val _ = add_thms rwts compset
in
  compset
end

(* add real calculation facilities to global functionality *)
val _ = let open computeLib in add_funs rwts end

val _ = BasicProvers.augment_srw_ss [REAL_REDUCE_ss]



end;
