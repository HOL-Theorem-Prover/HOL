structure integerRingLib :> integerRingLib =
struct

open HolKernel boolLib bossLib liteLib;

open integerTheory intSimps intSyntax intReduce Normalizer Grobner Canon
     hurdUtils mesonLib tautLib;

open integerRingTheory;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars integer_grammars
end

open Parse;

val ERR = mk_HOL_ERR "intLib";
fun failwith function = raise (ERR function "");

val num_to_int = intSyntax.int_injection;
val int_0 = intSyntax.zero_tm
val int_1 = intSyntax.one_tm
fun is_closed_int t =
  tmem t [int_0,int_1] orelse
    (is_comb t andalso rator t ~~ num_to_int andalso
     numSyntax.is_numeral (rand t));

val _ = EVAL_ringLib.declare_ring
    { RingThm = int_ring_thms,
      IsConst = is_closed_int,
      Rewrites = [int_rewrites, EVAL_numRingTheory.num_rewrites] };

(* dealing with subtraction: *)
val PRE_CONV = REWRITE_CONV[int_sub]

val POST_CONV =
  REWRITE_CONV[GSYM INT_NEG_MINUS1] THENC
  REWRITE_CONV[GSYM INT_NEG_LMUL, GSYM int_sub]
;

val INT_RING_CONV = PRE_CONV THENC EVAL_ringLib.RING_CONV THENC POST_CONV;
val INT_NORM_CONV = PRE_CONV THENC EVAL_ringLib.RING_NORM_CONV THENC POST_CONV;

val INT_RING_TAC = CONV_TAC INT_RING_CONV
val INT_NORM_TAC = CONV_TAC INT_NORM_CONV

val INT_RING_RULE = CONV_RULE INT_RING_CONV
val INT_NORM_RULE = CONV_RULE INT_NORM_CONV

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer (code below are ported from HOL-Light)         *)
(* ------------------------------------------------------------------------- *)

local
  val sth = prove
   (“(!x y z. x + (y + z) = (x + y) + z :int) /\
     (!x y. x + y = y + x :int) /\
     (!x. &0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z :int) /\
     (!x y. x * y = y * x :int) /\
     (!x. &1 * x = x :int) /\
     (!(x :int). &0 * x = &0) /\
     (!x y z. x * (y + z) = x * y + x * z :int) /\
     (!(x :int). x ** 0 = &1) /\
     (!(x :int) n. x ** (SUC n) = x * (x ** n))”,
    REWRITE_TAC [INT_POW, INT_ADD_ASSOC, INT_MUL_ASSOC, INT_ADD_LID,
                 INT_MUL_LZERO, INT_MUL_LID, INT_LDISTRIB] THEN
    REWRITE_TAC [Once INT_ADD_SYM, Once INT_MUL_SYM]);
  val rth = prove
   (“(!x. -x = -(&1) * x :int) /\
     (!x y. x - y = x + -(&1) * y :int)”,
    REWRITE_TAC [INT_MUL_LNEG, INT_MUL_LID, int_sub]);
  val is_semiring_constant = is_int_literal
  and SEMIRING_ADD_CONV = INT_ADD_CONV
  and SEMIRING_MUL_CONV = INT_MUL_CONV
  and SEMIRING_POW_CONV = INT_POW_CONV;
  fun term_lt u t = (Term.compare(u,t) = LESS);
  val (_,_,_,_,_,POLY_CONV) =
    SEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
     term_lt
in
  val INT_POLY_CONV = POLY_CONV;
end;

(* ------------------------------------------------------------------------- *)
(* Instantiate the ring and ideal procedures.                                *)
(* ------------------------------------------------------------------------- *)

local
  val INT_INTEGRAL = prove
   (“(!(x :int). &0 * x = &0) /\
     (!x y (z :int). (x + y = x + z) <=> (y = z)) /\
     (!w x y (z :int). (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))”,
    REWRITE_TAC[INT_MUL_LZERO, INT_EQ_LADD] THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
    REWRITE_TAC[GSYM INT_ENTIRE] THEN
    rpt GEN_TAC \\
    Suff ‘w * y + x * z - (w * z + x * y) = (w - x) * (y - z :int)’
    >- (Rewr' >> REWRITE_TAC []) \\
    REWRITE_TAC [INT_ADD2_SUB2] \\
    REWRITE_TAC [GSYM INT_SUB_LDISTRIB] \\
   ‘x * (z - y) = -x * (y - z :int)’
      by (REWRITE_TAC [INT_MUL_LNEG, INT_SUB_LDISTRIB, INT_NEG_SUB]) \\
    POP_ORW \\
    REWRITE_TAC [GSYM INT_RDISTRIB, GSYM int_sub]);
  val dest_intconst = Arbrat.fromAInt o int_of_term;
  val mk_intconst = term_of_int o Arbrat.toAInt;
  val (pure,ideal) =
    RING_AND_IDEAL_CONV
      (dest_intconst,mk_intconst,INT_EQ_CONV,
       negate_tm, plus_tm, minus_tm,
       genvar bool, mult_tm, genvar bool, exp_tm,
       INT_INTEGRAL,TRUTH,INT_POLY_CONV)
in
  val INT_RING = pure;
  fun int_ideal_cofactors tms tm =
      if forall (fn t => type_of t = int_ty) (tm::tms)
      then ideal tms tm
      else
        failwith "int_ideal_cofactors: not all terms have type :int"
end;

end;
