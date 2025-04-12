structure integerRingLib :> integerRingLib =
struct

open HolKernel boolLib bossLib liteLib

open integerTheory intSimps intSyntax intReduce Normalizer Grobner Canon
     hurdUtils mesonLib tautLib

open integerRingTheory

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars $ valOf $ grammarDB {thyname="integer"}
end

open Parse

val ERR = mk_HOL_ERR "intLib"
fun failwith function = raise ERR function ""

val num_to_int = intSyntax.int_injection
val int_0 = intSyntax.zero_tm
val int_1 = intSyntax.one_tm
fun is_closed_int t =
  tmem t [int_0,int_1] orelse
    (is_comb t andalso rator t ~~ num_to_int andalso
     numSyntax.is_numeral (rand t))

val _ = EVAL_ringLib.declare_ring
    { RingThm = int_ring_thms,
      IsConst = is_closed_int,
      Rewrites = [int_rewrites, EVAL_numRingTheory.num_rewrites] }

(* dealing with subtraction: *)
val PRE_CONV = REWRITE_CONV[int_sub]

val POST_CONV =
  REWRITE_CONV[GSYM INT_NEG_MINUS1] THENC
  REWRITE_CONV[GSYM INT_NEG_LMUL, GSYM int_sub]


val INT_RING_CONV = PRE_CONV THENC EVAL_ringLib.RING_CONV THENC POST_CONV
val INT_NORM_CONV = PRE_CONV THENC EVAL_ringLib.RING_NORM_CONV THENC POST_CONV

val INT_RING_TAC = CONV_TAC INT_RING_CONV
val INT_NORM_TAC = CONV_TAC INT_NORM_CONV

val INT_RING_RULE = CONV_RULE INT_RING_CONV
val INT_NORM_RULE = CONV_RULE INT_NORM_CONV

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer (code below are ported from HOL-Light)         *)
(* ------------------------------------------------------------------------- *)

val (_,_,_,_,_,INT_POLY_CONV) =
  SEMIRING_NORMALIZERS_CONV INT_POLY_CONV_sth INT_POLY_CONV_rth
    (is_int_literal,INT_ADD_CONV,INT_MUL_CONV,INT_POW_CONV)
    (fn u => fn t => Term.compare(u,t) = LESS)

(* ------------------------------------------------------------------------- *)
(* Instantiate the ring and ideal procedures.                                *)
(* ------------------------------------------------------------------------- *)

local
  val dest_intconst = Arbrat.fromAInt o int_of_term
  val mk_intconst = term_of_int o Arbrat.toAInt
  val (pure,ideal) =
    RING_AND_IDEAL_CONV
      (dest_intconst,mk_intconst,INT_EQ_CONV,
       negate_tm, plus_tm, minus_tm,
       genvar bool, mult_tm, genvar bool, exp_tm,
       INT_INTEGRAL,TRUTH,INT_POLY_CONV)
in
  val INT_RING = pure
  fun int_ideal_cofactors tms tm =
    if forall (fn t => type_of t = int_ty) (tm::tms)
    then ideal tms tm
    else
      failwith "int_ideal_cofactors: not all terms have type :int"
end

end;
