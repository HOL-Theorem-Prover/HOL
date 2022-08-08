(* ========================================================================= *)
(* Calculation with rational-valued reals. (HOL-Light's calc_rat.ml)         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                                                                           *)
(*       Ported to HOL4 by Chun Tian, May 2022                               *)
(* ========================================================================= *)

structure RealField :> RealField =
struct

open HolKernel Parse boolLib bossLib;

open prim_recTheory arithmeticTheory numLib reduceLib tautLib liteLib;
open realaxTheory realTheory realSyntax RealArith jrhUtils normalForms;
open realSimps

open Sub_and_cond Normalizer Grobner;

(* Fix the grammar used by this file *)
local
val x = mk_var("x", numSyntax.num)
val y = mk_var("y", numSyntax.num)
in
(* In HOL-Light this was a definition but in HOL4 we use markerTheory
     DECIMAL maps to \x y. unint(&x / &y)
*)
val decimal_tm =
list_mk_abs([x, y],
            mk_comb (mk_thy_const{Thy = "marker", Name = "unint",
                                  Ty = real_ty --> real_ty},
                     mk_div (mk_injected x, mk_injected y)))
end
structure Parse = struct
  open Parse
  local val (rtyg, rtmg0) = realTheory.real_grammars
        val rtmg = term_grammar.fupdate_overload_info
                     (Overload.add_overloading("DECIMAL", decimal_tm))
                     rtmg0
  in
  val (Type,Term) = parse_from_grammars (rtyg, rtmg)
  end
end

open Parse;

(* clarify some conflicting library functions *)
val assert      = Lib.assert;
val is_binop    = liteLib.is_binop;
val SKOLEM_CONV = Canon_Port.SKOLEM_CONV;

(* for HOL-Light compatibilities  *)
val REAL_INV_MUL = REAL_INV_MUL';
val REAL_INV_DIV = REAL_INV_DIV';
val NNF_CONV = normalForms.NNFD_CONV;
val NUM_REDUCE_CONV = reduceLib.REDUCE_CONV;

(* clarify some primitive real theorem names involving real_0 and real_1 *)
val REAL_10         = realTheory.REAL_10;
val REAL_ADD_LID    = realTheory.REAL_ADD_LID;
val REAL_ADD_LINV   = realTheory.REAL_ADD_LINV;
val REAL_INV_0      = realTheory.REAL_INV_0;
val REAL_LT_IADD    = realTheory.REAL_LT_IADD;
val REAL_LT_MUL     = realTheory.REAL_LT_MUL;
val REAL_MUL_LID    = realTheory.REAL_MUL_LID;
val REAL_MUL_LINV   = realTheory.REAL_MUL_LINV;
val REAL_SUP_ALLPOS = realTheory.REAL_SUP_ALLPOS;

fun failwith s = raise mk_HOL_ERR "RealField" "?" s

(* set verbose level (of REAL_LINEAR_PROVER) to nothing for internal loading *)
val _ = RealArith.verbose_level := 0;

(* ------------------------------------------------------------------------- *)
(* Syntax operations on integer constants of type “:real”.                   *)
(* ------------------------------------------------------------------------- *)

(* NOTE: HOL-Light's gcd_num function accepts negative numbers, but their gcd
   is always positive. It looks like having abs first, then gcd. *)
local open Arbint in
fun gcd a b = fromNat (Arbnum.gcd (toNat (abs a), toNat (abs b)))
end (* local *)

type aint = Arbint.int

(* ------------------------------------------------------------------------- *)
(* Create trivial rational from integer or decimal, and postconvert back.    *)
(* ------------------------------------------------------------------------- *)

(* |- !x. unint x = x *)
val DECIMAL = markerTheory.unint_def;

(* |- !x. x / 1 = x *)
val REAL_DIV_1 = REAL_OVER1;

val REAL_INT_RAT_CONV = let
  val pth = prove
   (“(&x = &x / (&1 :real)) /\
     (~(&x) = ~(&x) / &1) /\
     (DECIMAL x y = &x / &y) /\
     (~DECIMAL x y = ~(&x) / &y)”,
    REWRITE_TAC[REAL_DIV_1, DECIMAL] THEN
    REWRITE_TAC[real_div, REAL_MUL_LNEG])
  in
    GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth]
  end;

(* ------------------------------------------------------------------------- *)
(* Relational operations.                                                    *)
(* ------------------------------------------------------------------------- *)

(* |- !t1 t2 t3. t1 ==> t2 ==> t3 <=> t1 /\ t2 ==> t3 *)
val IMP_IMP = AND_IMP_INTRO;

val REAL_RAT_LE_CONV = let
  val pth = prove
   (“&0 < y1 ==> &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)”,
    REWRITE_TAC[IMP_IMP, RAT_LEMMA4])
  and x1 = “x1:real” and x2 = “x2:real”
  and y1 = “y1:real” and y2 = “y2:real”
  and dest_le = dest_binop realSyntax.leq_tm
  and dest_div = dest_binop realSyntax.div_tm;
  fun RAW_REAL_RAT_LE_CONV tm = let
    val (l,r) = dest_le tm;
    val (lx,ly) = dest_div l
    and (rx,ry) = dest_div r;
    val th0 = INST [x1 |-> lx, y1 |-> ly, x2 |-> rx, y2 |-> ry] pth;
    val th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0;
    val th2 = (BINOP_CONV REAL_INT_MUL_CONV THENC REAL_INT_LE_CONV)
              (rand(concl th1))
  in
    TRANS th1 th2
  end (* of RAW_REAL_RAT_LE_CONV *)
in
   BINOP_CONV REAL_INT_RAT_CONV THENC RAW_REAL_RAT_LE_CONV
end;

val REAL_RAT_LT_CONV = let
  val pth = prove
   (“&0 < y1 ==> &0 < y2 ==> (x1 / y1 < x2 / y2 <=> x1 * y2 < x2 * y1)”,
    REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM REAL_NOT_LE] THEN
    SIMP_TAC bool_ss [TAUT ‘(~a <=> ~b) <=> (a <=> b)’, RAT_LEMMA4])
  and x1 = “x1:real” and x2 = “x2:real”
  and y1 = “y1:real” and y2 = “y2:real”
  and dest_lt = dest_binop realSyntax.less_tm
  and dest_div = dest_binop realSyntax.div_tm;
  fun RAW_REAL_RAT_LT_CONV tm = let
    val (l,r) = dest_lt tm;
    val (lx,ly) = dest_div l
    and (rx,ry) = dest_div r;
    val th0 = INST [x1 |-> lx, y1 |-> ly, x2 |-> rx, y2 |-> ry] pth;
    val th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0;
    val th2 = (BINOP_CONV REAL_INT_MUL_CONV THENC REAL_INT_LT_CONV)
              (rand(concl th1))
  in
    TRANS th1 th2
  end (* of RAW_REAL_RAT_LT_CONV *)
in
   BINOP_CONV REAL_INT_RAT_CONV THENC RAW_REAL_RAT_LT_CONV
end;

val REAL_RAT_GE_CONV =
    GEN_REWRITE_CONV TRY_CONV empty_rewrites [real_ge] THENC
    REAL_RAT_LE_CONV;

val REAL_RAT_GT_CONV =
    GEN_REWRITE_CONV TRY_CONV empty_rewrites [real_gt] THENC
    REAL_RAT_LT_CONV;

val REAL_RAT_EQ_CONV = let
  val pth = prove
   (“&0 < y1 ==> &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))”,
    REWRITE_TAC[IMP_IMP, RAT_LEMMA5])
  and x1 = “x1:real” and x2 = “x2:real”
  and y1 = “y1:real” and y2 = “y2:real”
  and dest_eq = dest_binop realSyntax.real_eq_tm
  and dest_div = dest_binop realSyntax.div_tm;
  fun RAW_REAL_RAT_EQ_CONV tm = let
    val (l,r) = dest_eq tm;
    val (lx,ly) = dest_div l
    and (rx,ry) = dest_div r;
    val th0 = INST [x1 |-> lx, y1 |-> ly, x2 |-> rx, y2 |-> ry] pth;
    val th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0;
    val th2 = (BINOP_CONV REAL_INT_MUL_CONV THENC REAL_INT_EQ_CONV)
              (rand(concl th1))
  in
    TRANS th1 th2
  end (* of RAW_REAL_RAT_EQ_CONV *)
in
   BINOP_CONV REAL_INT_RAT_CONV THENC RAW_REAL_RAT_EQ_CONV
end;

val REAL_RAT_SGN_CONV =
  GEN_REWRITE_CONV TRY_CONV empty_rewrites [real_sgn] THENC
  RATOR_CONV(LAND_CONV REAL_RAT_LT_CONV) THENC
  ((GEN_REWRITE_CONV I empty_rewrites
                     [CONJUNCT1(SPEC_ALL COND_CLAUSES)]) ORELSEC
   (GEN_REWRITE_CONV TRY_CONV empty_rewrites
                     [CONJUNCT2(SPEC_ALL COND_CLAUSES)] THENC
    RATOR_CONV(LAND_CONV REAL_RAT_LT_CONV) THENC
    GEN_REWRITE_CONV TRY_CONV empty_rewrites [COND_CLAUSES]));

(* ------------------------------------------------------------------------- *)
(* The unary operations; all easy.                                           *)
(* ------------------------------------------------------------------------- *)

local open Arbint in
val REAL_RAT_NEG_CONV = let
  val pth = prove
   (“(~(&0) = &0) /\
     (~(~(&n)) = &n) /\
     (~(&m / &n) = ~(&m) / &n) /\
     (~(~(&m) / &n) = &m / &n) /\
     (~(DECIMAL m n) = ~(&m) / &n)”,
    REWRITE_TAC[real_div, REAL_INV_NEG, REAL_MUL_LNEG, REAL_NEG_NEG,
     REAL_NEG_0, DECIMAL])
  and ptm = realSyntax.negate_tm;
  val conv1 = GEN_REWRITE_CONV I empty_rewrites [pth]
in
  (* NOTE: "GEN_REWRITE_CONV I" throws HOL_ERR instead of UNCHANGED! *)
  fn tm => (conv1 tm
            handle HOL_ERR _ =>
           (let val (l,r) = dest_comb tm in
              if l ~~ ptm andalso is_realintconst r andalso
                 dest_realintconst r > zero
              then raise UNCHANGED
              else failwith "REAL_RAT_NEG_CONV"
            end
            handle HOL_ERR _ => failwith "REAL_RAT_NEG_CONV"))
end;
end (* local *)

val REAL_RAT_ABS_CONV = let
  val pth = prove
   (“(abs(&n) = &n) /\
     (abs(~(&n)) = &n) /\
     (abs(&m / &n) = &m / &n) /\
     (abs(~(&m) / &n) = &m / &n) /\
     (abs(DECIMAL m n) = &m / &n) /\
     (abs(~(DECIMAL m n)) = &m / &n)”,
    REWRITE_TAC[DECIMAL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_NUM])
in
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth]
end;

val REAL_RAT_INV_CONV = let
  val pth1 = prove
   (“(inv(&0) = &0) /\
     (inv(&1) = &1) /\
     (inv(~&1) = ~(&1)) /\
     (inv(&1 / &n) = &n) /\
     (inv(~&1 / &n) = ~&n)”,
    REWRITE_TAC[REAL_INV_0, REAL_INV_1, REAL_INV_NEG,
                REAL_INV_DIV, REAL_DIV_1] THEN
    REWRITE_TAC[real_div, REAL_INV_NEG, REAL_MUL_RNEG, REAL_INV_1,
                REAL_MUL_RID])
  and pth2 = prove
   (“(inv(&n) = &1 / &n) /\
     (inv(~(&n)) = ~(&1) / &n) /\
     (inv(&m / &n) = &n / &m) /\
     (inv(~(&m) / &n) = ~(&n) / &m) /\
     (inv(DECIMAL m n) = &n / &m) /\
     (inv(~(DECIMAL m n)) = ~(&n) / &m)”,
    REWRITE_TAC[DECIMAL, REAL_INV_DIV] THEN
    REWRITE_TAC[REAL_INV_NEG, real_div, REAL_MUL_RNEG,
     REAL_MUL_LID, REAL_MUL_LNEG, REAL_INV_MUL, REAL_INV_INV] THEN
    REWRITE_TAC [Once REAL_MUL_COMM])
in
   GEN_REWRITE_CONV I empty_rewrites [pth1] ORELSEC
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth2]
end;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

local open Arbint in
val REAL_RAT_ADD_CONV = let
  val pth = prove
   (“(&0 :real) < y1 ==> &0 < y2 ==> &0 < y3 ==>
     ((x1 * y2 + x2 * y1) * y3 = x3 * (y1 * y2))
     ==> (x1 / y1 + x2 / y2 = x3 / y3)”,
    REPEAT DISCH_TAC THEN
    MP_TAC RAT_LEMMA2 THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL, GSYM real_div] THEN
    Q.SUBGOAL_THEN ‘&0 < y1 * y2 /\ &0 < y3’ MP_TAC THENL
    [ ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => ASM_REWRITE_TAC[MATCH_MP RAT_LEMMA5 th]) ])
  and dest_divop = dest_binop realSyntax.div_tm
  and dest_addop = dest_binop realSyntax.plus_tm
  and x1 = “x1:real” and x2 = “x2:real” and x3 = “x3:real”
  and y1 = “y1:real” and y2 = “y2:real” and y3 = “y3:real”;
  fun RAW_REAL_RAT_ADD_CONV tm = let
    val (r1,r2) = realSyntax.dest_plus tm;
    val (x1',y1') = realSyntax.dest_div r1
    and (x2',y2') = realSyntax.dest_div r2;
    val x1n = dest_realintconst x1' and y1n = dest_realintconst y1'
    and x2n = dest_realintconst x2' and y2n = dest_realintconst y2';
    val x3n = x1n * y2n + x2n * y1n
    and y3n = y1n * y2n;
    val d = gcd x3n y3n;
    val x3n' = quot (x3n,d) and y3n' = quot (y3n,d);
    val (x3n'',y3n'') = if y3n' > zero then (x3n',y3n') else (~x3n',~y3n');
    val x3' = mk_realintconst x3n'' and y3' = mk_realintconst y3n'';
    val th0 = INST [x1 |-> x1', y1 |-> y1', x2 |-> x2', y2 |-> y2',
                    x3 |-> x3', y3 |-> y3'] pth;
    val th1 = funpow 3 (MP_CONV REAL_INT_LT_CONV) th0;
    val (tm2,tm3) = dest_eq(fst(dest_imp(concl th1)));
    val th2 = (LAND_CONV (BINOP_CONV REAL_INT_MUL_CONV THENC
                          REAL_INT_ADD_CONV) THENC
               REAL_INT_MUL_CONV) tm2
    and th3 = (RAND_CONV REAL_INT_MUL_CONV THENC REAL_INT_MUL_CONV) tm3
  in
    MP th1 (TRANS th2 (SYM th3))
  end (* of RAW_REAL_RAT_ADD_CONV *)
in
   BINOP_CONV REAL_INT_RAT_CONV THENC
   RAW_REAL_RAT_ADD_CONV THENC
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [REAL_DIV_1]
end; (* of REAL_RAT_ADD_CONV *)
end (* local *)

(* ------------------------------------------------------------------------- *)
(* Subtraction.                                                              *)
(* ------------------------------------------------------------------------- *)

val REAL_RAT_SUB_CONV = let
  val pth = prove (“x - y = x + ~y”, REWRITE_TAC[real_sub])
in
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth] THENC
   RAND_CONV REAL_RAT_NEG_CONV THENC REAL_RAT_ADD_CONV
end;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

local open Arbint simpLib in
val REAL_RAT_MUL_CONV = let
  val pth_nocancel = prove
   (“(x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2 :real)”,
    SIMP_TAC bool_ss [real_div, REAL_INV_MUL',
                      AC REAL_MUL_ASSOC REAL_MUL_COMM])
  and pth_cancel = prove
   (“~(d1 = (&0 :real)) /\ ~(d2 = &0) /\
     (d1 * u1 = x1) /\ (d2 * u2 = x2) /\
     (d2 * v1 = y1) /\ (d1 * v2 = y2)
     ==> ((x1 / y1) * (x2 / y2) = (u1 * u2) / (v1 * v2))”,
    rpt strip_tac >>
    RW_TAC (bool_ss ++ RMULCANON_ss) [real_div, REAL_INV_MUL', nonzerop_def])
  and x1 = “x1:real” and x2 = “x2:real”
  and y1 = “y1:real” and y2 = “y2:real”
  and u1 = “u1:real” and u2 = “u2:real”
  and v1 = “v1:real” and v2 = “v2:real”
  and d1 = “d1:real” and d2 = “d2:real”;
  fun RAW_REAL_RAT_MUL_CONV tm = let
    val (r1,r2) = dest_mult tm;
    val (x1',y1') = dest_div r1
    and (x2',y2') = dest_div r2;
    val x1n = dest_realintconst x1' and y1n = dest_realintconst y1'
    and x2n = dest_realintconst x2' and y2n = dest_realintconst y2';
    val d1n = gcd x1n y2n
    and d2n = gcd x2n y1n;
  in
    if d1n = one andalso d2n = one then
      let val th0 = INST [x1 |-> x1', y1 |-> y1', x2 |-> x2', y2 |-> y2'] pth_nocancel;
          val th1 = BINOP_CONV REAL_INT_MUL_CONV (rand(concl th0))
      in
          TRANS th0 th1
      end
    else
      let val u1n = quot (x1n, d1n)
          and u2n = quot (x2n, d2n)
          and v1n = quot (y1n, d2n)
          and v2n = quot (y2n, d1n);
          val u1' = mk_realintconst u1n
          and u2' = mk_realintconst u2n
          and v1' = mk_realintconst v1n
          and v2' = mk_realintconst v2n
          and d1' = mk_realintconst d1n
          and d2' = mk_realintconst d2n;
          val th0 = INST [x1 |-> x1', y1 |-> y1', x2 |-> x2', y2 |-> y2',
                          u1 |-> u1', v1 |-> v1', u2 |-> u2', v2 |-> v2',
                          d1 |-> d1', d2 |-> d2'] pth_cancel;
          val th1 = EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th0)));
          val th2 = MP th0 th1;
          val th3 = BINOP_CONV REAL_INT_MUL_CONV (rand(concl th2))
      in
          TRANS th2 th3
      end
  end (* of RAW_REAL_RAT_MUL_CONV *)
in
   BINOP_CONV REAL_INT_RAT_CONV THENC
   RAW_REAL_RAT_MUL_CONV THENC
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [REAL_DIV_1]
end;
end (* local *)

(* ------------------------------------------------------------------------- *)
(* Division.                                                                 *)
(* ------------------------------------------------------------------------- *)

val REAL_RAT_DIV_CONV = let
  val pth = prove (“x / y = x * inv(y)”, REWRITE_TAC[real_div])
in
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth] THENC
   RAND_CONV REAL_RAT_INV_CONV THENC REAL_RAT_MUL_CONV
end;

(* ------------------------------------------------------------------------- *)
(* Powers.                                                                   *)
(* ------------------------------------------------------------------------- *)

val REAL_RAT_POW_CONV = let
  val pth = prove
   (“(x / y) pow n = (x pow n) / (y pow n)”,
    REWRITE_TAC[REAL_POW_DIV])
in
  REAL_INT_POW_CONV ORELSEC
  (LAND_CONV REAL_INT_RAT_CONV THENC
   GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth] THENC
   BINOP_CONV REAL_INT_POW_CONV)
end;

(* ------------------------------------------------------------------------- *)
(* Max and min.                                                              *)
(* ------------------------------------------------------------------------- *)

val REAL_RAT_MAX_CONV =
  REWR_CONV real_max THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV REAL_RAT_LE_CONV)) THENC
  GEN_REWRITE_CONV TRY_CONV empty_rewrites [COND_CLAUSES];

val REAL_RAT_MIN_CONV =
  REWR_CONV real_min THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV REAL_RAT_LE_CONV)) THENC
  GEN_REWRITE_CONV TRY_CONV empty_rewrites [COND_CLAUSES];

(* ------------------------------------------------------------------------- *)
(* Everything.                                                               *)
(* ------------------------------------------------------------------------- *)

val sgn_tm = “real_sgn :real -> real”;
val max_tm = “max :real -> real -> real”;
val min_tm = “min :real -> real -> real”;

fun real_rat_compset () = let
  open computeLib
  val compset = num_compset()
  val _ = add_conv (leq_tm,     2, REAL_RAT_LE_CONV) compset
  val _ = add_conv (less_tm,    2, REAL_RAT_LT_CONV) compset
  val _ = add_conv (geq_tm,     2, REAL_RAT_GE_CONV) compset
  val _ = add_conv (greater_tm, 2, REAL_RAT_GT_CONV) compset
  val _ = add_conv (real_eq_tm, 2, REAL_RAT_EQ_CONV) compset
  val _ = add_conv (negate_tm,  1, CHANGED_CONV REAL_RAT_NEG_CONV) compset
  val _ = add_conv (sgn_tm,     1, REAL_RAT_SGN_CONV) compset
  val _ = add_conv (absval_tm,  1, REAL_RAT_ABS_CONV) compset
  val _ = add_conv (inv_tm,     1, REAL_RAT_INV_CONV) compset
  val _ = add_conv (plus_tm,    2, REAL_RAT_ADD_CONV) compset
  val _ = add_conv (minus_tm,   2, REAL_RAT_SUB_CONV) compset
  val _ = add_conv (mult_tm,    2, REAL_RAT_MUL_CONV) compset
  val _ = add_conv (div_tm,     2, REAL_RAT_DIV_CONV) compset
  val _ = add_conv (exp_tm,     2, REAL_RAT_POW_CONV) compset
  val _ = add_conv (max_tm,     2, REAL_RAT_MAX_CONV) compset
  val _ = add_conv (min_tm,     2, REAL_RAT_MIN_CONV) compset
in
  compset
end;

val REAL_RAT_REDUCE_CONV = let
  val cs = real_rat_compset ();
  val _ = computeLib.set_skip cs boolSyntax.conditional NONE
          (* ensure that REDUCE_CONV will look at all of a term, even
             conditionals' branches *)
in
  computeLib.CBV_CONV cs
end

(* ------------------------------------------------------------------------- *)
(* Real normalizer dealing with rational constants.                          *)
(* ------------------------------------------------------------------------- *)

fun term_lt x y = (Term.compare (x,y) = LESS);

(* NOTE: the returned REAL_POLY_CONV' does not support many real operators.  *)
val (REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_SUB_CONV,
     REAL_POLY_MUL_CONV,REAL_POLY_POW_CONV,REAL_POLY_CONV') =
  SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES
   (is_ratconst,
    REAL_RAT_ADD_CONV,REAL_RAT_MUL_CONV,REAL_RAT_POW_CONV) term_lt;

(* ------------------------------------------------------------------------- *)
(* Extend normalizer to handle "inv" and division by rational constants, and *)
(* normalize inside nested "max", "min" and "abs" terms.                     *)
(* ------------------------------------------------------------------------- *)

(* NOTE: the above REAL_POLY_CONV' is not used here. *)
val div_conv = QCONV (REWR_CONV real_div);

val REAL_POLY_CONV = let
  fun REAL_POLY_CONV' tm =
    if not(is_comb tm) orelse is_ratconst tm then
        REFL tm
    else
    let val (lop,r) = dest_comb tm in
    if lop ~~ negate_tm then
      let val th1 = AP_TERM lop (REAL_POLY_CONV' r) in
        TRANS th1 (REAL_POLY_NEG_CONV (rand(concl th1)))
      end
    else if lop ~~ inv_tm then
      let val th1 = AP_TERM lop (REAL_POLY_CONV' r) in
        TRANS th1 (QCONV REAL_RAT_INV_CONV (rand(concl th1)))
      end
    else if lop ~~ absval_tm then
        AP_TERM lop (REAL_POLY_CONV' r)
    else if not(is_comb lop) then
        REFL tm
    else
    let val (op',l) = dest_comb lop in
    if op' ~~ exp_tm then
      let val th1 = AP_THM (AP_TERM op' (REAL_POLY_CONV' l)) r in
        TRANS th1 (QCONV REAL_POLY_POW_CONV (rand(concl th1)))
      end
    else if op' ~~ plus_tm orelse op' ~~ mult_tm orelse op' ~~ minus_tm then
      let val th1 = MK_COMB(AP_TERM op' (REAL_POLY_CONV' l),
                            REAL_POLY_CONV' r)
          and fn' = if op' ~~ plus_tm then REAL_POLY_ADD_CONV
               else if op' ~~ mult_tm then REAL_POLY_MUL_CONV
               else REAL_POLY_SUB_CONV in
        TRANS th1 (QCONV fn' (rand(concl th1)))
      end
    else if op' ~~ div_tm then
      let val th1 = div_conv tm in
        TRANS th1 (REAL_POLY_CONV' (rand(concl th1)))
      end
    else if op' ~~ min_tm orelse op' ~~ max_tm then
        MK_COMB(AP_TERM op' (REAL_POLY_CONV' l),REAL_POLY_CONV' r)
    else
        REFL tm
    end (* let val (op',l) *)
    end (* let val (lop,r) *)
in
    UNCHANGED_CONV REAL_POLY_CONV'
end;

(* ------------------------------------------------------------------------- *)
(* Basic ring and ideal conversions.                                         *)
(* ------------------------------------------------------------------------- *)

val (REAL_RING,real_ideal_cofactors) = let
  val REAL_INTEGRAL = prove
   (“(!(x :real). &0 * x = &0) /\
     (!(x :real) y z. (x + y = x + z) <=> (y = z)) /\
     (!(w :real) x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))”,
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_ENTIRE] THEN REAL_ARITH_TAC)
  and REAL_RABINOWITSCH = prove
   (“!x y:real. ~(x = y) <=> ?z. (x - y) * z = &1”,
    REWRITE_TAC[EQ_IMP_THM] >> rpt strip_tac >>
    FULL_SIMP_TAC std_ss [EQ_IMP_THM, REAL_SUB_REFL, REAL_MUL_LZERO, REAL_10] >>
    irule_at Any REAL_MUL_RINV >> ASM_REWRITE_TAC [REAL_SUB_0])
  and init = GEN_REWRITE_CONV ONCE_DEPTH_CONV empty_rewrites [DECIMAL];
  val (pure,ideal) =
    RING_AND_IDEAL_CONV
        (rat_of_term, term_of_rat, REAL_RAT_EQ_CONV,
         negate_tm, plus_tm, minus_tm, inv_tm, mult_tm, div_tm, exp_tm,
         REAL_INTEGRAL, REAL_RABINOWITSCH, REAL_POLY_CONV);
in
  ((fn tm => let val th = init tm handle UNCHANGED => REFL tm in
                 EQ_MP (SYM th) (pure(rand(concl th)))
             end),
   (fn tms => fn tm =>
       if forall (fn t => type_of t = real_ty) (tm::tms) then
           ideal tms tm
       else
           failwith "real_ideal_cofactors: not all terms have type :real"))
end;

(* ------------------------------------------------------------------------- *)
(* Conversion for ideal membership.                                          *)
(* ------------------------------------------------------------------------- *)

fun REAL_IDEAL_CONV tms tm = let
    val cfs = real_ideal_cofactors tms tm;
    val tm' = end_itlist (curry mk_plus) (map2 (curry mk_mult) cfs tms);
    val th = REAL_POLY_CONV tm
    and th' = REAL_POLY_CONV tm'
in
    TRANS th (SYM th')
end;

(* ------------------------------------------------------------------------- *)
(* Further specialize GEN_REAL_ARITH and REAL_ARITH (final versions).        *)
(* ------------------------------------------------------------------------- *)

(* NOTE: since it's not going to be exported, no need to have the same name. *)
fun GEN_REAL_ARITH prover =
    RealArith.GEN_REAL_ARITH
   (term_of_rat,
    REAL_RAT_EQ_CONV,REAL_RAT_GE_CONV,REAL_RAT_GT_CONV,
    REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
    prover);

val REAL_ARITH = let
  val init = GEN_REWRITE_CONV ONCE_DEPTH_CONV empty_rewrites [DECIMAL]
  and pure = GEN_REAL_ARITH REAL_LINEAR_PROVER
in
  fn tm => let val th = init tm handle UNCHANGED => REFL tm in
               EQ_MP (SYM th) (pure(rand(concl th)))
           end
end;

(* tactic versions *)
val (REAL_ARITH_TAC,REAL_ASM_ARITH_TAC) = mk_real_arith_tac REAL_ARITH;

(* ------------------------------------------------------------------------- *)
(* A simple "field" rule.                                                    *)
(* ------------------------------------------------------------------------- *)

val REAL_FIELD = let
  fun check p x = if p x then x else failwith "check";
  val norm_conv =
      REWR_CONV(GSYM REAL_POW_INV) o check (is_numeral o rand o rand);
  val norm_net = simpLib.SSFRAG
     {name = SOME "REAL_FIELD",
      convs = [{name = "inv",  trace = 1, key = SOME([], “inv((x:real) pow n)”),
                conv = K (K norm_conv)}],
      rewrs = [(SOME{Thy = "bool", Name = "FORALL_SIMP"}, FORALL_SIMP),
               (SOME{Thy = "bool", Name = "EXISTS_SIMP"}, EXISTS_SIMP),
               (SOME{Thy = "realax", Name = "real_div"}, real_div),
               (SOME{Thy = "real", Name = "REAL_INV_INV"}, REAL_INV_INV),
               (SOME{Thy = "real", Name = "REAL_INV_MUL'"}, REAL_INV_MUL'),
               (SOME{Thy = "real", Name = "REAL_POW_ADD"}, REAL_POW_ADD)],
      congs = [], filter = NONE, ac = [], dprocs = []};

  val pth = prove(
       “x pow n <> 0 <=> x <> 0 \/ &n = 0r \/ x pow n <> 0”,
       SIMP_TAC bool_ss [REAL_POW_EQ_0, DE_MORGAN_THM,EQ_IMP_THM,DISJ_IMP_THM,
                         REAL_OF_NUM_EQ]);

  val easy_nz_conv = QCONV
     (LAND_CONV (GEN_REWRITE_CONV TRY_CONV empty_rewrites [pth]) THENC
      TRY_CONV(LAND_CONV REAL_RAT_REDUCE_CONV THENC
               GEN_REWRITE_CONV I empty_rewrites [TAUT ‘(T ==> p) <=> p’]));

  val and_tm = boolSyntax.conjunction;
  val prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    NUM_REDUCE_CONV THENC
    TOP_DEPTH_CONV(SIMP_CONV (bool_ss ++ norm_net) []) THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV and_tm CONDS_CELIM_CONV THENC
    PRENEX_CONV THENC
    ONCE_REWRITE_CONV[REAL_ARITH “(x :real) < y <=> x < y /\ ~(x = y)”];

  val setup_conv = NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV;

  (* REAL_RING and REAL_ARITH are called here! *)
  fun core_rule t = (REAL_RING t) handle HOL_ERR _ => REAL_ARITH t;

  fun is_inv' tm =
     (is_div tm orelse realSyntax.is_inv tm) andalso not(is_ratconst(rand tm));

  fun BASIC_REAL_FIELD tm = let
    fun is_freeinv t = is_inv' t andalso free_in t tm;
    val itms = setify_term (map rand (find_terms is_freeinv tm));
    val hyps = map
       (fn t => CONV_RULE easy_nz_conv (SPEC t REAL_MUL_RINV)) itms;
    val tm' = itlist (fn th => fn t => mk_imp(concl th,t)) hyps tm;
    val th1 = setup_conv tm';
    val cjs = strip_conj(rand(concl th1));
    val ths = map core_rule cjs;
    val th2 = EQ_MP (SYM th1) (end_itlist CONJ ths)
  in
    rev_itlist (C MP) hyps th2
  end
in
  fn tm => let
    val th0 = prenex_conv tm;
    val tm0 = rand(concl th0);
    val (avs,bod) = strip_forall tm0;
    val th1 = setup_conv bod;
    val ths = map BASIC_REAL_FIELD (strip_conj(rand(concl th1)))
  in
    EQ_MP (SYM th0) (GENL avs (EQ_MP (SYM th1) (end_itlist CONJ ths)))
  end
end (* REAL_FIELD *)

(* create tactic versions for REAL_FIELD *)
val (REAL_FIELD_TAC,REAL_ASM_FIELD_TAC) = mk_real_arith_tac REAL_FIELD;

(* set verbose level to 1 by default *)
val _ = RealArith.verbose_level := 1;

end (* struct *)
