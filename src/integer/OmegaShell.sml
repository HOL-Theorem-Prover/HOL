structure OmegaShell :> OmegaShell =
struct

open HolKernel boolLib intSyntax QConv integerTheory

(* Takes a closed Presburger arithmetic term over the integers and
   tries to decide it using the Omega procedure.

   Terms that are Presburger over the naturals or have free variables, or
   both, are dealt with be by the procedures in Omega.

   This code makes the decision as to whether or not OmegaSimple can be
   used, and also performs the necessary normalisation of the input.
*)

infix THENC ORELSEC |->

val lhand = rand o rator

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val BINOP_CONV = BINOP_QCONV
val ALL_CONV = ALL_QCONV

fun ERR f msg = HOL_ERR { origin_structure = "OmegaShell",
                          origin_function = f,
                          message = msg}

fun EVERY_SUMMAND c tm =
  if is_plus tm then BINOP_CONV (EVERY_SUMMAND c) tm
  else c tm

local
  val lt_elim = SPEC_ALL int_arithTheory.less_to_leq_samer
  val tac = REWRITE_TAC [GSYM int_le, INT_NOT_LE, lt_elim, int_gt,
                         INT_LE_RADD, int_ge, GSYM INT_LE_ANTISYM,
                         DE_MORGAN_THM]
  val not_le = prove(``~(x <= y) = (y + 1i <= x)``, tac)
  val not_lt = prove(``~(x:int < y) = y <= x``, tac)
  val not_gt = prove(``~(x:int > y) = x <= y``, tac)
  val not_ge = prove(``~(x >= y) = x + 1i <= y``, tac)
  val not_eq = prove(``~(x = y:int) = y + 1 <= x \/ x + 1 <= y``, tac)
  val ge_elim = prove(``x:int >= y = y <= x``, tac)
  val gt_elim = prove(``x > y = y + 1i <= x``, tac)
  val eq_elim = prove(``(x:int = y) = (x <= y /\ y <= x)``, tac)
in

fun normalise_numbers tm = let
  val MK_LEQ =
    TRY_CONV (FIRST_CONV (map REWR_CONV [lt_elim, not_le, not_lt, not_gt,
                                         not_ge, ge_elim, gt_elim])) THENC
    (REWR_CONV int_arithTheory.le_move_all_right ORELSEC
     REWR_CONV int_arithTheory.eq_move_all_right)
  val base_normaliser =
    RAND_CONV (REWRITE_CONV [INT_NEG_ADD, INT_LDISTRIB, INT_RDISTRIB,
                             INT_NEG_LMUL, INT_NEGNEG] THENC
               EVERY_SUMMAND (TRY_CONV OmegaMath.NORMALISE_MULT) THENC
               REWRITE_CONV [GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                             INT_NEGNEG] THENC
               REWRITE_CONV [INT_NEG_LMUL] THENC
               OmegaMath.SORT_AND_GATHER_CONV THENC OmegaMath.addzero)
in
  if (is_leq tm orelse is_eq tm) andalso lhand tm = zero_tm then
    if is_plus (rand tm) then let
      val (rl, rr) = dest_plus (rand tm)
      fun mult_ok acc tm = let
        val (c,v) = dest_mult tm
      in
        is_int_literal c andalso is_var v andalso
        (case acc of
           NONE => true
         | SOME v0 => Term.compare(v0, v) = GREATER)
      end handle HOL_ERR _ => false
      fun rhs_ok acc tm = let
        val (l,r) = dest_plus tm
      in
        mult_ok acc r andalso rhs_ok (SOME (rand r)) l
      end handle HOL_ERR _ => mult_ok acc tm
    in
      if is_int_literal rr andalso rhs_ok NONE rl then NO_CONV
      else base_normaliser
    end
    else if is_int_literal (rand tm) then CooperMath.REDUCE_CONV
         else base_normaliser
  else MK_LEQ THENC base_normaliser
end tm

val leaf_normalise =
  REWR_CONV not_eq ORELSEC REWR_CONV eq_elim ORELSEC normalise_numbers
end (* local *)

fun normalise tm = let
  val vs = map (#1 o dest_var) (#1 (strip_exists tm))
in
  STRIP_QUANT_CONV (Canon.NNF_CONV leaf_normalise false THENC
                    Canon.PROP_DNF_CONV) THENC
  CooperSyntax.push_in_exists THENC EVERY_DISJ_CONV (RENAME_VARS_CONV vs)
end tm

fun ISCONST_CONV tm = if is_const tm then ALL_CONV tm else NO_CONV tm

val simple =
  normalise THENC
  EVERY_DISJ_CONV (REWRITE_CONV [] THENC
                   (ISCONST_CONV ORELSEC
                    (OmegaEq.OmegaEq THENC OmegaSimple.simple_CONV)))


fun decide_strategy tm = let
  open CooperSyntax
in
  case goal_qtype tm of
    qsUNIV =>
      Canon.PRENEX_CONV THENC flip_foralls THENC
      RAND_CONV simple THENC CooperMath.REDUCE_CONV
  | qsEXISTS => Canon.PRENEX_CONV THENC simple
  | EITHER => CooperMath.REDUCE_CONV
  | NEITHER =>
      raise ERR "decide_closed_presburger"
        "Can't handle alternating quantifiers"
end tm




val decide_closed_presburger = decide_strategy


end (* struct *)