structure OmegaShell :> OmegaShell =
struct

open HolKernel boolLib intSyntax QConv integerTheory

(* Takes a closed Presburger arithmetic term over the integers and
   tries to decide it using the Omega procedure.

   Terms that are Presburger over the naturals or have free variables,
   or both, are dealt with by the procedures in IntDP_Munge.

   This code makes the decision as to whether or not OmegaSimple can be
   used, and also performs the necessary normalisation of the input.
*)

infix THENC THEN ORELSEC |->
infixr --> ##

val lhand = rand o rator

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val BINOP_CONV = BINOP_QCONV
val ALL_CONV = ALL_QCONV
val TRY_CONV = TRY_QCONV

fun ERR f msg = HOL_ERR { origin_structure = "OmegaShell",
                          origin_function = f,
                          message = msg}

fun EVERY_SUMMAND c tm =
  if is_plus tm then BINOP_CONV (EVERY_SUMMAND c) tm
  else c tm

(* ----------------------------------------------------------------------
    check_for_early_equalities t

    t is of the form ?v1..vn. T, and T has been purged of all negations
    and connectives other than /\ and \/.
    Before throwing ourselves into DNF-ication, we check to see if T
    can be seen as
          (c * vi = ....) /\ P vi
    If so, the OmegaEq simplification might usefully be applied.  Moreover
    we may save on having to do it multiple times in lots of different
    disjuncts if we do it now rather than later.
   ---------------------------------------------------------------------- *)

val check_for_early_equalities = OmegaEq.OmegaEq


(* ----------------------------------------------------------------------
    leaf_normalise t

    Takes a "leaf term" (a relational operator over integer values) and
    normalises it to either an equality, a <= or a disjunction of two
    (un-normalised) <= leaves.  (The latter happens if called onto
    normalise ~(x = y)).
   ---------------------------------------------------------------------- *)

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
                             INT_NEG_LMUL, INT_NEGNEG, INT_NEG_0,
                             int_sub] THENC
               EVERY_SUMMAND (TRY_CONV OmegaMath.NORMALISE_MULT) THENC
               REWRITE_CONV [GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                             INT_NEGNEG] THENC
               REWRITE_CONV [INT_NEG_LMUL] THENC
               OmegaMath.SORT_AND_GATHER_CONV)
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

val leaf_normalise = REWR_CONV not_eq ORELSEC normalise_numbers
end (* local *)

fun ISCONST_CONV tm = if is_const tm then ALL_CONV tm else NO_CONV tm

(* ----------------------------------------------------------------------
    normalise t

    Normalises t, where t is of the form
        ?v1..vn. T
    and T is a closed term involving usual boolean operators and leaf terms
    that are relational operators over integers.  T is put into DNF, and
    the leaf terms are all normalised as well.
   ---------------------------------------------------------------------- *)

val normalise = let
  fun push_exs tm = let
    val vs = map (#1 o dest_var) (#1 (strip_exists tm))
  in
    CooperSyntax.push_in_exists THENC EVERY_DISJ_CONV (RENAME_VARS_CONV vs)
  end tm
in
  STRIP_QUANT_CONV (Canon.NNF_CONV leaf_normalise false THENC
                    CSimp.csimp leaf_normalise) THENC
  push_exs THENC
  EVERY_DISJ_CONV (check_for_early_equalities THENC
                   (ISCONST_CONV ORELSEC
                    (STRIP_QUANT_CONV Canon.PROP_DNF_CONV THENC push_exs)))
end


fun generate_nway_casesplit n = let
  val _ = n >= 1 orelse raise Fail "generate_nway_casesplit: n < 1"
  fun genty n = if n = 1 then bool --> bool
                else bool --> (genty (n - 1))
  val P_ty = genty n
  val P_t = mk_var("P", P_ty)
  fun gen_cases (m, vs, t) =
      if m < n then let
          val v = mk_var("v"^Int.toString m, bool)
          val vT = (m + 1, v::vs, mk_comb(t, T))
          val vF = (m + 1, (mk_neg v)::vs, mk_comb(t, F))
        in
          mk_disj(gen_cases vT, gen_cases vF)
        end
      else
        mk_conj(t, list_mk_conj vs)
  val RHS = gen_cases (0, [], P_t)
  fun gen_vars n acc =
      if n < 0 then acc
      else gen_vars (n - 1) (mk_var("v"^Int.toString n, bool)::acc)
  val vars = gen_vars (n - 1) []
in
  GEN P_t (GENL vars
                (prove(mk_eq(list_mk_comb(P_t, vars), RHS),
                       MAP_EVERY BOOL_CASES_TAC vars THEN REWRITE_TAC [])))
end

fun UNBETA_LIST tlist =
    case tlist of
      [] => ALL_CONV
    | (t::ts) => CooperSyntax.UNBETA_CONV t THENC RATOR_CONV (UNBETA_LIST ts)

val not_beq = prove(
  ``~(b1 = b2) = b1 /\ ~b2 \/ ~b1 /\ b2``,
  BOOL_CASES_TAC ``b1:bool`` THEN REWRITE_TAC []);
val beq = prove(
  ``(b1 = b2) = b1 /\ b2 \/ ~b1 /\ ~b2``,
  BOOL_CASES_TAC ``b1:bool`` THEN REWRITE_TAC []);

fun reveal_a_disj tm =
    if is_disj tm then ALL_CONV tm
    else
      (FIRST_CONV (map REWR_CONV [beq, not_beq, IMP_DISJ_THM,
                                  CooperThms.NOT_AND]) ORELSEC
       (REWR_CONV CooperThms.NOT_NOT_P THENC reveal_a_disj)) tm


(* ----------------------------------------------------------------------
    normalise_guard t

    t is a conditional expression with a single leaf term as its guard.
    If this is a <= leaf, flip its sense (and the corresponding then and
    else branches) so that the coefficient of the first variable is
    positive
   ---------------------------------------------------------------------- *)

val FLIP_COND = prove(
  ``(if g then t:'a else e) = if ~g then e else t``,
  COND_CASES_TAC THEN REWRITE_TAC []);

fun normalise_guard t = let
  val _ = dest_cond t
  fun make_guard_positive t = let
    val (g, _, _) = dest_cond t
  in
    if is_leq g then let
        val t1 = hd (strip_plus (rand g))
      in
        if is_negated (#1 (dest_mult t1)) handle HOL_ERR _ => false then
          REWR_CONV FLIP_COND THENC
          RATOR_CONV (LAND_CONV leaf_normalise)
        else
          ALL_CONV
      end
    else
      ALL_CONV
  end t
in
  RATOR_CONV (LAND_CONV leaf_normalise) THENC make_guard_positive
end t

fun TOP_SWEEP_ONCE_CONV c t =
    (TRY_CONV c THENC SUB_QCONV (TOP_SWEEP_ONCE_CONV c)) t

val normalise_guards = TOP_SWEEP_ONCE_CONV normalise_guard

(* ----------------------------------------------------------------------
    cond_removal0 t

    If t contains conditional expressions where guards of these appear
    more than once, then do a case-split on these guard expressions at
    the top level.
    E.g.,
        (if g then t else e) /\ (if g then t' else e')
    will turn into
        g /\ t /\ t' \/ g /\ e /\ e'

   ---------------------------------------------------------------------- *)

fun cond_removal0 t = let
  open Binarymap
  val condexps = List.map (hd o #2 o strip_comb) (find_terms is_cond t)
  val empty_map = mkDict Term.compare
  fun my_insert(g, m) =
      case peek(m,g) of
        NONE => insert(m, g, 1)
      | SOME n => insert(m, g, n + 1)
  val final_map = List.foldl my_insert empty_map condexps
  fun find_gt2 (t,n,l) = if n >= 2 then t::l else l
  val gt2_guards = foldl find_gt2 [] final_map
  val n = assert (curry op < 0) (length gt2_guards)
  val case_split = generate_nway_casesplit n
in
  UNBETA_LIST (List.rev gt2_guards) THENC
  REWR_CONV case_split THENC
  EVERY_DISJ_CONV (LAND_CONV LIST_BETA_CONV THENC REWRITE_CONV [])
end t

(* ----------------------------------------------------------------------
    cond_removal t

    Perform cond_removal0 on all of t's disjunctions, not being put off
    by disjunctions hiding as negated conjunctions.
   ---------------------------------------------------------------------- *)

fun cond_removal t =
    ((reveal_a_disj THENC BINOP_CONV cond_removal) ORELSEC
     (normalise_guards THENC cond_removal0)) t


(* ----------------------------------------------------------------------
    simple t

    Takes a closed term of form ?v1..vn. T and decides it using the
    OmegaSimple method.
   ---------------------------------------------------------------------- *)

val simple =
  TRY_CONV (STRIP_QUANT_CONV cond_removal) THENC
  normalise THENC
  EVERY_DISJ_CONV (REWRITE_CONV [] THENC
                   (ISCONST_CONV ORELSEC
                    (OmegaEq.OmegaEq THENC
                     (ISCONST_CONV ORELSEC OmegaSimple.simple_CONV))))

val tac = COND_CASES_TAC THEN REWRITE_TAC []
val COND_FA_THEN_THM =
    prove(``(if p then !x:'a. P x else q) = !x. if p then P x else q``, tac)
val COND_FA_ELSE_THM =
    prove(``(if p then q else !x:'a. P x) = !x. if p then q else P x``, tac)
val COND_EX_THEN_THM =
    prove(``(if p then ?x:'a. P x else q) = ?x. if p then P x else q``, tac)
val COND_EX_ELSE_THM =
    prove(``(if p then q else ?x:'a. P x) = ?x. if p then q else P x``, tac)

fun COND_FA_THEN tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_forall t
in
  HO_REWR_CONV COND_FA_THEN_THM THENC RAND_CONV (ALPHA_CONV v)
end tm
fun COND_FA_ELSE tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_forall e
in
  HO_REWR_CONV COND_FA_ELSE_THM THENC RAND_CONV (ALPHA_CONV v)
end tm
fun COND_EX_THEN tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_exists t
in
  HO_REWR_CONV COND_EX_THEN_THM THENC RAND_CONV (ALPHA_CONV v)
end tm
fun COND_EX_ELSE tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_exists e
in
  HO_REWR_CONV COND_EX_ELSE_THM THENC RAND_CONV (ALPHA_CONV v)
end tm

val myPRENEX_CONV =
    TOP_DEPTH_CONV
    (FIRST_CONV [NOT_FORALL_CONV, NOT_EXISTS_CONV,
                 AND_FORALL_CONV, OR_EXISTS_CONV,
                 RIGHT_AND_FORALL_CONV, LEFT_AND_FORALL_CONV,
                 RIGHT_AND_EXISTS_CONV, LEFT_AND_EXISTS_CONV,
                 RIGHT_IMP_FORALL_CONV, LEFT_IMP_FORALL_CONV,
                 RIGHT_IMP_EXISTS_CONV, LEFT_IMP_EXISTS_CONV,
                 RIGHT_OR_FORALL_CONV,  LEFT_OR_FORALL_CONV,
                 RIGHT_OR_EXISTS_CONV,  LEFT_OR_EXISTS_CONV,
                 COND_FA_THEN, COND_FA_ELSE, COND_EX_THEN, COND_EX_ELSE])

fun decide_strategy tm = let
  open CooperSyntax
in
  case goal_qtype tm of
    qsUNIV =>
      myPRENEX_CONV THENC flip_foralls THENC
      RAND_CONV simple THENC CooperMath.REDUCE_CONV
  | qsEXISTS => myPRENEX_CONV THENC simple
  | EITHER => CooperMath.REDUCE_CONV
  | NEITHER =>
      raise ERR "decide_closed_presburger"
        "Can't handle alternating quantifiers"
end tm


(* in order to do prenexing, we need to remove quantifiers that hide
   within conditional guards.  There's a lot of faff happening here:
   why not just do away with conditional expressions from the outset?

   Two reasons:
  * rewriting the wrong way will double the term size because one
    rewrite is right for CNF and the other is right for DNF.
  * conditional expressions that repeat the same guard should have
    the case-split done on the guard just once. *)
fun remove_qs_from_guards tm = let
  val (g, t, e) = dest_cond tm
in
  if CooperSyntax.goal_qtype g <> CooperSyntax.EITHER then
    REWR_CONV COND_EXPAND tm
  else NO_CONV tm
end









val decide_closed_presburger =
    TOP_DEPTH_CONV remove_qs_from_guards THENC
    REWRITE_CONV [IMP_DISJ_THM] THENC decide_strategy

(* utility function for assessing how big a term will result when something
   is converted to DNF naively :
fun dnf_size t =
    if is_disj t then
      (op+ o (dnf_size ## dnf_size) o dest_disj) t
    else if is_conj t then
      (op* o (dnf_size ## dnf_size) o dest_conj) t
    else 1

*)


end (* struct *)