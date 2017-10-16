(* ===================================================================== *)
(* FILE          : Tactic.sml                                            *)
(* DESCRIPTION   : Tactics are from LCF. They are a fundamental proof    *)
(*                 method due to Robin Milner. This file has been        *)
(*                 translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)

structure Tactic :> Tactic =
struct

open HolKernel Drule Conv Tactical Thm_cont boolTheory boolSyntax Abbrev;

val ERR = mk_HOL_ERR "Tactic"

fun empty th [] = th
  | empty th _ = raise ERR "empty" "Bind Error"
fun sing f [x] = f x
  | sing f _ = raise ERR "sing" "Bind Error"
fun pairths f [x, y] = f x y
  | pairths f _ = raise ERR "pairths" "Bind Error"

(*---------------------------------------------------------------------------*
 * Accepts a theorem that satisfies the goal                                 *
 *                                                                           *
 *      A                                                                    *
 *    ========= ACCEPT_TAC "|-A"                                             *
 *      -                                                                    *
 *---------------------------------------------------------------------------*)

val ACCEPT_TAC: thm_tactic =
   fn th => fn (asl, w) =>
      if aconv (concl th) w then ([], empty th) else raise ERR "ACCEPT_TAC" ""

(* --------------------------------------------------------------------------*
 * DISCARD_TAC: checks that a theorem is useless, then ignores it.           *
 * Revised: 90.06.15 TFM.                                                    *
 * --------------------------------------------------------------------------*)

fun DISCARD_TAC th (asl, w) =
   if Lib.exists (aconv (concl th)) (boolSyntax.T :: asl)
      then ALL_TAC (asl, w)
   else raise ERR "DISCARD_TAC" ""

(*---------------------------------------------------------------------------*
 * Contradiction rule                                                        *
 *                                                                           *
 *       A                                                                   *
 *    ===========  CONTR_TAC "|- F"                                          *
 *       -                                                                   *
 *---------------------------------------------------------------------------*)

val CONTR_TAC: thm_tactic =
   fn cth => fn (asl, w) =>
      let
         val th = CONTR w cth
      in
         ([], empty th)
      end
      handle HOL_ERR _ => raise ERR "CONTR_TAC" ""

(* --------------------------------------------------------------------------*
 * OPPOSITE_TAC: proves the goal using the theorem p and an assumption ~p.   *
 * --------------------------------------------------------------------------*)

local
   fun resolve th th' = MP (MP (SPEC (concl th) F_IMP) th') th

   fun target_rule tm =
      if is_neg tm then (dest_neg tm, Lib.C resolve) else (mk_neg tm, resolve)
in
   fun OPPOSITE_TAC th (asl, w) =
      let
         val (opp, rule) = target_rule (concl th)
      in
         case List.find (aconv opp) asl of
            NONE => raise ERR "OPPOSITE_TAC" ""
          | SOME asm => CONTR_TAC (rule th (ASSUME asm)) (asl, w)
      end
end

(*---------------------------------------------------------------------------*
 * Classical contradiction rule                                              *
 *                                                                           *
 *       A                                                                   *
 *    ===========  CCONTR_TAC                                                *
 *       -                                                                   *
 *---------------------------------------------------------------------------*)

fun CCONTR_TAC (asl, w) = ([(mk_neg w :: asl, boolSyntax.F)], sing (CCONTR w))

(*---------------------------------------------------------------------------*
 * Put a theorem onto the assumption list.                                   *
 * Note:  since an assumption B denotes a theorem B|-B,                      *
 *        you cannot instantiate types or variables in assumptions.          *
 *                                                                           *
 *         A                                                                 *
 *    ===========  |- B                                                      *
 *      [B] A                                                                *
 *---------------------------------------------------------------------------*)

val ASSUME_TAC: thm_tactic =
   fn bth => fn (asl, w) => ([(concl bth :: asl, w)], sing (PROVE_HYP bth))

val assume_tac = ASSUME_TAC

(*---------------------------------------------------------------------------*
 * "Freeze" a theorem to prevent instantiation                               *
 *                                                                           *
 *         A                                                                 *
 *    ===========       ttac "B|-B"                                          *
 *        ...                                                                *
 *---------------------------------------------------------------------------*)

val FREEZE_THEN: thm_tactical =
   fn ttac: thm_tactic => fn bth => fn g =>
      let
         val (gl, prf) = ttac (ASSUME (concl bth)) g
      in
         (gl, PROVE_HYP bth o prf)
      end

(*---------------------------------------------------------------------------*
 * Conjunction introduction                                                  *
 *                                                                           *
 *         A /\ B                                                            *
 *     ===============                                                       *
 *       A        B                                                          *
 *---------------------------------------------------------------------------*)

val CONJ_TAC: tactic =
   fn (asl, w) =>
      let
         val (conj1, conj2) = dest_conj w
      in
         ([(asl, conj1), (asl, conj2)],
          fn [th1, th2] => CONJ th1 th2 | _ => raise Match)
      end
      handle HOL_ERR _ => raise ERR "CONJ_TAC" ""
val conj_tac = CONJ_TAC

(* ASM1 & ASM2 variants assume the given conjunct when proving the other one *)

val CONJ_ASM1_TAC = CONJ_TAC THEN_LT USE_SG_THEN ASSUME_TAC 1 2 ;
val CONJ_ASM2_TAC = CONJ_TAC THEN_LT USE_SG_THEN ASSUME_TAC 2 1 ;
val conj_asm1_tac = CONJ_ASM1_TAC
val conj_asm2_tac = CONJ_ASM2_TAC

(*---------------------------------------------------------------------------*
 * Disjunction introduction                                                  *
 *                                                                           *
 *      A \/ B                                                               *
 *  ==============                                                           *
 *        A                                                                  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun DISJ1_TAC (asl, w) =
   let
      val (disj1, disj2) = dest_disj w
   in
      ([(asl, disj1)], sing (fn th => DISJ1 th disj2))
   end
   handle HOL_ERR _ => raise ERR "DISJ1_TAC" ""
val disj1_tac = DISJ1_TAC

(*---------------------------------------------------------------------------*
 *      A \/ B                                                               *
 *    ==============                                                         *
 *        B                                                                  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun DISJ2_TAC (asl, w) =
   let
      val (disj1, disj2) = dest_disj w
   in
      ([(asl, disj2)], sing (DISJ2 disj1))
   end
   handle HOL_ERR _ => raise ERR "DISJ2_TAC" ""
val disj2_tac = DISJ2_TAC

(*---------------------------------------------------------------------------*
 * Implication elimination                                                   *
 *                                                                           *
 *                  A                                                        *
 *     |- B  ================                                                *
 *                B ==> A                                                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun MP_TAC thb (asl, w) =
   ([(asl, mk_imp (concl thb, w))], sing (fn thimp => MP thimp thb))
val mp_tac = MP_TAC

(*---------------------------------------------------------------------------*
 * Equality Introduction                                                     *
 *                                                                           *
 *                A = B                                                      *
 *        =====================                                              *
 *         A ==> B     B ==> A                                               *
 *                                                                           *
 *---------------------------------------------------------------------------*)

val EQ_TAC: tactic =
   fn (asl, t) =>
      let
         val (lhs, rhs) = dest_eq t
      in
         ([(asl, mk_imp (lhs, rhs)), (asl, mk_imp (rhs, lhs))],
          fn [th1, th2] => IMP_ANTISYM_RULE th1 th2 | _ => raise Match)
      end
      handle HOL_ERR _ => raise ERR "EQ_TAC" ""
val eq_tac = EQ_TAC

(*---------------------------------------------------------------------------*
 * Universal quantifier                                                      *
 *                                                                           *
 *      !x.A(x)                                                              *
 *   ==============                                                          *
 *        A(x')                                                              *
 *                                                                           *
 * Explicit version for tactic programming;  proof fails if x' is free in    *
 * hyps.                                                                     *
 *                                                                           *
 * fun X_GEN_TAC x' :tactic (asl,w) =                                        *
 *   (let val x,body = dest_forall w in                                      *
 *    [ (asl, subst[x',x]body) ], (\[th]. GEN x' th)                         *
 *   ) ? failwith X_GEN_TAC;                                                 *
 *                                                                           *
 * T. Melham. X_GEN_TAC rewritten 88.09.17                                   *
 *                                                                           *
 * 1)  X_GEN_TAC x'    now fails if x' is not a variable.                    *
 *                                                                           *
 * 2) rewritten so that the proof yields the same quantified var as the      *
 *    goal.                                                                  *
 *                                                                           *
 *  fun X_GEN_TAC x' :tactic =                                               *
 *   if not(is_var x') then failwith X_GEN_TAC else                          *
 *   \(asl,w).((let val x,body = dest_forall w in                            *
 *               [(asl,subst[x',x]body)],                                    *
 *                (\[th]. GEN x (INST [(x,x')] th)))                         *
 *              ? failwith X_GEN_TAC);                                       *
 * Bugfix for HOL88.1.05, MJCG, 4 April 1989                                 *
 * Instantiation before GEN replaced by alpha-conversion after it to         *
 * prevent spurious failures due to bound variable problems when             *
 * quantified variable is free in assumptions.                               *
 * Optimization for the x=x' case added.                                     *
 *---------------------------------------------------------------------------*)

fun X_GEN_TAC x1 : tactic =
   fn (asl, w) =>
      if is_var x1
         then let
                 val (Bvar, Body) = dest_forall w
              in
                 if aconv Bvar x1 then ([(asl, Body)], sing (GEN x1))
                 else ([(asl, subst [Bvar |-> x1] Body)],
                       sing (fn th =>
                               let
                                  val th' = GEN x1 th
                               in
                                  EQ_MP (GEN_ALPHA_CONV Bvar (concl th')) th'
                               end))
              end
              handle HOL_ERR _ => raise ERR "X_GEN_TAC" ""
      else raise ERR "X_GEN_TAC" "need a variable"

(*---------------------------------------------------------------------------*
 * GEN_TAC - Chooses a variant for the user;  for interactive proof          *
 *---------------------------------------------------------------------------*)

val GEN_TAC: tactic =
   fn (asl, w) =>
      let
         val (Bvar, _) = with_exn dest_forall w (ERR "GEN_TAC" "not a forall")
      in
         X_GEN_TAC
             (gen_variant Parse.is_constname "" (free_varsl (w :: asl)) Bvar)
             (asl, w)
      end
val gen_tac = GEN_TAC

(*---------------------------------------------------------------------------*
 * Specialization                                                            *
 *        A(t)                                                               *
 *     ============  t,x                                                     *
 *       !x.A(x)                                                             *
 *                                                                           *
 * Example of use:  generalizing a goal before attempting an inductive proof *
 * as with Boyer and Moore.                                                  *
 *---------------------------------------------------------------------------*)

fun SPEC_TAC (t, x) : tactic =
   fn (asl, w) =>
      ([(asl, mk_forall (x, subst [t |-> x] w))], sing (SPEC t))
      handle HOL_ERR _ => raise ERR "SPEC_TAC" ""

fun ID_SPEC_TAC x : tactic =
   fn (asl, w) =>
      ([(asl, mk_forall (x, w))], sing (SPEC x))
      handle HOL_ERR _ => raise ERR "SPEC_TAC" ""

(*---------------------------------------------------------------------------*
 * Existential introduction                                                  *
 *                                                                           *
 *      ?x.A(x)                                                              *
 *    ==============   t                                                     *
 *       A(t)                                                                *
 *---------------------------------------------------------------------------*)

fun EXISTS_TAC t : tactic =
   fn (asl, w) =>
      let
         val (Bvar, Body) = dest_exists w
      in
         ([(asl, subst [Bvar |-> t] Body)], sing (EXISTS (w, t)))
      end
      handle HOL_ERR _ => raise ERR "EXISTS_TAC" ""
val exists_tac = EXISTS_TAC

fun ID_EX_TAC(g as (_,w)) =
  EXISTS_TAC (fst(dest_exists w)
              handle HOL_ERR _ => raise ERR "ID_EX_TAC" "goal not an exists") g;



(*---------------------------------------------------------------------------*
 * Substitution                                                              *
 *                                                                           *
 * These substitute in the goal;  thus they DO NOT invert the rules SUBS and *
 * SUBS_OCCS, despite superficial similarities.  In fact, SUBS and SUBS_OCCS *
 * are not invertible;  only SUBST is.                                       *
 *---------------------------------------------------------------------------*)

fun GSUBST_TAC substfn ths (asl, w) =
   let
      val (theta1, theta2, theta3) =
         itlist (fn th => fn (theta1, theta2, theta3) =>
                    let
                       val (lhs, rhs) = dest_eq (concl th)
                       val v = Term.genvar (type_of lhs)
                    in
                       ((lhs |-> v) :: theta1,
                        (v |-> rhs) :: theta2,
                        (v |-> SYM th) :: theta3)
                    end) ths ([], [], [])
      val base = substfn theta1 w
   in
      ([(asl, subst theta2 base)], sing (SUBST theta3 base))
   end
   handle HOL_ERR _ => raise ERR "GSUBST_TAC" ""

(*---------------------------------------------------------------------------*
 *      A(ti)                                                                *
 *    ==============   |- ti == ui                                           *
 *      A(ui)                                                                *
 *---------------------------------------------------------------------------*)

fun SUBST_TAC ths =
   GSUBST_TAC subst ths handle HOL_ERR _ => raise ERR "SUBST_TAC" ""

fun SUBST_OCCS_TAC nlths =
   let
      val (nll, ths) = unzip nlths
   in
      GSUBST_TAC (subst_occs nll) ths
   end
   handle HOL_ERR _ => raise ERR "SUBST_OCCS_TAC" ""

(*---------------------------------------------------------------------------*
 *       A(t)                                                                *
 *   ===============   |- t==u                                               *
 *       A(u)                                                                *
 *                                                                           *
 * Works nicely with tacticals.                                              *
 *---------------------------------------------------------------------------*)

fun SUBST1_TAC rthm = SUBST_TAC [rthm]

(*---------------------------------------------------------------------------*
 * Map an inference rule over the assumptions, replacing them.               *
 *---------------------------------------------------------------------------*)

fun RULE_ASSUM_TAC rule : tactic =
   POP_ASSUM_LIST
      (fn asl => MAP_EVERY ASSUME_TAC (rev_itlist (cons o rule) asl []))
val rule_assum_tac = RULE_ASSUM_TAC

fun RULE_L_ASSUM_TAC rule : tactic =
   POP_ASSUM_LIST
      (fn asl => MAP_EVERY ASSUME_TAC (rev_itlist (append o rule) asl []))

(*---------------------------------------------------------------------------*
 * Substitute throughout the goal and its assumptions.                       *
 *---------------------------------------------------------------------------*)

fun SUBST_ALL_TAC rth = SUBST1_TAC rth THEN RULE_ASSUM_TAC (SUBS [rth])

val CHECK_ASSUME_TAC: thm_tactic =
   fn gth =>
      FIRST [CONTR_TAC gth, ACCEPT_TAC gth, OPPOSITE_TAC gth,
             DISCARD_TAC gth, ASSUME_TAC gth]

val STRIP_ASSUME_TAC = REPEAT_TCL STRIP_THM_THEN CHECK_ASSUME_TAC
val strip_assume_tac = STRIP_ASSUME_TAC

(*---------------------------------------------------------------------------*
 * given a theorem:                                                          *
 *                                                                           *
 * |- (?y1. (x=t1(y1)) /\ B1(x,y1))  \/...\/  (?yn. (x=tn(yn)) /\ Bn(x,yn))  *
 *                                                                           *
 * where each y is a vector of zero or more variables and each Bi is a       *
 * conjunction (Ci1 /\ ... /\ Cin)                                           *
 *                                                                           *
 *                      A(x)                                                 *
 *     ===============================================                       *
 *     [Ci1(tm,y1')] A(t1)  . . .  [Cin(tm,yn')] A(tn)                       *
 *                                                                           *
 * such definitions specify a structure as having n different possible       *
 * constructions (the ti) from subcomponents (the yi) that satisfy various   *
 * constraints (the Cij).                                                    *
 *---------------------------------------------------------------------------*)

val STRUCT_CASES_TAC =
   REPEAT_TCL STRIP_THM_THEN (fn th => SUBST1_TAC th ORELSE ASSUME_TAC th)

val FULL_STRUCT_CASES_TAC =
   REPEAT_TCL STRIP_THM_THEN (fn th => SUBST_ALL_TAC th ORELSE ASSUME_TAC th)

(*---------------------------------------------------------------------------*
 * COND_CASES_TAC: tactic for doing a case split on the condition p          *
 *                 in a conditional (p => u | v).                            *
 *                                                                           *
 * Find a conditional "p => u | v" that is free in the goal and whose        *
 * condition p is not a constant. Perform a case split on the condition.     *
 *                                                                           *
 *      t[p=>u|v]                                                            *
 *    =================  COND_CASES_TAC                                      *
 *       {p}  t[u]                                                           *
 *       {~p}  t[v]                                                          *
 *                                                                           *
 *     [Revised: TFM 90.05.11]                                               *
 *---------------------------------------------------------------------------*)

fun GEN_COND_CASES_TAC P (asl, w) =
   let
      val cond = find_term (fn tm => P tm andalso free_in tm w) w
                   handle HOL_ERR _ => raise ERR "GEN_COND_CASES_TAC" ""
      val (cond, larm, rarm) = dest_cond cond
      val inst = INST_TYPE [Type.alpha |-> type_of larm] COND_CLAUSES
      val (ct, cf) = CONJ_PAIR (SPEC rarm (SPEC larm inst))
      fun subst_tac th c = SUBST1_TAC th THEN SUBST1_TAC (SUBS [th] c)
   in
      DISJ_CASES_THEN2
        (fn th =>
           subst_tac (EQT_INTRO th) ct THEN ASSUME_TAC th)
        (fn th =>
           subst_tac (EQF_INTRO th) cf THEN ASSUME_TAC th)
        (SPEC cond EXCLUDED_MIDDLE)
        (asl, w)
   end

local
   fun bool_can P x = P x handle HOL_ERR _ => false
in
   val COND_CASES_TAC =
      GEN_COND_CASES_TAC (bool_can (not o is_const o #1 o dest_cond))
end

(*---------------------------------------------------------------------------
      Version of COND_CASES_TAC that handles nested conditionals
      in the test of a conditional nicely (by not putting them onto
      the assumptions).
 ---------------------------------------------------------------------------*)

val IF_CASES_TAC =
   let
      fun test tm =
         let
            val (b,_,_) = dest_cond tm
         in
            not (is_const b orelse is_cond b)
         end
         handle HOL_ERR _ => false
   in
      GEN_COND_CASES_TAC test
   end

(*---------------------------------------------------------------------------*
 * Cases on  |- p=T  \/  p=F                                                 *
 *---------------------------------------------------------------------------*)

fun BOOL_CASES_TAC p = STRUCT_CASES_TAC (SPEC p BOOL_CASES_AX)

(*---------------------------------------------------------------------------*
 * Strip one outer !, /\, ==> from the goal.                                 *
 *---------------------------------------------------------------------------*)

fun STRIP_GOAL_THEN ttac = FIRST [GEN_TAC, CONJ_TAC, DISCH_THEN ttac]

(*---------------------------------------------------------------------------*
 * Like GEN_TAC but fails if the term equals the quantified variable.        *
 *---------------------------------------------------------------------------*)

fun FILTER_GEN_TAC tm : tactic =
   fn (asl, w) =>
      if is_forall w andalso not (aconv tm (fst (dest_forall w)))
         then GEN_TAC (asl, w)
      else raise ERR "FILTER_GEN_TAC" ""

(*---------------------------------------------------------------------------*
 * Like DISCH_THEN but fails if the antecedent mentions the given term.      *
 *---------------------------------------------------------------------------*)

fun FILTER_DISCH_THEN ttac tm = fn (asl, w) =>
   if is_imp w andalso not (free_in tm (fst (dest_imp w)))
      then DISCH_THEN ttac (asl, w)
   else raise ERR "FILTER_DISCH_THEN" ""

(*---------------------------------------------------------------------------*
 * Like STRIP_THEN but preserves any part of the goal mentioning the term.   *
 *---------------------------------------------------------------------------*)

fun FILTER_STRIP_THEN ttac tm =
   FIRST [FILTER_GEN_TAC tm, FILTER_DISCH_THEN ttac tm, CONJ_TAC]

fun DISCH_TAC g =
   DISCH_THEN ASSUME_TAC g handle HOL_ERR _ => raise ERR "DISCH_TAC" ""

val FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC

val DISJ_CASES_TAC = DISJ_CASES_THEN ASSUME_TAC

val CHOOSE_TAC = CHOOSE_THEN ASSUME_TAC

fun X_CHOOSE_TAC x = X_CHOOSE_THEN x ASSUME_TAC

fun STRIP_TAC g =
   STRIP_GOAL_THEN STRIP_ASSUME_TAC g
   handle HOL_ERR _ => raise ERR "STRIP_TAC" ""
val strip_tac = STRIP_TAC

val FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC

(*---------------------------------------------------------------------------*
 * Cases on  |- t \/ ~t                                                      *
 *---------------------------------------------------------------------------*)

fun ASM_CASES_TAC t = DISJ_CASES_TAC (SPEC t EXCLUDED_MIDDLE)

(*---------------------------------------------------------------------------*
 * A tactic inverting REFL (from tfm).                                       *
 *                                                                           *
 *       A = A                                                               *
 *   ==============                                                          *
 *                                                                           *
 * Revised to work if lhs is alpha-equivalent to rhs      [TFM 91.02.02]     *
 * Also revised to retain assumptions.                                       *
 *---------------------------------------------------------------------------*)

fun REFL_TAC (asl, g) =
   let
      val (lhs, rhs) = with_exn dest_eq g (ERR "REFL_TAC" "not an equation")
      val asms = itlist ADD_ASSUM asl
   in
      if aconv lhs rhs then ([], K (asms (REFL lhs)))
      else raise ERR "REFL_TAC" "lhs and rhs not alpha-equivalent"
   end

(*---------------------------------------------------------------------------*
 * UNDISCH_TAC - moves one of the assumptions as LHS of an implication       *
 * to the goal (fails if named assumption not in assumptions)                *
 *                                                                           *
 * UNDISCH_TAC: term -> tactic                                               *
 *               tm                                                          *
 *                                                                           *
 *         [ t1;t2;...;tm;tn;...tz ]  t                                      *
 *   ======================================                                  *
 *        [ t1;t2;...;tn;...tz ]  tm ==> t                                   *
 *---------------------------------------------------------------------------*)

fun UNDISCH_TAC wf (asl, w) =
   if op_mem term_eq wf asl
      then ([(op_set_diff term_eq asl [wf], mk_imp (wf, w))],
            UNDISCH o Lib.trye hd)
   else raise ERR "UNDISCH_TAC" "Specified term not in assumption list"

(*---------------------------------------------------------------------------*
 * AP_TERM_TAC: Strips a function application off the lhs and rhs of an      *
 * equation.  If the function is not one-to-one, does not preserve           *
 * equivalence of the goal and subgoal.                                      *
 *                                                                           *
 *   f x = f y                                                               *
 * =============                                                             *
 *     x = y                                                                 *
 *                                                                           *
 * Added: TFM 88.03.31                                                       *
 * Revised: TFM 91.02.02                                                     *
 *---------------------------------------------------------------------------*)

local
   fun ER s = ERR "AP_TERM_TAC" s
in
   fun AP_TERM_TAC (asl, gl) =
      let
         val (lhs, rhs) = with_exn dest_eq gl (ER "not an equation")
         val (g, x) = with_exn dest_comb lhs (ER "lhs not a comb")
         val (f, y) = with_exn dest_comb rhs (ER "rhs not a comb")
      in
         if not (term_eq f g)
            then raise ER "functions on lhs and rhs differ"
         else ([(asl, mk_eq (x, y))], AP_TERM f o Lib.trye hd)
      end
end

(*---------------------------------------------------------------------------*
 * AP_THM_TAC: inverts the AP_THM inference rule.                            *
 *                                                                           *
 *   f x = g x                                                               *
 * =============                                                             *
 *     f = g                                                                 *
 *                                                                           *
 * Added: TFM 91.02.02                                                       *
 *---------------------------------------------------------------------------*)

local
   fun ER s = ERR "AP_THM_TAC" s
in
   fun AP_THM_TAC (asl, gl) =
      let
         val (lhs, rhs) = with_exn dest_eq gl (ER "not an equation")
         val (g, x) = with_exn dest_comb lhs (ER "lhs not a comb")
         val (f, y) = with_exn dest_comb rhs (ER "rhs not a comb")
      in
         if not (term_eq x y)
            then raise ER "arguments on lhs and rhs differ"
         else ([(asl, mk_eq (g, f))], C AP_THM x o Lib.trye hd)
      end
end

(*---------------------------------------------------------------------------*
 * MK_COMB_TAC - reduces ?- f x = g y to ?- f = g and ?- x = y     (JRH)     *
 *---------------------------------------------------------------------------*)

local
   fun ER s = ERR "MK_COMB_TAC" s
in
   fun MK_COMB_TAC (asl, w) =
      let
         val (lhs, rhs) = with_exn dest_eq w (ER "not an equation")
         val (l1, l2) = with_exn dest_comb lhs (ER "lhs not a comb")
         val (r1, r2) = with_exn dest_comb rhs (ER "rhs not a comb")
      in
         ([(asl, mk_eq (l1, r1)), (asl, mk_eq (l2, r2))],
          end_itlist (curry MK_COMB))
      end
end

(*---------------------------------------------------------------------------*
 * BINOP_TAC - reduces "$op x y = $op u v" to "x = u" and "y = v"    (JRH)   *
 *---------------------------------------------------------------------------*)

val BINOP_TAC = MK_COMB_TAC THENL [AP_TERM_TAC, ALL_TAC]

(*---------------------------------------------------------------------------*
 * ABS_TAC: inverts the ABS inference rule.                                  *
 *                                                                           *
 *   \x. f x = \x. g x                                                       *
 * =====================                                                     *
 *       f x = g x                                                           *
 *                                                                           *
 * Added: TT 2009.12.23                                                      *
 *---------------------------------------------------------------------------*)

local
   fun ER s = ERR "ABS_TAC" s
in
   fun ABS_TAC (asl: term list, gl) =
      let
         val (lhs, rhs) = with_exn dest_eq gl (ER "not an equation")
         val (x, g) = with_exn dest_abs lhs (ER "lhs not an abstraction")
         val (y, f) = with_exn dest_abs rhs (ER "rhs not an abstraction")
         val f_thm = if aconv x y then REFL rhs else ALPHA_CONV x rhs
         val (_, f') = dest_abs (rand (concl f_thm))
      in
         ([(asl, mk_eq (g, f'))],
          CONV_RULE (RHS_CONV (K (GSYM f_thm))) o ABS x o Lib.trye hd)
      end
end

(*---------------------------------------------------------------------------*
 * NTAC n tac - Applies the tactic the given number of times.                *
 *---------------------------------------------------------------------------*)

fun NTAC n tac = funpow n (curry op THEN tac) ALL_TAC
val ntac = NTAC

(*---------------------------------------------------------------------------*
 * WEAKEN_TAC tm - Removes the first term meeting P from the hypotheses      *
 * of the goal.                                                              *
 *---------------------------------------------------------------------------*)

fun WEAKEN_TAC P : tactic =
   fn (asl, w) =>
      let
         fun robustP x = Lib.trye P x handle HOL_ERR _ => false
         val (tm, rst) =
            Lib.pluck robustP asl
            handle HOL_ERR _ =>
                   raise ERR "WEAKEN_TAC" "no matching item found in hypotheses"
      in
         ([(rst, w)], sing (ADD_ASSUM tm))
      end

(* ---------------------------------------------------------------------*
 * Accept a theorem that, properly instantiated, satisfies the goal     *
 * ---------------------------------------------------------------------*)

fun MATCH_ACCEPT_TAC thm : tactic =
   let
      val fmatch = PART_MATCH Lib.I thm
      fun atac (asl, w) = ([], Lib.K (fmatch w))
   in
      REPEAT GEN_TAC THEN atac
   end
   handle HOL_ERR _ => raise ERR "MATCH_ACCEPT_TAC" ""

(* ---------------------------------------------------------------------*
 * prim_irule : Similar to MATCH_ACCEPT_TAC but                         *
 * (1) allows substitution in hypotheses of the supplied theorem        *
 * (2) adds new subgoals for those hypotheses                           *
 * ---------------------------------------------------------------------*)

fun prim_irule thm (asl, w) =
  let val matchsub = match_term (concl thm) w ;
    val (subthm, subhyps) = INST_TT_HYPS matchsub thm ;
  in ADD_SGS_TAC subhyps (ACCEPT_TAC subthm) (asl, w) end ;

(* --------------------------------------------------------------------------*
 * MATCH_MP_TAC: Takes a theorem of the form                                 *
 *                                                                           *
 *       |- !x1..xn. A ==> !y1 ... ym. B                                     *
 *                                                                           *
 * and matches B to the goal, reducing it to the subgoal consisting of       *
 * some existentially-quantified instance of A:                              *
 *                                                                           *
 *      !v1...vi. B                                                          *
 * ======================= MATCH_MP_TAC |- !x1...1n. A ==> !y1...ym. B       *
 *      ?z1...zp. A                                                          *
 *                                                                           *
 * where {z1,...,zn} is the subset of {x1,...,xn} whose elements do not      *
 * appear free in B.                                                         *
 *                                                                           *
 * Added: TFM 88.03.31                                                       *
 * Revised: TFM 91.04.20                                                     *
 *                                                                           *
 * Old version:                                                              *
 *                                                                           *
 * let MATCH_MP_TAC thm:tactic (gl,g) =                                      *
 *     let imp = ((PART_MATCH (snd o dest_imp) thm) g) ?                     *
 *               failwith `MATCH_MP_TAC` in                                  *
 *     ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl));             *
 * --------------------------------------------------------------------------*)

local
   fun efn v (tm, th) =
      let val ntm = mk_exists (v, tm) in (ntm, CHOOSE (v, ASSUME ntm) th) end
in
   fun MATCH_MP_TAC thm : tactic =
      let
         val lconsts =
            HOLset.intersection (FVL [concl thm] empty_tmset, hyp_frees thm)
        val hyptyvars = HOLset.listItems (hyp_tyvars thm)
        val (gvs, imp) = strip_forall (concl thm)
      in
          fn (A,g) =>
             let
                 val (ant, conseq) =
                     with_exn dest_imp imp (ERR "MATCH_MP_TAC" "Not an implication")
                 val (cvs, con) = strip_forall conseq
                 val th1 = SPECL cvs (UNDISCH (SPECL gvs thm))
                 val (vs, evs) = partition (C Term.free_in con) gvs
                 val th2 = uncurry DISCH (itlist efn evs (ant, th1))
                 val (vs, gl) = strip_forall g
                 val ins = match_terml hyptyvars lconsts con gl
                           handle HOL_ERR _ => raise ERR "MATCH_MP_TAC" "No match"
                 val ith = INST_TY_TERM ins th2
                 val gth = GENL vs (UNDISCH ith)
                           handle HOL_ERR _ => raise ERR "MATCH_MP_TAC"
                                                     "Generalized var(s)."
                 val ant = fst (dest_imp (concl ith))
             in
                 ([(A, ant)], fn thl => MP (DISCH ant gth) (hd thl))
             end
      end
   val match_mp_tac = MATCH_MP_TAC
end

(* --------------------------------------------------------------------------*
 * irule: similar to MATCH_MP_TAC, but                                       *
 * (1) uses conclusion following more than one ==>                           *
 * (2) where multiple assumptions involve the same variable that is not in   *
 *     the conclusion (as y in x = y ==> y = z ==> x = z), collects them     *
 *     and existentially quantifies                                          *
 * (3) hypotheses of the theorem provided also become new subgoals           *
 * --------------------------------------------------------------------------*)

fun irule thm = let
  val th' = IRULE_CANON thm
in
  if th' |> concl |> strip_forall |> #2 |> is_imp then
    MATCH_MP_TAC th' THEN REPEAT CONJ_TAC
  else MATCH_ACCEPT_TAC th'
end
val IRULE_TAC = irule

fun impl_tac (g as (_,w)) =
  let
    val (h0,c) = dest_imp w
    val (a,h) = dest_imp h0
  in
    SUBGOAL_THEN a (fn ath => DISCH_THEN (fn impth => MP_TAC (MP impth ath)))
  end g

fun impl_keep_tac (g as (_,w)) =
  let
    val (h0,c) = dest_imp w
    val (a,h) = dest_imp h0
  in
    SUBGOAL_THEN a
       (fn ath => DISCH_THEN
                    (fn impth => ASSUME_TAC ath THEN MP_TAC (MP impth ath)))
  end g


(* ----------------------------------------------------------------------*
 * Definition of the standard resolution tactics IMP_RES_TAC and RES_TAC *
 *                                                                       *
 * The function SA is like STRIP_ASSUME_TAC, except that it does not     *
 * strip off existential quantifiers. And ST is like STRIP_THM_THEN,     *
 * except that it also does not strip existential quantifiers.           *
 *                                                                       *
 * Old version: deleted for HOL version 1.12      [TFM 91.01.17]         *
 *                                                                       *
 * let (IMP_RES_TAC,RES_TAC) =                                           *
 *    let ST = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN] in            *
 *    let SA = (REPEAT_TCL ST) CHECK_ASSUME_TAC in                       *
 *        (IMP_RES_THEN SA, RES_THEN SA);                                *
 *                                                                       *
 * The "new" versions of IMP_RES_TAC and RES_TAC: repeatedly resolve,    *
 * and then add FULLY stripped, final, result(s) to the assumptions.     *
 * ----------------------------------------------------------------------*)

local
   open Thm_cont
in
   fun IMP_RES_TAC th g =
      IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g
      handle HOL_ERR _ => ALL_TAC g

   fun RES_TAC g =
      RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g
      handle HOL_ERR _ => ALL_TAC g

   val res_tac = RES_TAC
   val imp_res_tac = IMP_RES_TAC
end

(*--------------------------------------------------------------------------*
 *   Assertional style reasoning                                            *
 *--------------------------------------------------------------------------*)

(* First we need a variant on THEN. *)

fun THENF (tac1: tactic, tac2: tactic, tac3: tactic) g =
    case tac1 g of
       (h::rst, p) =>
          let
             val (gl0, p0) = tac2 h
             val (gln, pn) = unzip (map tac3 rst)
             val gll = gl0 @ flatten gln
          in
             (gll, p o mapshape (length gl0 :: map length gln) (p0 :: pn))
          end
     | x => x

infix 8 via;

fun (tm via tac) =
   THENF (SUBGOAL_THEN tm STRIP_ASSUME_TAC, tac, ALL_TAC)
   handle e as HOL_ERR _ => raise ERR "via" ""

(*--------------------------------------------------------------------------*
 *   Tactic for beta-reducing a goal.                                       *
 *--------------------------------------------------------------------------*)

val BETA_TAC = CONV_TAC (DEPTH_CONV BETA_CONV)

(* ---------------------------------------------------------------------*
 * Accept a theorem that, properly instantiated, satisfies the goal     *
 * ---------------------------------------------------------------------*)

fun HO_MATCH_ACCEPT_TAC thm =
   let
      val fmatch = HO_PART_MATCH I thm
      fun atac (asl, w) = ([], K (fmatch w))
   in
      REPEAT GEN_TAC THEN atac
   end
   handle HOL_ERR _ => raise ERR "HO_MATCH_ACCEPT_TAC" ""

(*-------------------------------------------------------------------------*
 * Simplified version of HO_MATCH_MP_TAC to avoid quantifier troubles.     *
 *-------------------------------------------------------------------------*)

fun HO_BACKCHAIN_TAC th =
   let
      val match_fn = HO_PART_MATCH (snd o dest_imp_only) th
   in
      fn (asl, w) =>
         let
            val th1 = match_fn w
            val (ant, _) = dest_imp_only (concl th1)
         in
            ([(asl, ant)], sing (HO_MATCH_MP th1))
         end
   end

fun HO_MATCH_MP_TAC th =
   let
      val sth =
         let
            val tm = concl th
            val (avs, bod) = strip_forall tm
            val (ant, conseq) = dest_imp_only bod
            val th1 = SPECL avs (ASSUME tm)
            val th2 = UNDISCH th1
            val evs =
               filter (fn v => free_in v ant andalso not (free_in v conseq)) avs
            val th3 = itlist SIMPLE_CHOOSE evs (DISCH tm th2)
            val tm3 = Lib.trye hd (hyp th3)
         in
            MP (DISCH tm (GEN_ALL (DISCH tm3 (UNDISCH th3)))) th
         end
         handle HOL_ERR _ => raise ERR "HO_MATCH_MP_TAC" "Bad theorem"
      val match_fun = HO_PART_MATCH (snd o dest_imp_only) sth
   in
      fn (asl, w) =>
         let
            val xth = match_fun w
            val lant = fst (dest_imp_only (concl xth))
         in
            ([(asl, lant)], MP xth o Lib.trye hd)
         end
         handle e => raise (wrap_exn "Tactic" "HO_MATCH_MP_TAC" e)
   end

val ho_match_mp_tac = HO_MATCH_MP_TAC

(*----------------------------------------------------------------------*
 *   Tactics explicitly declaring subgoals.                             *
 *----------------------------------------------------------------------*)

fun SUFF_TAC tm (al, c) =
   ([(al, mk_imp (tm, c)), (al, tm)],
    fn [th1, th2] => MP th1 th2
     | _ => raise ERR "SUFF_TAC" "panic")
val suff_tac = SUFF_TAC

fun KNOW_TAC tm = REVERSE (SUFF_TAC tm)

(*----------------------------------------------------------------------*
 *  DEEP_INTROk_TAC : thm -> tactic -> tactic                           *
 *----------------------------------------------------------------------*)

fun gvarify th =
   let
      val th = SPEC_ALL th
      val fvs = FVL [concl th] empty_tmset
      val hfvs = hyp_frees th
      val true_frees = HOLset.difference (fvs, hfvs)
      fun foldthis (fv, acc) = (fv |-> genvar (type_of fv)) :: acc
   in
      INST (HOLset.foldl foldthis [] true_frees) th
   end

fun IMP2AND_CONV t =
   if is_imp t
      then (RAND_CONV IMP2AND_CONV THENC TRY_CONV (REWR_CONV AND_IMP_INTRO)) t
   else ALL_CONV t

fun DEEP_INTROk_TAC th tac (asl, g) =
   let
      val th = th |> CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV THENC
                                STRIP_QUANT_CONV IMP2AND_CONV)
                  |> GEN_ALL
      val hyfrees = hyp_frees th
      val hytyvars = hyp_tyvars th
      val (_, Ppattern) = th |> concl |> strip_forall |> #2 |> dest_imp
      val (Pvar, pattern) = dest_comb Ppattern
      val _ = is_var Pvar
              orelse raise ERR "DEEP_INTROk_TAC"
                               "Conclusion not of form ``var (pattern)``"
      fun test (bvs, t) =
         let
            val ((theta_tms, tmids), _) =
              raw_match (HOLset.listItems hytyvars) hyfrees pattern t ([], [])
            val bv_set = HOLset.fromList Term.compare bvs
            fun testtheta {redex, residue} =
               let
                  val rfrees = FVL [residue] empty_tmset
               in
                  HOLset.isEmpty (HOLset.intersection (rfrees, bv_set))
               end
         in
            List.all testtheta theta_tms
            andalso HOLset.isEmpty (HOLset.intersection (bv_set, tmids))
         end
         handle HOL_ERR _ (* if match fails *) => false
      fun continuation subt =
         (CONV_TAC (UNBETA_CONV subt) THEN
          MATCH_MP_TAC th THEN BETA_TAC THEN tac) (asl, g)
   in
      case bvk_find_term test continuation g of
         SOME result => result
       | NONE => raise ERR "DEEP_INTROk_TAC" "No matching sub-terms"
   end

fun DEEP_INTRO_TAC th = DEEP_INTROk_TAC th ALL_TAC

(*----------------------------------------------------------------------*
 *  SELECT_ELIM_TAC                                                     *
 *    eliminates a select term from the goal.                           *
 *----------------------------------------------------------------------*)

val SELECT_ELIM_TAC = DEEP_INTRO_TAC SELECT_ELIM_THM


(*----------------------------------------------------------------------*
 *  HINT_EXISTS_TAC                                                     *
 *    instantiates an existential by using hints from the assumptions.  *
 *----------------------------------------------------------------------*)

fun HINT_EXISTS_TAC g =
  let
    val (hs,c) = g
    val (v,c') = dest_exists c
    val (vs,c') = strip_exists c'
    fun hyp_match c h =
      if exists (C (op_mem aconv) vs) (free_vars c) then fail ()
      else match_term c h
    val (subs,_) = tryfind (C tryfind hs o hyp_match) (strip_conj c')
    val witness =
      case subs of
         [] => v
        |[{redex = u, residue = t}] =>
            if aconv u v then t else failwith "HINT_EXISTS_TAC not applicable"
        |_ => failwith "HINT_EXISTS_TAC not applicable"
  in
    EXISTS_TAC witness g
  end;

(* ----------------------------------------------------------------------
    part_match_exists_tac : (term -> term) -> term -> tactic

    part_match_exists_tac selfn tm (asl,w)

    w must be of shape ?v1 .. vn. body.

    Apply selfn to body extracting a term that is then matched against
    tm.  Instantiate the existential variables according to this match.

   ---------------------------------------------------------------------- *)

fun part_match_exists_tac selfn tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val c = selfn b
    val cfvs = FVL [c] empty_tmset
    val constvars = HOLset.difference(cfvs, HOLset.fromList Term.compare vs)
    val ((tms0,tmfixed),_) = raw_match [] constvars c tm ([], [])
    val tms =
        tms0 @ HOLset.foldl
                 (fn (v,acc) =>
                     if op_mem aconv v vs then {redex=v,residue=v}::acc
                     else acc)
                 [] tmfixed
    val xs = map #redex tms
    val ys = map #residue tms
    fun sorter ls = xs@(List.filter(not o Lib.C (op_mem aconv) xs)ls)
  in
    CONV_TAC(RESORT_EXISTS_CONV sorter) >> map_every exists_tac ys
  end g

end (* Tactic *)
