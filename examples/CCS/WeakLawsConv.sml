(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure WeakLawsConv :> WeakLawsConv =
struct

open HolKernel Parse boolLib bossLib;

open IndDefRules;
open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory StrongLawsConv;
open WeakEQTheory WeakEQLib WeakLawsTheory;

infixr 0 OE_THENC OE_ORELSEC;

(******************************************************************************)
(*                                                                            *)
(*             Conversions and tactics for applying the laws for              *)
(*              observation equivalence through strong equivalence            *)
(*                                                                            *)
(******************************************************************************)

(* Define the conversions and tactics for the application of the laws for
   WEAK_EQUIV (through the conversions and tactics for strong equivalence). *)
fun STRONG_TO_WEAK_EQUIV_CONV (c: conv) tm =
    MATCH_MP STRONG_IMP_WEAK_EQUIV (c tm);

val [OE_SUM_IDEMP_CONV, OE_SUM_NIL_CONV, OE_RELAB_ELIM_CONV,
     OE_RESTR_ELIM_CONV, OE_PAR_ELIM_CONV, OE_EXP_THM_CONV,
     OE_REC_UNF_CONV] =
    map STRONG_TO_WEAK_EQUIV_CONV
        [STRONG_SUM_IDEMP_CONV, STRONG_SUM_NIL_CONV, STRONG_RELAB_ELIM_CONV,
         STRONG_RESTR_ELIM_CONV, STRONG_PAR_ELIM_CONV, STRONG_EXP_THM_CONV,
         STRONG_REC_UNF_CONV];

val [OE_SUM_IDEMP_TAC, OE_SUM_NIL_TAC, OE_RELAB_ELIM_TAC,
     OE_RESTR_ELIM_TAC, OE_PAR_ELIM_TAC, OE_REC_UNF_TAC] =
    map OE_LHS_CONV_TAC
        [STRONG_SUM_IDEMP_CONV, STRONG_SUM_NIL_CONV, STRONG_RELAB_ELIM_CONV,
         STRONG_RESTR_ELIM_CONV, STRONG_PAR_ELIM_CONV, STRONG_REC_UNF_CONV];

val OE_RHS_RELAB_ELIM_TAC = OE_RHS_CONV_TAC STRONG_RELAB_ELIM_CONV;

(* TODO: idem for the other operators *)

(* Tactic for applying the expansion theorem (parallel and restriction operators). *)
val OE_EXP_THM_TAC :tactic =
    fn (asl, w) => let
        val (opt, t1, t2) = args_equiv w
    in
        if opt ~~ mk_const ("WEAK_EQUIV", type_of opt) then
            let val thm = MATCH_MP STRONG_IMP_WEAK_EQUIV (STRONG_EXP_THM_CONV t1);
                val (t1', t') = args_thm thm (* t1' = t1 *)
            in
                if (t' ~~ t2) then
                    ([], fn [] => OE_TRANS thm (ISPEC t' WEAK_EQUIV_REFL))
                else
                    ([(asl, ``WEAK_EQUIV ^t' ^t2``)], fn [thm'] => OE_TRANS thm thm')
            end
        else
            failwith "the goal is not an WEAK_EQUIV relation"
    end;

(******************************************************************************)
(*                                                                            *)
(*           Basic conversions and tactics for applying the laws for          *)
(*                        observation equivalence                             *)
(*                                                                            *)
(******************************************************************************)

(* Conversion that proves whether or not a CCS term is stable. *)
fun STABLE_CONV tm = let
    fun list2_pair [x, y] = (x, y);
    val f = (fn c => map (snd o dest_eq) (strip_conj c));
    val thm = CCS_TRANS_CONV tm;
    val lp = map (list2_pair o f) (strip_disj (rconcl thm));
    val taul = filter (fn (act, _) => is_tau act) lp;
    val ccs_typ = type_of tm
in
    if (null taul) then
        prove (``STABLE ^tm``,
    REWRITE_TAC [STABLE, thm]
 >> REPEAT STRIP_TAC
 >| list_apply_tac
      (fn act => CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME ``u = tau``, Action_distinct]
                                                (ASSUME ``u = ^act``)))
      (fst (split lp)))
    else
        prove (``~STABLE ^tm``,
    REWRITE_TAC [STABLE, thm]
 >> CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV)
 >> EXISTS_TAC (fst (hd taul))
 >> EXISTS_TAC (snd (hd taul))
 >> REWRITE_TAC [])
end;

(* Define the function OE_SUB_CONV. *)
fun OE_SUB_CONV (c: conv) tm =
  if is_prefix tm then
      let val (u, P) = args_prefix tm;
          val thm = c P
      in
          ISPEC u (MATCH_MP WEAK_EQUIV_SUBST_PREFIX thm)
      end
  else if is_sum tm then
      let val (t1, t2) = args_sum tm;
          val thm1 = c t1
          and thm2 = c t2;
          val (t1', t1'') = args_thm thm1 (* t1' = t1, t2' = t2 *)
          and (t2', t2'') = args_thm thm2
      in
          if t1' ~~ t1'' andalso t2' ~~ t2'' then
              ISPEC (mk_sum (t1', t2')) WEAK_EQUIV_REFL
          else if t1' ~~ t1'' then
              ISPEC t1' (MATCH_MP WEAK_EQUIV_SUBST_SUM_L
                                  (LIST_CONJ [thm2, STABLE_CONV t2', STABLE_CONV t2'']))
          else if t2' ~~ t2'' then
              ISPEC t2' (MATCH_MP WEAK_EQUIV_SUBST_SUM_R
                                  (LIST_CONJ [thm1, STABLE_CONV t1', STABLE_CONV t1'']))
          else
              MATCH_MP WEAK_EQUIV_PRESD_BY_SUM
                       (LIST_CONJ [thm1, STABLE_CONV t1', STABLE_CONV t1'',
                                   thm2, STABLE_CONV t2', STABLE_CONV t2''])
              handle HOL_ERR _ => failwith "stable conditions not satisfied"
      end
  else if is_par tm then
      let val (t1, t2) = args_par tm;
          val thm1 = c t1
          and thm2 = c t2
      in
          MATCH_MP WEAK_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2)
      end
  else if is_restr tm then
      let val (P, L) = args_restr tm;
          val thm = c P
      in
          ISPEC L (MATCH_MP WEAK_EQUIV_SUBST_RESTR thm)
      end
  else if is_relab tm then
      let val (P, rf) = args_relab tm;
          val thm = c P
      in
          ISPEC rf (MATCH_MP WEAK_EQUIV_SUBST_RELAB thm)
      end
  else
      OE_ALL_CONV tm;

(* Define the function OE_DEPTH_CONV. *)
fun OE_DEPTH_CONV (c: conv) t =
  OE_SUB_CONV ((OE_DEPTH_CONV c) OE_THENC (OE_REPEATC c)) t;

(* Define the function OE_TOP_DEPTH_CONV. *)
fun OE_TOP_DEPTH_CONV (c: conv) t =
   ((OE_REPEATC c) OE_THENC
    (OE_SUB_CONV (OE_TOP_DEPTH_CONV c)) OE_THENC
    ((c OE_THENC (OE_TOP_DEPTH_CONV c)) OE_ORELSEC OE_ALL_CONV))
   t;

(* Define the function OE_SUBST for substitution in WEAK_EQUIV terms. *)
fun OE_SUBST thm tm = let
    val (ti, ti') = args_thm thm
in
    if tm ~~ ti then thm
    else if is_prefix tm then
        let val (u, t) = args_prefix tm;
            val thm1 = OE_SUBST thm t
        in
            ISPEC u (MATCH_MP WEAK_EQUIV_SUBST_PREFIX thm1)
        end
    else if is_sum tm then
        let val (t1, t2) = args_sum tm;
            val thm1 = OE_SUBST thm t1
            and thm2 = OE_SUBST thm t2;
            val (t1', t1'') = args_thm thm1 (* t1' = t1, t2' = t2 *)
            and (t2', t2'') = args_thm thm2
        in
            if (t1' ~~ t1'') andalso (t2' ~~ t2'') then
                ISPEC (mk_sum (t1', t2')) WEAK_EQUIV_REFL
            else if (t1' ~~ t1'') then
                ISPEC t1' (MATCH_MP WEAK_EQUIV_SUBST_SUM_L
                                    (LIST_CONJ [thm2, STABLE_CONV t2', STABLE_CONV t2'']))
            else if (t2' ~~ t2'') then
                ISPEC t2' (MATCH_MP WEAK_EQUIV_SUBST_SUM_R
                                    (LIST_CONJ [thm1, STABLE_CONV t1', STABLE_CONV t1'']))
            else
                MATCH_MP WEAK_EQUIV_PRESD_BY_SUM
                         (LIST_CONJ [thm1, STABLE_CONV t1', STABLE_CONV t1'',
                                     thm2, STABLE_CONV t2', STABLE_CONV t2''])
                handle HOL_ERR _ =>
                       failwith "stable conditions not satisfied"
        end
    else if is_par tm then
        let val (t1, t2) = args_par tm;
            val thm1 = OE_SUBST thm t1
            and thm2 = OE_SUBST thm t2
        in
            MATCH_MP WEAK_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2)
        end
    else if is_restr tm then
        let val (t, L) = args_restr tm;
            val thm1 = OE_SUBST thm t
        in
            ISPEC L (MATCH_MP WEAK_EQUIV_SUBST_RESTR thm1)
        end
    else if is_relab tm then
        let val (t, rf) = args_relab tm;
            val thm1 = OE_SUBST thm t
        in
            ISPEC rf (MATCH_MP WEAK_EQUIV_SUBST_RELAB thm1)
        end
    else
        OE_ALL_CONV tm
end;

(* Define the tactic OE_LHS_SUBST1_TAC: thm_tactic which substitutes a theorem
   in the left-hand side of an observation equivalence. *)
fun OE_LHS_SUBST1_TAC thm :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if opt ~~ mk_const ("WEAK_EQUIV", type_of opt) then
          let val thm' = OE_SUBST thm t1;
              val (t1', t') = args_thm thm' (* t1' = t1 *)
          in
              if (t' ~~ t2) then
                  ([], fn [] => OE_TRANS thm' (ISPEC t' WEAK_EQUIV_REFL))
              else
                  ([(asl, ``WEAK_EQUIV ^t' ^t2``)], fn [thm''] => OE_TRANS thm' thm'')
          end
      else
          failwith "the goal is not an WEAK_EQUIV relation"
  end;

(* The tactic OE_LHS_SUBST_TAC substitutes a list of theorems in the left-hand
   side of an observation equivalence. *)
fun OE_LHS_SUBST_TAC thmlist = EVERY (map OE_LHS_SUBST1_TAC thmlist);

(* The tactic OE_RHS_SUBST1_TAC substitutes a theorem in the right-hand side
   of an observation equivalence. *)
fun OE_RHS_SUBST1_TAC thm =
    REPEAT GEN_TAC
 >> RULE_TAC WEAK_EQUIV_SYM
 >> OE_LHS_SUBST1_TAC thm
 >> RULE_TAC WEAK_EQUIV_SYM;

(* The tactic OE_RHS_SUBST_TAC substitutes a list of theorems in the right-hand
   side of an observation equivalence. *)
fun OE_RHS_SUBST_TAC thmlist =
    REPEAT GEN_TAC
 >> RULE_TAC WEAK_EQUIV_SYM
 >> OE_LHS_SUBST_TAC thmlist
 >> RULE_TAC WEAK_EQUIV_SYM;

(* The tactic OE_SUBST1_TAC (OE_SUBST_TAC) substitutes a (list of) theorem(s)
   in both sides of an observation equivalence. *)
fun OE_SUBST1_TAC thm =
    OE_LHS_SUBST1_TAC thm
 >> OE_RHS_SUBST1_TAC thm;

fun OE_SUBST_TAC thmlist =
    OE_LHS_SUBST_TAC thmlist
 >> OE_RHS_SUBST_TAC thmlist;

end (* struct *)

(* last updated: Jun 18, 2017 *)
