(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure ObsCongrConv :> ObsCongrConv =
struct

open HolKernel Parse boolLib bossLib;

open IndDefRules;
open CCSLib CCSTheory CCSSyntax;
open StrongEQTheory StrongEQLib StrongLawsTheory StrongLawsConv;
open WeakEQTheory WeakEQLib WeakLawsTheory WeakLawsConv;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;

infix 0 OC_THENC OC_ORELSEC;

(******************************************************************************)
(*                                                                            *)
(*          Basic conversions and tactics for applying the laws for           *)
(*                observation congruence                                      *)
(*                                                                            *)
(******************************************************************************)

(* Define the function OC_SUB_CONV. *)
fun OC_SUB_CONV (c: conv) tm =
  if is_prefix tm then
      let val (u, P) = args_prefix tm;
          val thm = c P
      in
          ISPEC u (MATCH_MP OBS_CONGR_SUBST_PREFIX thm)
      end
  else if is_sum tm then
      let val (t1, t2) = args_sum tm;
          val thm1 = c t1
          and thm2 = c t2
      in
          MATCH_MP OBS_CONGR_PRESD_BY_SUM (CONJ thm1 thm2)
      end
  else if is_par tm then
      let val (t1, t2) = args_par tm;
          val thm1 = c t1
          and thm2 = c t2
      in
          MATCH_MP OBS_CONGR_PRESD_BY_PAR (CONJ thm1 thm2)
      end
  else if is_restr tm then
      let val (P, L) = args_restr tm;
          val thm = c P
      in
          ISPEC L (MATCH_MP OBS_CONGR_SUBST_RESTR thm)
      end
  else if is_relab tm then
      let val (P, rf) = args_relab tm;
          val thm = c P
      in
          ISPEC rf (MATCH_MP OBS_CONGR_SUBST_RELAB thm)
      end
  else
      OC_ALL_CONV tm;

(* Define the function OC_DEPTH_CONV. *)
fun OC_DEPTH_CONV (c: conv) t =
   (OC_SUB_CONV (OC_DEPTH_CONV c) OC_THENC (OC_REPEATC c)) t;

(* Define the function OC_TOP_DEPTH_CONV. *)
fun OC_TOP_DEPTH_CONV (c: conv) t =
  ((OC_REPEATC c) OC_THENC
   (OC_SUB_CONV (OC_TOP_DEPTH_CONV c)) OC_THENC
   ((c OC_THENC (OC_TOP_DEPTH_CONV c)) OC_ORELSEC OC_ALL_CONV))
      t;

(* Define the function OC_SUBST for substitution in OBS_CONGR terms. *)
fun OC_SUBST thm tm = let
    val (ti, ti') = args_thm thm
in
    if tm ~~ ti then thm
    else if is_prefix tm then
        let val (u, t) = args_prefix tm;
            val thm1 = OC_SUBST thm t
        in
            ISPEC u (MATCH_MP OBS_CONGR_SUBST_PREFIX thm1)
        end
    else if is_sum tm then
        let val (t1, t2) = args_sum tm;
            val thm1 = OC_SUBST thm t1;
            val thm2 = OC_SUBST thm t2
        in
            MATCH_MP OBS_CONGR_PRESD_BY_SUM (CONJ thm1 thm2)
        end
    else if is_par tm then
        let val (t1, t2) = args_par tm;
            val thm1 = OC_SUBST thm t1
            and thm2 = OC_SUBST thm t2
        in
            MATCH_MP OBS_CONGR_PRESD_BY_PAR (CONJ thm1 thm2)
        end
    else if is_restr tm then
        let val (t, L) = args_restr tm;
            val thm1 = OC_SUBST thm t
        in
            ISPEC L (MATCH_MP OBS_CONGR_SUBST_RESTR thm1)
        end
    else if is_relab tm then
        let val (t, rf) = args_relab tm;
            val thm1 = OC_SUBST thm t
        in
            ISPEC rf (MATCH_MP OBS_CONGR_SUBST_RELAB thm1)
        end
    else
        OC_ALL_CONV tm
end;

(* Define the tactic OC_LHS_SUBST1_TAC: thm_tactic which substitutes a theorem
   in the left-hand side of an observation congruence. *)
fun OC_LHS_SUBST1_TAC thm :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if opt ~~ ``OBS_CONGR`` then
          let val thm' = OC_SUBST thm t1;
              val (t1', t') = args_thm thm' (* t1' = t1 *)
          in
              if (t' ~~ t2) then
                  ([], fn _ => OC_TRANS thm' (ISPEC t' OBS_CONGR_REFL))
              else
                  ([(asl, ``OBS_CONGR ^t' ^t2``)], fn [thm''] => OC_TRANS thm' thm'')
          end
      else
          failwith "the goal is not an OBS_CONGR relation"
  end;

(* The tactic OC_LHS_SUBST_TAC substitutes a list of theorems in the left-hand
   side of an observation congruence. *)
fun OC_LHS_SUBST_TAC thmlist =
    EVERY (map OC_LHS_SUBST1_TAC thmlist);

(* The tactic OC_RHS_SUBST1_TAC substitutes a theorem in the right-hand side
   of an observation congruence. *)
fun OC_RHS_SUBST1_TAC thm =
    REPEAT GEN_TAC
 >> RULE_TAC OBS_CONGR_SYM
 >> OC_LHS_SUBST1_TAC thm
 >> RULE_TAC OBS_CONGR_SYM;

(* The tactic OC_RHS_SUBST_TAC substitutes a list of theorems in the right-hand
   side of an observation congruence. *)
fun OC_RHS_SUBST_TAC thmlist =
    REPEAT GEN_TAC
 >> RULE_TAC OBS_CONGR_SYM
 >> OC_LHS_SUBST_TAC thmlist
 >> RULE_TAC OBS_CONGR_SYM;

(* The tactic OC_SUBST1_TAC (OC_SUBST_TAC) substitutes a (list of) theorem(s)
   in both sides of an observation congruence. *)
fun OC_SUBST1_TAC thm =
    OC_LHS_SUBST1_TAC thm
 >> OC_RHS_SUBST1_TAC thm;

fun OC_SUBST_TAC thmlist =
    OC_LHS_SUBST_TAC thmlist
 >> OC_RHS_SUBST_TAC thmlist;

(******************************************************************************)
(*                                                                            *)
(*     Conversions for applying the tau-laws of observation congruence        *)
(*                                                                            *)
(******************************************************************************)

(* Conversion for the application of the tau-law TAU1:
   |- !u E. OBS_CONGR (prefix u (prefix tau E)) (prefix u E) *)
fun TAU1_CONV tm =
  if is_prefix tm then
      let val (u, t) = args_prefix tm
      in
          if is_prefix t then
              let val (u', t') = args_prefix t
              in
                  if is_tau u' then
                      ISPECL [u, t'] TAU1
                  else
                      failwith "TAU1_CONV"
              end
          else
              failwith "TAU1_CONV"
      end
  else
      failwith "TAU1_CONV";

(* Conversion for the application of the tau-law TAU2:
   |- !E. OBS_CONGR (sum E (prefix tau E)) (prefix tau E)
 *)
fun TAU2_CONV tm =
  if is_sum tm then
    let
      val (tm1, tm2) = args_sum tm
    in
      if is_prefix tm2 then
        let val (u, t) = args_prefix tm2
        in
          if is_tau u andalso tm1 ~~ t then ISPEC t TAU2
          else failwith "TAU2_CONV"
        end
      else failwith "TAU2_CONV"
    end
  else failwith "TAU2_CONV";

(* Conversion for the application of the tau-law TAU3:
   |- !u E E'.
       OBS_CONGR (sum (prefix u (sum E (prefix tau E'))) (prefix u E'))
                 (prefix u (sum E (prefix tau E')))
 *)
fun TAU3_CONV tm =
  if is_sum tm then
      let val (tm1, tm2) = args_sum tm
      in
          if is_prefix tm2 then
              let val (u, t2) = args_prefix tm2
              in
                  if is_prefix tm1 then
                      let val (u', tm3) = args_prefix tm1
                      in
                          if u ~~ u' andalso is_sum tm3 then
                              let val (t1, tm4) = args_sum tm3
                              in
                                  if is_prefix tm4 then
                                      let val (u'', tm5) = args_prefix tm4
                                      in
                                          if is_tau u'' andalso tm5 ~~ t2 then
                                              ISPECL [u, t1, t2] TAU3
                                          else failwith "TAU3_CONV"
                                      end
                                  else failwith "TAU3_CONV"
                              end
                          else failwith "TAU3_CONV"
                      end
                  else failwith "TAU3_CONV"
              end
          else failwith "TAU3_CONV"
      end
  else failwith "TAU3_CONV";

(******************************************************************************)
(*                                                                            *)
(*            Conversions and tactics for applying the laws for               *)
(*                 observation congruence                                     *)
(*                                                                            *)
(******************************************************************************)

(* Define the conversions for the application of the laws for OBS_CONGR
   (through the conversions for strong equivalence). *)
fun STRONG_TO_OBS_CONGR_CONV (c: conv) tm =
    MATCH_MP STRONG_IMP_OBS_CONGR (c tm);

val [OC_SUM_IDEMP_CONV, OC_SUM_NIL_CONV,
     OC_RELAB_ELIM_CONV, OC_RESTR_ELIM_CONV,
     OC_PAR_ELIM_CONV, OC_EXP_THM_CONV, OC_REC_UNF_CONV] =
    map STRONG_TO_OBS_CONGR_CONV
        [STRONG_SUM_IDEMP_CONV, STRONG_SUM_NIL_CONV, STRONG_RELAB_ELIM_CONV,
         STRONG_RESTR_ELIM_CONV, STRONG_PAR_ELIM_CONV, STRONG_EXP_THM_CONV,
         STRONG_REC_UNF_CONV];

(* Define the tactics for the application of the laws for OBS_CONGR *)
val [OC_SUM_IDEMP_TAC, OC_SUM_NIL_TAC, OC_RELAB_ELIM_TAC, OC_RESTR_ELIM_TAC,
     OC_PAR_ELIM_TAC, OC_REC_UNF_TAC, TAU1_TAC, TAU2_TAC, TAU3_TAC] =
    map (OC_LHS_CONV_TAC o OC_DEPTH_CONV)
        [OC_SUM_IDEMP_CONV, OC_SUM_NIL_CONV,
         OC_RELAB_ELIM_CONV, OC_RESTR_ELIM_CONV,
         OC_PAR_ELIM_CONV, OC_REC_UNF_CONV,
         TAU1_CONV, TAU2_CONV, TAU3_CONV];

val OC_RHS_RELAB_ELIM_TAC =
    (OC_RHS_CONV_TAC o OC_DEPTH_CONV) OC_RELAB_ELIM_CONV;

(* TODO: idem for the other operators *)

(* Tactic for applying the expansion theorem (parallel and restriction operators). *)
val OC_EXP_THM_TAC = OC_LHS_CONV_TAC OC_EXP_THM_CONV;

end (* struct *)

(* last updated: Jun 24, 2017 *)
