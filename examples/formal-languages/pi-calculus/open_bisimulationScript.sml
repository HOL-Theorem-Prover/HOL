(* ========================================================================== *)
(* FILE          : open_bisimulationScript.sml                                *)
(* DESCRIPTION   : Open bisimulation for the pi-calculus                      *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory relationTheory hurdUtils;

open basic_swapTheory nomsetTheory NEWLib pi_agentTheory;

val _ = new_theory "open_bisimulation";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* NOTE: The type 'a is reserved for TRANS_bvc_gen_ind *)
Type transition[pp] = “:pi -> residual -> bool”
Type gen_transition = “:'a -> transition”

Definition TRANS_TAU_def :
    TRANS_TAU (R :'a gen_transition) z P <=> R z (Tau P) (TauR P)
End

Definition TRANS_INPUT_def :
    TRANS_INPUT R z a x P <=> x <> a ==> R z (Input a x P) (InputS a x P)
End

Definition TRANS_OUTPUT_def :
    TRANS_OUTPUT (R :'a gen_transition) z a b P <=>
        R z (Output a b P) (FreeOutput a b P)
End

Definition TRANS_MATCH_def :
    TRANS_MATCH (R :'a gen_transition) z P Rs b <=> R z P Rs ==> R z (Match b b P) Rs
End

Definition TRANS_MISMATCH_def :
    TRANS_MISMATCH (R :'a gen_transition) z P Rs a b <=>
        R z P Rs /\ a <> b ==> R z (Mismatch a b P) Rs
End

Definition TRANS_OPEN_def :
    TRANS_OPEN R z P P' a b <=>
               R z P (FreeOutput a b P') /\ a <> b ==>
               R z (Res b P) (BoundOutput a b P')
End

Definition TRANS_SUM1_def :
    TRANS_SUM1 (R :'a gen_transition) z P Q Rs <=> R z P Rs ==> R z (Sum P Q) Rs
End

Definition TRANS_SUM2_def :
    TRANS_SUM2 (R :'a gen_transition) z P Q Rs <=> R z Q Rs ==> R z (Sum P Q) Rs
End

Definition TRANS_PAR1_I_def :
    TRANS_PAR1_I R z P P' Q a x <=>
       R z P (InputS a x P') /\ x # P /\ x # Q /\ x <> a ==>
       R z (Par P Q) (InputS a x (Par P' Q))
End

Definition TRANS_PAR1_BO_def :
    TRANS_PAR1_BO R z P P' Q a x <=>
       R z P (BoundOutput a x P') /\ x # P /\ x # Q /\ x <> a ==>
       R z (Par P Q) (BoundOutput a x (Par P' Q))
End

Definition TRANS_PAR1_FO_def :
    TRANS_PAR1_FO R z P P' Q a b <=>
       R z P (FreeOutput a b P') ==>
       R z (Par P Q) (FreeOutput a b (Par P' Q))
End

Definition TRANS_PAR1_T_def :
    TRANS_PAR1_T R z P P' Q <=> R z P (TauR P') ==> R z (Par P Q) (TauR (Par P' Q))
End

Definition TRANS_PAR2_I_def :
    TRANS_PAR2_I R z P Q Q' a x <=>
       R z Q (InputS a x Q') /\ x # Q /\ x # P /\ x <> a ==>
       R z (Par P Q) (InputS a x (Par P Q'))
End

Definition TRANS_PAR2_BO_def :
    TRANS_PAR2_BO R z P Q Q' a x <=>
       R z Q (BoundOutput a x Q') /\ x # Q /\ x # P /\ x <> a ==>
       R z (Par P Q) (BoundOutput a x (Par P Q'))
End

Definition TRANS_PAR2_FO_def :
    TRANS_PAR2_FO R z P Q Q' a b <=>
       R z Q (FreeOutput a b Q') ==>
       R z (Par P Q) (FreeOutput a b (Par P Q'))
End

Definition TRANS_PAR2_T_def :
    TRANS_PAR2_T R z P Q Q' <=> R z Q (TauR Q') ==> R z (Par P Q) (TauR (Par P Q'))
End

Definition TRANS_COMM1_def :
    TRANS_COMM1 R z P P' Q Q' a b x <=>
       R z P (InputS a x P') /\ R z Q (FreeOutput a b Q') /\
       x # P /\ x # Q /\ x <> a /\ x <> b /\ x # Q' ==>
       R z (Par P Q) (TauR (Par ([b/x] P') Q'))
End

Definition TRANS_COMM2_def :
    TRANS_COMM2 R z P P' Q Q' a b x <=>
       R z P (FreeOutput a b P') /\ R z Q (InputS a x Q') /\
       x # Q /\ x # P /\ x <> a /\ x <> b /\ x # P' ==>
       R z (Par P Q) (TauR (Par P' ([b/x] Q')))
End

Definition TRANS_CLOSE1_def :
    TRANS_CLOSE1 R z P P' Q Q' a x y <=>
       R z P (InputS a x P') /\ R z Q (BoundOutput a y Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # Q' /\ y <> a /\ y # P' /\ x <> y ==>
       R z (Par P Q) (TauR (Res y (Par ([y/x] P') Q')))
End

Definition TRANS_CLOSE2_def :
    TRANS_CLOSE2 R z P P' Q Q' a x y <=>
       R z P (BoundOutput a y P') /\
       R z Q (InputS a x Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # P' /\ y <> a /\ y # Q' /\ x <> y ==>
       R z (Par P Q) (TauR (Res y (Par P' ([y/x] Q'))))
End

Definition TRANS_RES_I_def :
    TRANS_RES_I R z P P' a x y <=>
       R z P (InputS a x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       R z (Res y P) (InputS a x (Res y P'))
End

Definition TRANS_RES_BO_def :
    TRANS_RES_BO R z P P' a x y <=>
       R z P (BoundOutput a x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       R z (Res y P) (BoundOutput a x (Res y P'))
End

Definition TRANS_RES_FO_def :
    TRANS_RES_FO R z P P' a b y <=>
       R z P (FreeOutput a b P') /\
       y <> a /\ y <> b ==>
       R z (Res y P) (FreeOutput a b (Res y P'))
End

Definition TRANS_RES_T_def :
    TRANS_RES_T R z P P' y <=> R z P (TauR P') ==> R z (Res y P) (TauR (Res y P'))
End

(* A list of 24 definitions *)
val TRANS_gen_defs =
   [TRANS_TAU_def, TRANS_INPUT_def, TRANS_OUTPUT_def, TRANS_MATCH_def,
    TRANS_MISMATCH_def, TRANS_OPEN_def, TRANS_SUM1_def, TRANS_SUM2_def,
    TRANS_PAR1_I_def, TRANS_PAR1_BO_def, TRANS_PAR1_FO_def, TRANS_PAR1_T_def,
    TRANS_PAR2_I_def, TRANS_PAR2_BO_def, TRANS_PAR2_FO_def, TRANS_PAR2_T_def,
    TRANS_COMM1_def, TRANS_COMM2_def, TRANS_CLOSE1_def, TRANS_CLOSE2_def,
    TRANS_RES_I_def, TRANS_RES_BO_def, TRANS_RES_FO_def, TRANS_RES_T_def];

val R_tm = “R :pi -> residual -> bool”;
fun mk_spec_def d =
    d |> Q.SPECL [‘K ^R_tm’, ‘ARB’]
      |> SIMP_RULE std_ss [SimpRHS]
      |> GEN R_tm

val TRANS_defs = map mk_spec_def TRANS_gen_defs

(* and their GSYM versions *)
val GSYM_TRANS_defs = map GSYM TRANS_defs;

(* This function generates Inductive-compatible rule terms
   val d = TRANS_TAU_def *)
val trans_tm = “TRANS :pi -> residual -> bool”;

fun mk_ind_rule d = let
    val th = d |> Q.SPECL [‘K ^trans_tm’, ‘ARB’]
               |> SIMP_RULE std_ss [SimpRHS];
    val (vars,eq_tm) = strip_forall (concl th);
    val body_tm = snd (dest_eq eq_tm)
in
    list_mk_forall (vars,body_tm)
end

val TAU_rule      = mk_ind_rule TRANS_TAU_def
val INPUT_rule    = mk_ind_rule TRANS_INPUT_def
val OUTPUT_rule   = mk_ind_rule TRANS_OUTPUT_def
val MATCH_rule    = mk_ind_rule TRANS_MATCH_def
val MISMATCH_rule = mk_ind_rule TRANS_MISMATCH_def
val OPEN_rule     = mk_ind_rule TRANS_OPEN_def
val SUM1_rule     = mk_ind_rule TRANS_SUM1_def
val SUM2_rule     = mk_ind_rule TRANS_SUM2_def
val PAR1_I_rule   = mk_ind_rule TRANS_PAR1_I_def
val PAR1_BO_rule  = mk_ind_rule TRANS_PAR1_BO_def
val PAR1_FO_rule  = mk_ind_rule TRANS_PAR1_FO_def
val PAR1_T_rule   = mk_ind_rule TRANS_PAR1_T_def
val PAR2_I_rule   = mk_ind_rule TRANS_PAR2_I_def
val PAR2_BO_rule  = mk_ind_rule TRANS_PAR2_BO_def
val PAR2_FO_rule  = mk_ind_rule TRANS_PAR2_FO_def
val PAR2_T_rule   = mk_ind_rule TRANS_PAR2_T_def
val RES_I_rule    = mk_ind_rule TRANS_RES_I_def
val RES_BO_rule   = mk_ind_rule TRANS_RES_BO_def
val RES_FO_rule   = mk_ind_rule TRANS_RES_FO_def
val RES_T_rule    = mk_ind_rule TRANS_RES_T_def
val COMM1_rule    = mk_ind_rule TRANS_COMM1_def
val COMM2_rule    = mk_ind_rule TRANS_COMM2_def
val CLOSE1_rule   = mk_ind_rule TRANS_CLOSE1_def
val CLOSE2_rule   = mk_ind_rule TRANS_CLOSE2_def

Inductive TRANS :
[TAU:]      ^TAU_rule
[INPUT:]    ^INPUT_rule
[OUTPUT:]   ^OUTPUT_rule
[MATCH:]    ^MATCH_rule
[MISMATCH:] ^MISMATCH_rule
[OPEN:]     ^OPEN_rule
[SUM1:]     ^SUM1_rule
[SUM2:]     ^SUM2_rule
[PAR1_I:]   ^PAR1_I_rule
[PAR1_BO:]  ^PAR1_BO_rule
[PAR1_FO:]  ^PAR1_FO_rule
[PAR1_T:]   ^PAR1_T_rule
[PAR2_I:]   ^PAR2_I_rule
[PAR2_BO:]  ^PAR2_BO_rule
[PAR2_FO:]  ^PAR2_FO_rule
[PAR2_T:]   ^PAR2_T_rule
[RES_I:]    ^RES_I_rule
[RES_BO:]   ^RES_BO_rule
[RES_FO:]   ^RES_FO_rule
[RES_T:]    ^RES_T_rule
[COMM1:]    ^COMM1_rule
[COMM2:]    ^COMM2_rule
[CLOSE1:]   ^CLOSE1_rule
[CLOSE2:]   ^CLOSE2_rule
End

(* NOTE: No way to simplify TRANS_cases in the same manner *)
Theorem TRANS_rules[allow_rebind] =
        TRANS_rules |> REWRITE_RULE GSYM_TRANS_defs

Theorem TRANS_ind[allow_rebind] =
        TRANS_ind |> REWRITE_RULE GSYM_TRANS_defs
                  |> Q.SPEC ‘R’ |> Q.GEN ‘R’

Overload TRANS_TAU'      = “\R. TRANS_TAU      (K R) ARB”
Overload TRANS_INPUT'    = “\R. TRANS_INPUT    (K R) ARB”
Overload TRANS_OUTPUT'   = “\R. TRANS_OUTPUT   (K R) ARB”
Overload TRANS_MATCH'    = “\R. TRANS_MATCH    (K R) ARB”
Overload TRANS_MISMATCH' = “\R. TRANS_MISMATCH (K R) ARB”
Overload TRANS_OPEN'     = “\R. TRANS_OPEN     (K R) ARB”
Overload TRANS_SUM1'     = “\R. TRANS_SUM1     (K R) ARB”
Overload TRANS_SUM2'     = “\R. TRANS_SUM2     (K R) ARB”
Overload TRANS_PAR1_I'   = “\R. TRANS_PAR1_I   (K R) ARB”
Overload TRANS_PAR1_BO'  = “\R. TRANS_PAR1_BO  (K R) ARB”
Overload TRANS_PAR1_FO'  = “\R. TRANS_PAR1_FO  (K R) ARB”
Overload TRANS_PAR1_T'   = “\R. TRANS_PAR1_T   (K R) ARB”
Overload TRANS_PAR2_I'   = “\R. TRANS_PAR2_I   (K R) ARB”
Overload TRANS_PAR2_BO'  = “\R. TRANS_PAR2_BO  (K R) ARB”
Overload TRANS_PAR2_FO'  = “\R. TRANS_PAR2_FO  (K R) ARB”
Overload TRANS_PAR2_T'   = “\R. TRANS_PAR2_T   (K R) ARB”
Overload TRANS_RES_I'    = “\R. TRANS_RES_I    (K R) ARB”
Overload TRANS_RES_BO'   = “\R. TRANS_RES_BO   (K R) ARB”
Overload TRANS_RES_FO'   = “\R. TRANS_RES_FO   (K R) ARB”
Overload TRANS_RES_T'    = “\R. TRANS_RES_T    (K R) ARB”
Overload TRANS_COMM1'    = “\R. TRANS_COMM1    (K R) ARB”
Overload TRANS_COMM2'    = “\R. TRANS_COMM2    (K R) ARB”
Overload TRANS_CLOSE1'   = “\R. TRANS_CLOSE1   (K R) ARB”
Overload TRANS_CLOSE2'   = “\R. TRANS_CLOSE2   (K R) ARB”

(* NOTE: The following 3 lemmas reshape the statements of strong induction to
   make the abbreviation TRANS-symbols work.
 *)
val lemma1 = Q.prove (
   ‘!P Q A B C D E.
       (TRANS P A /\ B /\ TRANS Q C /\ D ==> E) <=>
       (TRANS P A /\ TRANS Q C ==> B /\ D ==> E)’,
    METIS_TAC []);

val lemma2 = Q.prove (
   ‘!P A B C. (TRANS P A /\ B ==> C) <=> (TRANS P A ==> B ==> C)’,
    METIS_TAC []);

val lemma3 = Q.prove (
   ‘!P Q A B C.
       (TRANS P A ==> TRANS Q B ==> C) <=>
       (TRANS P A /\ TRANS Q B ==> C)’,
    METIS_TAC []);

Theorem TRANS_strongind[allow_rebind] =
        TRANS_strongind |> SIMP_RULE bool_ss [lemma1]
                        |> SIMP_RULE bool_ss [lemma2]
                        |> SIMP_RULE bool_ss [lemma3]
                        |> REWRITE_RULE GSYM_TRANS_defs

Theorem TRANS_tpm :
    !P Q. TRANS P Q ==> !pi. TRANS (tpm pi P) (rpm pi Q)
Proof
    HO_MATCH_MP_TAC TRANS_ind
 >> rpt STRIP_TAC (* 24 subgoals *)
 >- rw [TRANS_TAU_def, TAU]
 >- rw [TRANS_INPUT_def, INPUT]
 >- rw [TRANS_OUTPUT_def, OUTPUT]
 >- rw [TRANS_MATCH_def, MATCH]
 >- rw [TRANS_MISMATCH_def, MISMATCH]
 >- rw [TRANS_OPEN_def, OPEN]
 >- rw [TRANS_SUM1_def, SUM1]
 >- rw [TRANS_SUM2_def, SUM2]
 >- rw [TRANS_PAR1_I_def, PAR1_I]
 >- rw [TRANS_PAR1_BO_def, PAR1_BO]
 >- rw [TRANS_PAR1_FO_def, PAR1_FO]
 >- rw [TRANS_PAR1_T_def, PAR1_T]
 >- rw [TRANS_PAR2_I_def, PAR2_I]
 >- rw [TRANS_PAR2_BO_def, PAR2_BO]
 >- rw [TRANS_PAR2_FO_def, PAR2_FO]
 >- rw [TRANS_PAR2_T_def, PAR2_T]
 >- rw [TRANS_RES_I_def, RES_I]
 >- rw [TRANS_RES_BO_def, RES_BO]
 >- rw [TRANS_RES_FO_def, RES_FO]
 >- rw [TRANS_RES_T_def, RES_T]
 (* 4 subgoals left *)
 >- (rw [TRANS_COMM1_def, tpm_subst] \\
     MATCH_MP_TAC COMM1 \\
     Q.EXISTS_TAC ‘lswapstr pi a’ >> simp [])
 (* 3 subgoals left *)
 >- (rw [TRANS_COMM2_def, tpm_subst] \\
     MATCH_MP_TAC COMM2 \\
     Q.EXISTS_TAC ‘lswapstr pi a’ >> simp [])
 (* 2 subgoals left *)
 >- (rw [TRANS_CLOSE1_def, tpm_subst] \\
     MATCH_MP_TAC CLOSE1 \\
     Q.EXISTS_TAC ‘lswapstr pi a’ >> simp [])
 (* 1 subgoal left *)
 >> (rw [TRANS_CLOSE2_def, tpm_subst] \\
     MATCH_MP_TAC CLOSE2 \\
     Q.EXISTS_TAC ‘lswapstr pi a’ >> simp [])
QED

Theorem FV_InputS_lemma :
    !P P' x z. TRANS P (InputS x z P') /\ x <> z /\ z # P ==>
               !y. y # P /\ y <> z ==> y # P'
Proof
    Induct_on ‘TRANS’ using TRANS_ind >> rw [] (* 24 subgoals *)
 >- rw [TRANS_TAU_def]
 >- (rw [TRANS_INPUT_def, InputS_eq_thm] (* 3 subgoals here *) \\
     rw [] (* only one goal is left *) \\
     Cases_on ‘x = y’ >> simp [swapstr_def])
 >- rw [TRANS_OUTPUT_def]
 >- (rw [TRANS_MATCH_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- (rw [TRANS_MISMATCH_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- rw [TRANS_OPEN_def]
 >- (rw [TRANS_SUM1_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- (rw [TRANS_SUM2_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- (rw [TRANS_PAR1_I_def] \\
     Q.PAT_X_ASSUM ‘InputS _ _ _ = InputS _ _ _’ MP_TAC \\
     rw [InputS_eq_thm] >> simp []
     >- (FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw []) \\
     Cases_on ‘x = y’ >> simp [] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘x’] >> rw [])
 >- rw [TRANS_PAR1_BO_def]
 >- rw [TRANS_PAR1_FO_def]
 >- rw [TRANS_PAR1_T_def]
 (* 12 subgoals left *)
 >- (rw [TRANS_PAR2_I_def] \\
     Q.PAT_X_ASSUM ‘InputS _ _ _ = InputS _ _ _’ MP_TAC \\
     rw [InputS_eq_thm] >> simp []
     >- (FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw []) \\
     Cases_on ‘x = y’ >> simp [] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘x’] >> rw [])
 >- rw [TRANS_PAR2_BO_def]
 >- rw [TRANS_PAR2_FO_def]
 >- rw [TRANS_PAR2_T_def]
 >- (rw [TRANS_RES_I_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.PAT_X_ASSUM ‘InputS _ _ _ = InputS _ _ _’ MP_TAC \\
       rw [InputS_eq_thm] >> simp [] >| (* 3 subgoals *)
       [ (* goal 1.1 (of 3) *)
         DISJ1_TAC \\
         FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw [],
         (* goal 1.2 (of 3) *)
         DISJ1_TAC \\
         Cases_on ‘x = y'’ >> simp [] \\
         FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw [],
         (* goal 1.3 (of 3) *)
         Cases_on ‘x = y'’ >> simp [] \\
         FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw [] ],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM ‘InputS _ _ _ = InputS _ _ _’ MP_TAC \\
       rw [InputS_eq_thm] >> simp [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM ‘InputS _ _ _ = InputS _ _ _’ MP_TAC \\
       rw [InputS_eq_thm] >> simp [] \\
       Cases_on ‘x = y'’ >> simp [] \\
       FIRST_X_ASSUM irule >> art [] \\
       qexistsl_tac [‘a’, ‘x’] >> rw [] ])
 (* 7 subgoals left *)
 >- rw [TRANS_RES_BO_def]
 >- rw [TRANS_RES_FO_def]
 >- rw [TRANS_RES_T_def]
 >- rw [TRANS_COMM1_def]
 >- rw [TRANS_COMM2_def]
 >- rw [TRANS_CLOSE1_def]
 >> rw [TRANS_CLOSE2_def]
QED

Theorem FV_InputS :
    !P P' x z. TRANS P (InputS x z P') /\ x <> z /\ z # P ==>
               FV P' SUBSET z INSERT FV P
Proof
    rw [SUBSET_DEF, IN_INSERT]
 >> METIS_TAC [FV_InputS_lemma]
QED

Theorem FV_FreeOutput_lemma :
    !P P' a b. TRANS P (FreeOutput a b P') ==> !y. y # P ==> y # P'
Proof
    Induct_on ‘TRANS’ using TRANS_ind >> rw [] (* 24 subgoals *)
 >- rw [TRANS_TAU_def]
 >- rw [TRANS_INPUT_def]
 >- rw [TRANS_OUTPUT_def]
 >- (rw [TRANS_MATCH_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘b'’] >> rw [])
 >- (rw [TRANS_MISMATCH_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a'’, ‘b'’] >> rw [])
 >- rw [TRANS_OPEN_def]
 >- (rw [TRANS_SUM1_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘b’] >> rw [])
 >- (rw [TRANS_SUM2_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘b’] >> rw [])
 >- rw [TRANS_PAR1_I_def]
 >- rw [TRANS_PAR1_BO_def]
 >- rw [TRANS_PAR1_FO_def]
 >- rw [TRANS_PAR1_T_def]
 >- rw [TRANS_PAR2_I_def]
 >- rw [TRANS_PAR2_BO_def]
 >- rw [TRANS_PAR2_FO_def]
 >- rw [TRANS_PAR2_T_def]
 >- rw [TRANS_RES_I_def]
 >- rw [TRANS_RES_BO_def]
 >- (rw [TRANS_RES_FO_def] \\
     DISJ1_TAC \\
     FIRST_X_ASSUM irule >> art [])
 >- rw [TRANS_RES_T_def]
 >- rw [TRANS_COMM1_def]
 >- rw [TRANS_COMM2_def]
 >- rw [TRANS_CLOSE1_def]
 >> rw [TRANS_CLOSE2_def]
QED

Theorem FV_FreeOutput :
    !P P' a b. TRANS P (FreeOutput a b P') ==> FV P' SUBSET FV P
Proof
    rw [SUBSET_DEF]
 >> METIS_TAC [FV_FreeOutput_lemma]
QED

Theorem FV_BoundOutput_lemma :
    !P P' x z. TRANS P (BoundOutput x z P') /\ x <> z /\ z # P ==>
               !y. y # P /\ y <> z ==> y # P'
Proof
    Induct_on ‘TRANS’ using TRANS_strongind >> rw [] (* 24 subgoals *)
 >- rw [TRANS_TAU_def]
 >- rw [TRANS_INPUT_def]
 >- rw [TRANS_OUTPUT_def]
 >- (rw [TRANS_MATCH_def] \\
     FIRST_X_ASSUM irule >> rw [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- (rw [TRANS_MISMATCH_def] \\
     FIRST_X_ASSUM irule >> rw [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- (rw [TRANS_OPEN_def, BoundOutput_eq_thm] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       irule FV_FreeOutput_lemma \\
       qexistsl_tac [‘P’, ‘a’, ‘b’] >> art [],
       (* goal 2 (of 4) *)
       irule FV_FreeOutput_lemma \\
       qexistsl_tac [‘P’, ‘a’, ‘b’] >> art [],
       (* goal 3 (of 4) *)
       rw [FV_tpm] \\
       Cases_on ‘b = y’ >> simp [] \\
       irule FV_FreeOutput_lemma \\
       qexistsl_tac [‘P’, ‘a’, ‘b’] >> art [],
       (* goal 4 (of 4) *)
       rw [FV_tpm] ])
 (* 18 subgoals left *)
 >- (rw [TRANS_SUM1_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- (rw [TRANS_SUM2_def] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘x’, ‘z’] >> rw [])
 >- rw [TRANS_PAR1_I_def]
 >- (rw [TRANS_PAR1_BO_def] \\
     Q.PAT_X_ASSUM ‘BoundOutput _ _ _ = BoundOutput _ _ _’ MP_TAC \\
     rw [BoundOutput_eq_thm] >> simp []
     >- (FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw []) \\
     Cases_on ‘x = y’ >> simp [] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘x’] >> rw [])
 >- rw [TRANS_PAR1_FO_def]
 >- rw [TRANS_PAR1_T_def]
 (* 12 subgoals left *)
 >- rw [TRANS_PAR2_I_def]
 >- (rw [TRANS_PAR2_BO_def] \\
     Q.PAT_X_ASSUM ‘BoundOutput _ _ _ = BoundOutput _ _ _’ MP_TAC \\
     rw [BoundOutput_eq_thm] >> simp []
     >- (FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw []) \\
     Cases_on ‘x = y’ >> simp [] \\
     FIRST_X_ASSUM irule >> art [] \\
     qexistsl_tac [‘a’, ‘x’] >> rw [])
 >- rw [TRANS_PAR2_FO_def]
 >- rw [TRANS_PAR2_T_def]
 >- rw [TRANS_RES_I_def]
 >- (rw [TRANS_RES_BO_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.PAT_X_ASSUM ‘BoundOutput _ _ _ = BoundOutput _ _ _’ MP_TAC \\
       rw [BoundOutput_eq_thm] >> simp [] >| (* 3 subgoals *)
       [ (* goal 1.1 (of 3) *)
         DISJ1_TAC \\
         FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw [],
         (* goal 1.2 (of 3) *)
         DISJ1_TAC \\
         Cases_on ‘x = y'’ >> simp [] \\
         FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw [],
         (* goal 1.3 (of 3) *)
         Cases_on ‘x = y'’ >> simp [] \\
         FIRST_X_ASSUM irule >> art [] \\
         qexistsl_tac [‘a’, ‘x’] >> rw [] ],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM ‘BoundOutput _ _ _ = BoundOutput _ _ _’ MP_TAC \\
       rw [BoundOutput_eq_thm] >> simp [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM ‘BoundOutput _ _ _ = BoundOutput _ _ _’ MP_TAC \\
       rw [BoundOutput_eq_thm] >> simp [] \\
       Cases_on ‘x = y'’ >> simp [] \\
       FIRST_X_ASSUM irule >> rw [] \\
       qexistsl_tac [‘a’, ‘x’] >> rw [] ])
 (* 6 subgoals left *)
 >- rw [TRANS_RES_FO_def]
 >- rw [TRANS_RES_T_def]
 >- rw [TRANS_COMM1_def]
 >- rw [TRANS_COMM2_def]
 >- rw [TRANS_CLOSE1_def]
 >> rw [TRANS_CLOSE2_def]
QED

Theorem FV_BoundOutput :
    !P P' x z. TRANS P (BoundOutput x z P') /\ x <> z /\ z # P ==>
               FV P' SUBSET z INSERT FV P
Proof
    rw [SUBSET_DEF, IN_INSERT]
 >> METIS_TAC [FV_BoundOutput_lemma]
QED

Definition open_simulation_def :
    open_simulation (R :pi -> pi -> bool) <=>
    !P Q. R P Q ==>
    (* 1 *)
      (!pi. R (tpm pi P) (tpm pi Q)) /\
    (* 3a *)
      (!P'. TRANS P (TauR P') ==> ?Q'. TRANS Q (TauR Q') /\ R P' Q') /\
    (* 3b *)
      (!x z P'. TRANS P (InputS x z P') /\
                z # P /\ z # Q /\ x <> z ==>
               ?Q'. TRANS Q (InputS x z Q') /\ R P' Q') /\
    (* 3c *)
      (!a b P'. TRANS P (FreeOutput a b P') ==>
               ?Q'. TRANS Q (FreeOutput a b Q') /\ R P' Q') /\
    (* 4 *)
      (!x z P'. TRANS P (BoundOutput x z P') /\
                z # P /\ z # Q /\ x <> z ==>
               ?Q'. TRANS Q (BoundOutput x z Q') /\ R P' Q')
End

Definition open_bisimulation_def :
    open_bisimulation (R :pi -> pi -> bool) <=>
    open_simulation R /\ open_simulation (\x y. R y x)
End

Definition open_bisimilar :
    open_bisimilar P Q <=> ?R. open_bisimulation R /\ R P Q
End

(* |- !P Q.
        open_bisimilar P Q <=>
        ?R. (open_simulation R /\ open_simulation (\x y. R y x)) /\ R P Q
 *)
Theorem open_bisimilar_def =
        open_bisimilar |> REWRITE_RULE [open_bisimulation_def]

Theorem open_simulation_id :
    open_simulation Id
Proof
    rw [open_simulation_def]
QED

Theorem open_bisimilar_reflexive :
    !P. open_bisimilar P P
Proof
    rw [open_bisimilar_def]
 >> Q.EXISTS_TAC ‘Id’
 >> ‘(\x y :pi. y = x) = Id’ by METIS_TAC []
 >> simp [open_simulation_id]
QED

Theorem open_simulation_union :
    !R1 R2. open_simulation R1 /\ open_simulation R2 ==>
            open_simulation (R1 RUNION R2)
Proof
    rw [open_simulation_def, RUNION] (* 5+5 subgoals *)
 (* goal 1 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R1 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [])
 (* goal 2 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R1 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!P'. TRANS P (TauR P') ==> _’ (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 3 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R1 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!x z P'. TRANS P (InputS x z P') /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘x’, ‘z’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 4 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R1 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!a b P'. TRANS P (FreeOutput a b P') ==> _’
       (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 5 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R1 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!x z P'. TRANS P (BoundOutput x z P') /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘x’, ‘z’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 6 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R2 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [])
 (* goal 7 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R2 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!P'. TRANS P (TauR P') ==> _’ (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 8 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R2 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!x z P'. TRANS P (InputS x z P') /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘x’, ‘z’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 9 (of 10) *)
 >- (Q.PAT_X_ASSUM ‘!P Q. R2 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!a b P'. TRANS P (FreeOutput a b P') ==> _’
       (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 10 (of 10) *)
 >> (Q.PAT_X_ASSUM ‘!P Q. R2 P Q ==> _’ (MP_TAC o Q.SPECL [‘P’, ‘Q’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!x z P'. TRANS P (BoundOutput x z P') /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘x’, ‘z’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
QED

Theorem open_bisimilar_symmetric :
    !P Q. open_bisimilar P Q ==> open_bisimilar Q P
Proof
    rw [open_bisimilar_def]
 >> qabbrev_tac ‘R' = \x y. R y x’
 >> Q.EXISTS_TAC ‘R RUNION R'’
 >> reverse CONJ_TAC >- simp [RUNION, Abbr ‘R'’]
 >> CONJ_TAC
 >- (MATCH_MP_TAC open_simulation_union >> art [])
 >> rw [RUNION, Abbr ‘R'’]
 >> ‘(\x y. R y x \/ R x y) = (\x y. R y x) RUNION R’
      by rw [FUN_EQ_THM, RUNION]
 >> POP_ORW
 >> MATCH_MP_TAC open_simulation_union >> art []
QED

Theorem open_bisimilar_transitive :
    !P1 P2 P3. open_bisimilar P1 P2 /\ open_bisimilar P2 P3 ==> open_bisimilar P1 P3
Proof
    rw [open_bisimilar_def]
 >> Q.EXISTS_TAC ‘R' O R’
 >> simp [O_DEF]
 >> reverse CONJ_TAC
 >- (Q.EXISTS_TAC ‘P2’ >> art [])
 >> Q.PAT_X_ASSUM ‘R  P1 P2’ K_TAC
 >> Q.PAT_X_ASSUM ‘R' P2 P3’ K_TAC
 >> rw [open_simulation_def, O_DEF] (* 5+5 subgoals *)
 >| [ (* goal 1 (of 10) *)
      Q.PAT_X_ASSUM ‘open_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘open_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.EXISTS_TAC ‘tpm pi y’ >> rw [],
      (* goal 2 (of 10) *)
      Q.PAT_X_ASSUM ‘open_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!P Q P'. R P Q ==> TRANS P (TauR P') ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘y’, ‘P'’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘open_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      rename1 ‘TRANS y (TauR y')’ \\
      Q.PAT_X_ASSUM ‘!P Q P'. R' P Q ==> TRANS P (TauR P') ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘Q’, ‘y'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [] \\
      Q.EXISTS_TAC ‘y'’ >> rw [],
      (* goal 3 (of 10) *)
      Q.PAT_X_ASSUM ‘open_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      qabbrev_tac ‘X = {z} UNION {x} UNION FV y UNION FV P UNION FV Q UNION FV P'’ \\
     ‘FINITE X’ by rw [Abbr ‘X’] \\
      Q_TAC (NEW_TAC "z'") ‘X’ \\
      Q.PAT_X_ASSUM ‘FINITE X’ K_TAC >> fs [Abbr ‘X’, IN_UNION] \\
      Know ‘InputS x z P' = InputS x z' (tpm [(z',z)] P')’
      >- (MATCH_MP_TAC tpm_ALPHA_InputS >> art []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘P'' = tpm [(z',z)] P'’ \\
      Q.PAT_X_ASSUM ‘!P Q x z P'. R P Q ==> TRANS P (InputS x z P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘y’, ‘x’, ‘z'’, ‘P''’]) >> rw [] \\
      rename1 ‘TRANS y (InputS x z' y')’ \\
      Q.PAT_X_ASSUM ‘open_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!P Q x z P'. R' P Q ==> TRANS P (InputS x z P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘Q’, ‘x’, ‘z'’, ‘y'’]) >> rw [] \\
      Know ‘InputS x z' Q' = InputS x z (tpm [(z,z')] Q')’
      >- (MATCH_MP_TAC tpm_ALPHA_InputS >> art [] \\
          irule FV_InputS_lemma \\
          qexistsl_tac [‘Q’, ‘x’, ‘z'’] >> rw []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘Q'' = tpm [(z,z')] Q'’ \\
      Q.EXISTS_TAC ‘Q''’ >> art [] \\
     ‘P' = tpm [(z',z)] P''’ by rw [Abbr ‘P''’] >> POP_ORW \\
     ‘tpm [(z',z)] P'' = tpm [(z,z')] P''’
        by rw [Once pmact_flip_args] >> POP_ORW \\
      Q.EXISTS_TAC ‘tpm [(z,z')] y'’ >> simp [Abbr ‘Q''’],
      (* goal 4 (of 10) *)
      Q.PAT_X_ASSUM ‘open_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!P Q a b P'. R P Q ==>
                                  TRANS P (FreeOutput a b P') ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘y’, ‘a’, ‘b’, ‘P'’]) >> rw [] \\
      rename1 ‘TRANS y (FreeOutput a b y')’ \\
      Q.PAT_X_ASSUM ‘open_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!P Q a b P'. R' P Q ==>
                                  TRANS P (FreeOutput a b P') ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘Q’, ‘a’, ‘b’, ‘y'’]) >> rw [] \\
      Q.EXISTS_TAC ‘Q'’ >> rw [] \\
      Q.EXISTS_TAC ‘y'’ >> rw [],
      (* goal 5 (of 10) *)
      Q.PAT_X_ASSUM ‘open_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      qabbrev_tac ‘X = {z} UNION {x} UNION FV y UNION FV P UNION FV Q UNION FV P'’ \\
     ‘FINITE X’ by rw [Abbr ‘X’] \\
      Q_TAC (NEW_TAC "z'") ‘X’ \\
      Q.PAT_X_ASSUM ‘FINITE X’ K_TAC >> fs [Abbr ‘X’, IN_UNION] \\
      Know ‘BoundOutput x z P' = BoundOutput x z' (tpm [(z',z)] P')’
      >- (MATCH_MP_TAC tpm_ALPHA_BoundOutput >> art []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘P'' = tpm [(z',z)] P'’ \\
      Q.PAT_X_ASSUM ‘!P Q x z P'. R P Q ==>
                                  TRANS P (BoundOutput x z P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘P’, ‘y’, ‘x’, ‘z'’, ‘P''’]) >> rw [] \\
      rename1 ‘TRANS y (BoundOutput x z' y')’ \\
      Q.PAT_X_ASSUM ‘open_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!P Q x z P'. R' P Q ==>
                                  TRANS P (BoundOutput x z P') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘Q’, ‘x’, ‘z'’, ‘y'’]) >> rw [] \\
      Know ‘BoundOutput x z' Q' = BoundOutput x z (tpm [(z,z')] Q')’
      >- (MATCH_MP_TAC tpm_ALPHA_BoundOutput >> art [] \\
          irule FV_BoundOutput_lemma \\
          qexistsl_tac [‘Q’, ‘x’, ‘z'’] >> rw []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘Q'' = tpm [(z,z')] Q'’ \\
      Q.EXISTS_TAC ‘Q''’ >> art [] \\
     ‘P' = tpm [(z',z)] P''’ by rw [Abbr ‘P''’] >> POP_ORW \\
     ‘tpm [(z',z)] P'' = tpm [(z,z')] P''’
        by rw [Once pmact_flip_args] >> POP_ORW \\
      Q.EXISTS_TAC ‘tpm [(z,z')] y'’ >> simp [Abbr ‘Q''’],
      (* goal 6 (of 10) *)
      rename1 ‘R P y'’ >> rename1 ‘R' y Q’ \\
      Q.PAT_X_ASSUM ‘open_simulation R’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘open_simulation R'’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.EXISTS_TAC ‘tpm pi y’ >> rw [],
      (* goal 7 (of 10) *)
      rename1 ‘R P y'’ >> rename1 ‘R' y Q’ \\
      rename1 ‘TRANS Q (TauR Q')’ \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R' y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!x y x'. R' y x ==> TRANS x (TauR x') ==> _’
        (MP_TAC o Q.SPECL [‘Q’, ‘y’, ‘Q'’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!x y x''. R y x ==> TRANS x (TauR x') ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘P’, ‘y'’]) >> rw [] \\
      rename1 ‘TRANS P (TauR P')’ \\
      Q.EXISTS_TAC ‘P'’ >> rw [] \\
      Q.EXISTS_TAC ‘y'’ >> rw [],
      (* goal 8 (of 10) *)
      rename1 ‘R P y'’ >> rename1 ‘R' y Q’ \\
      rename1 ‘TRANS Q (InputS x z Q')’ \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R' y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      qabbrev_tac ‘X = {z} UNION {x} UNION FV y UNION FV P UNION FV Q UNION FV Q'’ \\
     ‘FINITE X’ by rw [Abbr ‘X’] \\
      Q_TAC (NEW_TAC "z'") ‘X’ \\
      Q.PAT_X_ASSUM ‘FINITE X’ K_TAC >> fs [Abbr ‘X’, IN_UNION] \\
      Know ‘InputS x z Q' = InputS x z' (tpm [(z',z)] Q')’
      >- (MATCH_MP_TAC tpm_ALPHA_InputS >> art []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘Q'' = tpm [(z',z)] Q'’ \\
      Q.PAT_X_ASSUM
        ‘!x y x' z x''. R' y x ==> TRANS x (InputS x' z x'') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘Q’, ‘y’, ‘x’, ‘z'’, ‘Q''’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM
        ‘!x y x' z x''. R y x ==> TRANS x (InputS x' z x'') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘P’, ‘x’, ‘z'’, ‘y'’]) >> rw [] \\
      rename1 ‘TRANS P (InputS x z' P')’ \\
      Know ‘InputS x z' P' = InputS x z (tpm [(z,z')] P')’
      >- (MATCH_MP_TAC tpm_ALPHA_InputS >> art [] \\
          irule FV_InputS_lemma \\
          qexistsl_tac [‘P’, ‘x’, ‘z'’] >> rw []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘P'' = tpm [(z,z')] P'’ \\
      Q.EXISTS_TAC ‘P''’ >> art [] \\
     ‘Q' = tpm [(z',z)] Q''’ by rw [Abbr ‘Q''’] >> POP_ORW \\
     ‘tpm [(z',z)] Q'' = tpm [(z,z')] Q''’
        by rw [Once pmact_flip_args] >> POP_ORW \\
      Q.EXISTS_TAC ‘tpm [(z,z')] y'’ >> simp [Abbr ‘P''’],
      (* goal 9 (of 10) *)
      rename1 ‘R P y'’ >> rename1 ‘R' y Q’ \\
      rename1 ‘TRANS Q (FreeOutput a b Q')’ \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R' y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!x y a b x'. R' y x ==>
                                  TRANS x (FreeOutput a b x') ==> _’
        (MP_TAC o Q.SPECL [‘Q’, ‘y’, ‘a’, ‘b’, ‘Q'’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!x y a b x'. R y x ==>
                                  TRANS x (FreeOutput a b x') ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘P’, ‘a’, ‘b’, ‘y'’]) >> rw [] \\
      rename1 ‘TRANS P (FreeOutput a b P')’ \\
      Q.EXISTS_TAC ‘P'’ >> rw [] \\
      Q.EXISTS_TAC ‘y'’ >> rw [],
      (* goal 10 (of 10) *)
      rename1 ‘R P y'’ >> rename1 ‘R' y Q’ \\
      rename1 ‘TRANS Q (BoundOutput x z Q')’ \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R' y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      qabbrev_tac ‘X = {z} UNION {x} UNION FV y UNION FV P UNION FV Q UNION FV Q'’ \\
     ‘FINITE X’ by rw [Abbr ‘X’] \\
      Q_TAC (NEW_TAC "z'") ‘X’ \\
      Q.PAT_X_ASSUM ‘FINITE X’ K_TAC >> fs [Abbr ‘X’, IN_UNION] \\
      Know ‘BoundOutput x z Q' = BoundOutput x z' (tpm [(z',z)] Q')’
      >- (MATCH_MP_TAC tpm_ALPHA_BoundOutput >> art []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘Q'' = tpm [(z',z)] Q'’ \\
      Q.PAT_X_ASSUM ‘!x y x' z x''. R' y x ==>
                                    TRANS x (BoundOutput x' z x'') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘Q’, ‘y’, ‘x’, ‘z'’, ‘Q''’]) >> rw [] \\
      Q.PAT_X_ASSUM ‘open_simulation (\x y. R y x)’
        (STRIP_ASSUME_TAC o SIMP_RULE (std_ss ++ DNF_ss) [open_simulation_def]) \\
      Q.PAT_X_ASSUM ‘!x y x' z x''. R y x ==>
                                    TRANS x (BoundOutput x' z x'') /\ _ ==> _’
        (MP_TAC o Q.SPECL [‘y’, ‘P’, ‘x’, ‘z'’, ‘y'’]) >> rw [] \\
      rename1 ‘TRANS P (BoundOutput x z' P')’ \\
      Know ‘BoundOutput x z' P' = BoundOutput x z (tpm [(z,z')] P')’
      >- (MATCH_MP_TAC tpm_ALPHA_BoundOutput >> art [] \\
          irule FV_BoundOutput_lemma \\
          qexistsl_tac [‘P’, ‘x’, ‘z'’] >> rw []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘P'' = tpm [(z,z')] P'’ \\
      Q.EXISTS_TAC ‘P''’ >> art [] \\
     ‘Q' = tpm [(z',z)] Q''’ by rw [Abbr ‘Q''’] >> POP_ORW \\
     ‘tpm [(z',z)] Q'' = tpm [(z,z')] Q''’
        by rw [Once pmact_flip_args] >> POP_ORW \\
      Q.EXISTS_TAC ‘tpm [(z,z')] y'’ >> simp [Abbr ‘P''’] ]
QED

Theorem open_bisimilar_equivalence :
    equivalence open_bisimilar
Proof
    rw [equivalence_def]
 >| [ (* goal 1 (of 3) *)
      rw [reflexive_def, open_bisimilar_reflexive],
      (* goal 2 (of 3) *)
      rw [symmetric_def] \\
      EQ_TAC >> rw [open_bisimilar_symmetric],
      (* goal 3 (of 3) *)
      rw [transitive_def] \\
      MATCH_MP_TAC open_bisimilar_transitive \\
      Q.EXISTS_TAC ‘y’ >> art [] ]
QED

val _ = export_theory ();
val _ = html_theory "open_bisimulation";
