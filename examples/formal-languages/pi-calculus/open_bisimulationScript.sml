(* ========================================================================== *)
(* FILE          : open_bisimulationScript.sml                                *)
(* DESCRIPTION   : Open bisimulation for the pi-calculus                      *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory relationTheory hurdUtils;

open nomsetTheory NEWLib pi_agentTheory;

val _ = new_theory "open_bisimulation";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* The original open transition relation *)
Inductive TRANS :
[TAU:]
    !P. TRANS (Tau P) (TauR P)
[INPUT:]
    !a x P. x <> a ==> TRANS (Input a x P) (InputS a x P)
[OUTPUT:]
    !a b P. TRANS (Output a b P) (FreeOutput a b P)
[MATCH:]
    !P Rs b. TRANS P Rs ==> TRANS (Match b b P) Rs
[MISMACH:]
    !P Rs a b. TRANS P Rs /\ a <> b ==> TRANS (Mismatch a b P) Rs

[OPEN:]
    !P P' a b. TRANS P (FreeOutput a b P') /\ a <> b ==>
               TRANS (Res b P) (BoundOutput a b P')
[SUM1:]
    !P Q Rs. TRANS P Rs ==> TRANS (Sum P Q) Rs
[SUM2:]
    !P Q Rs. TRANS Q Rs ==> TRANS (Sum P Q) Rs

[PAR1_I:]
    !P P' Q a x.
       TRANS P (InputS a x P') /\ x # P /\ x # Q /\ x <> a ==>
       TRANS (Par P Q) (InputS a x (Par P' Q))
[PAR1_BO:]
    !P P' Q a x.
       TRANS P (BoundOutput a x P') /\ x # P /\ x # Q /\ x <> a ==>
       TRANS (Par P Q) (BoundOutput a x (Par P' Q))
[PAR1_FO:]
    !P P' Q a b.
       TRANS P (FreeOutput a b P') ==>
       TRANS (Par P Q) (FreeOutput a b (Par P' Q))
[PAR1_T:]
    !P P' Q. TRANS P (TauR P') ==> TRANS (Par P Q) (TauR (Par P' Q))

[PAR2_I:]
    !P Q Q' a x.
       TRANS Q (InputS a x Q') /\ x # Q /\ x # P /\ x <> a ==>
       TRANS (Par P Q) (InputS a x (Par P Q'))
[PAR2_BO:]
    !P Q Q' a x.
       TRANS Q (BoundOutput a x Q') /\ x # Q /\ x # P /\ x <> a ==>
       TRANS (Par P Q) (BoundOutput a x (Par P Q'))
[PAR2_FO:]
    !P Q Q' a b.
       TRANS Q (FreeOutput a b Q') ==>
       TRANS (Par P Q) (FreeOutput a b (Par P Q'))
[PAR2_T:]
    !P Q Q'. TRANS Q (TauR Q') ==> TRANS (Par P Q) (TauR (Par P Q'))

[COMM1:] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a b x.
       TRANS P (InputS a x P') /\ TRANS Q (FreeOutput a b Q') /\
       x # P /\ x # Q /\ x <> a /\ x <> b /\ x # Q' ==>
       TRANS (Par P Q) (TauR (Par (tpm [(x,b)] P') Q'))
[COMM2:] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a b x.
       TRANS P (FreeOutput a b P') /\ TRANS Q (InputS a x Q') /\
       x # Q /\ x # P /\ x <> a /\ x <> b /\ x # P' ==>
       TRANS (Par P Q) (TauR (Par P' (tpm [(x,b)] Q')))
[CLOSE1:] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a x y.
       TRANS P (InputS a x P') /\
       TRANS Q (BoundOutput a y Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # Q' /\ y <> a /\ y # P' /\ x <> y ==>
       TRANS (Par P Q) (TauR (Res y (Par (tpm [(x,y)] P') Q')))
[CLOSE2:] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a x y.
       TRANS P (BoundOutput a y P') /\
       TRANS Q (InputS a x Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # P' /\ y <> a /\ y # Q' /\ x <> y ==>
       TRANS (Par P Q) (TauR (Res y (Par P' (tpm [(x,y)] Q'))))
[RES_I:]
    !P P' a x y.
       TRANS P (InputS a x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       TRANS (Res y P) (InputS a x (Res y P'))
[RES_BO:]
    !P P' a x y.
       TRANS P (BoundOutput a x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       TRANS (Res y P) (BoundOutput a x (Res y P'))
[RES_FO:]
    !P P' a b y.
       TRANS P (FreeOutput a b P') /\
       y <> a /\ y <> b ==>
       TRANS (Res y P) (FreeOutput a b (Res y P'))
[RES_T:]
    !P P' y.
       TRANS P (TauR P') ==> TRANS (Res y P) (TauR (Res y P'))
End

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

Theorem FV_InputS_lemma[local] :
    !P Q. TRANS P Q ==>
         !P' x z. Q = InputS x z P' /\ x <> z /\ z # P /\
                      !y. y # P /\ y <> z ==> y # P'
Proof
    cheat
QED

Theorem FV_InputS :
    !P P' x z y. TRANS P (InputS x z P') /\ x <> z /\ z # P /\
                 y # P /\ y <> z ==> y # P'
Proof
    METIS_TAC [FV_InputS_lemma]
QED

Theorem FV_BoundOutput_lemma[local] :
    !P Q. TRANS P Q ==>
          !P' x z. Q = BoundOutput x z P' /\ x <> z /\ z # P /\
                       !y. y # P /\ y <> z ==> y # P'
Proof
    cheat
QED

Theorem FV_BoundOutput :
    !P P' x z y. TRANS P (BoundOutput x z P') /\ x <> z /\ z # P /\
                 y # P /\ y <> z ==> y # P'
Proof
    METIS_TAC [FV_BoundOutput_lemma]
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
          irule FV_InputS \\
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
          irule FV_BoundOutput \\
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
          irule FV_InputS \\
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
          irule FV_BoundOutput \\
          qexistsl_tac [‘P’, ‘x’, ‘z'’] >> rw []) \\
      DISCH_THEN (fs o wrap) \\
      qabbrev_tac ‘P'' = tpm [(z,z')] P'’ \\
      Q.EXISTS_TAC ‘P''’ >> art [] \\
     ‘Q' = tpm [(z',z)] Q''’ by rw [Abbr ‘Q''’] >> POP_ORW \\
     ‘tpm [(z',z)] Q'' = tpm [(z,z')] Q''’
        by rw [Once pmact_flip_args] >> POP_ORW \\
      Q.EXISTS_TAC ‘tpm [(z,z')] y'’ >> simp [Abbr ‘P''’] ]
QED

Theorem equivalence_open_bisimilar :
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
