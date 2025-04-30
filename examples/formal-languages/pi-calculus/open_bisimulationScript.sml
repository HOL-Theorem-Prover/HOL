(* ========================================================================== *)
(* FILE          : open_bisimulationScript.sml                                *)
(* DESCRIPTION   : Open bisimulation for the pi-calculus with mismatch        *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory set_relationTheory hurdUtils;

open nomsetTheory NEWLib pi_agentTheory;

val _ = new_theory "open_bisimulation";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* ----------------------------------------------------------------------
   Pi-calculus as a nominal datatype in HOL4

   HOL4 syntax ('free and 'bound are special type variables (alias of string)

   Nominal_datatype :

           name = Name 'free

           pi   = Nil                      (* 0 *)
                | Tau pi                   (* tau.P *)
                | Input name 'bound pi     (* a(x).P *)
                | Output name name pi      (* {a}b.P *)
                | Match name name pi       (* [a == b] P *)
                | Mismatch name name pi    (* [a <> b] P *)
                | Sum pi pi                (* P + Q *)
                | Par pi pi                (* P | Q *)
                | Res 'bound pi            (* nu x. P *)

       residual = TauR pi
                | InputS name 'bound pi
                | FreeOutput name name pi
                | BoundOutput name 'bound pi
   End

   NOTE: Replication ("!") is not supported.
   ---------------------------------------------------------------------- *)

(* NOTE: We fallback to “:(string # string) -> bool” for the need of permutation
   on pairs in the dist set.
 *)
Type dist[pp] = “:(string # string) -> bool”

(* NOTE: We use uncurried relation (HOL preferred) given in relationTheory *)
Definition distinction_def :
    distinction (D :dist) <=> FINITE D /\ symmetric D UNIV /\ irreflexive D UNIV
End

Overload FV = “domain :dist -> string set”
Overload "#" = “\v (D :dist). v NOTIN FV D”

Theorem domain_alt :
    !r. domain r = IMAGE FST r
Proof
    rw [Once EXTENSION, in_domain]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘(x,y)’ >> rw [])
 >> rename1 ‘z IN r’
 >> PairCases_on ‘z’
 >> Q.EXISTS_TAC ‘z1’ >> rw []
QED

(* |- !D. FV D = IMAGE FST D *)
Theorem FV_distinction =
        domain_alt |> INST_TYPE [alpha |-> “:string”, beta |-> “:string”]
                   |> Q.SPEC ‘D’ |> GEN_ALL

Theorem FV_distinction_alt :
    !D. distinction D ==> FV D = IMAGE SND D
Proof
    rw [distinction_def, domain_alt, symmetric_def]
 >> simp [Once EXTENSION, EXISTS_PROD]
QED

Theorem finite_domain[simp] :
    distinction D ==> FINITE (FV D)
Proof
    rw [distinction_def, domain_alt]
QED

Theorem distinction_empty[simp] :
    distinction {}
Proof
    rw [distinction_def, symmetric_def, irreflexive_def]
QED

Theorem distinction_union :
    !D1 D2. distinction D1 /\ distinction D2 ==> distinction (D1 UNION D2)
Proof
    rw [distinction_def]
 >- (MATCH_MP_TAC symmetric_union >> art [])
 >> MATCH_MP_TAC irreflexive_union >> art []
QED

(* NOTE: This is permutation operation on distinction *)
Overload dpm[local] = “setpm (pair_pmact string_pmact string_pmact)”

Theorem distinction_dpm_lemma[local] :
    !pi d. distinction d ==> distinction (dpm pi d)
Proof
    rw [distinction_def]
 >- fs [symmetric_def]
 >> fs [irreflexive_def]
QED

Theorem distinction_dpm[simp] :
    distinction (dpm pi d) <=> distinction d
Proof
    reverse EQ_TAC
 >- rw [distinction_dpm_lemma]
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘REVERSE pi’, ‘dpm pi d’] distinction_dpm_lemma)
 >> simp []
QED

Theorem dpm_unchanged_lemma[local] :
    !D. FINITE D ==> !pi. DISJOINT (set (MAP FST pi)) (IMAGE FST D) /\
                          DISJOINT (set (MAP FST pi)) (IMAGE SND D) /\
                          DISJOINT (set (MAP SND pi)) (IMAGE FST D) /\
                          DISJOINT (set (MAP SND pi)) (IMAGE SND D) ==>
                          dpm pi D = D
Proof
    HO_MATCH_MP_TAC FINITE_INDUCT
 >> rw [pmact_INSERT]
 >> PairCases_on ‘e’ >> fs []
 >> Know ‘lswapstr pi e0 = e0’
 >- (MATCH_MP_TAC lswapstr_unchanged' >> art [])
 >> Rewr'
 >> Know ‘lswapstr pi e1 = e1’
 >- (MATCH_MP_TAC lswapstr_unchanged' >> art [])
 >> Rewr
QED

Theorem dpm_unchanged :
    !D pi. distinction D /\
           DISJOINT (set (MAP FST pi)) (FV D) /\
           DISJOINT (set (MAP SND pi)) (FV D) ==> dpm pi D = D
Proof
    rpt STRIP_TAC
 >> irule dpm_unchanged_lemma
 >> simp [GSYM FV_distinction, GSYM FV_distinction_alt]
 >> fs [distinction_def]
QED

(* The original open transition relation *)
Inductive TRANS :
[TAU]
    !P.       TRANS (Tau P) (TauR P)
[INPUT]
    !a x P.   x <> a ==> TRANS (Input (Name a) x P) (InputS (Name a) x P)
[OUTPUT]
    !a b P.   TRANS (Output (Name a) (Name b) P) (FreeOutput (Name a) (Name b) P)
[MATCH]
    !P Rs b.   TRANS P Rs ==> TRANS (Match (Name b) (Name b) P) Rs
[MISMACH]
    !P Rs a b. TRANS P Rs /\ a <> b ==> TRANS (Mismatch (Name a) (Name b) P) Rs

[OPEN]
    !P P' a b. TRANS P (FreeOutput (Name a) (Name b) P') /\ a <> b ==>
               TRANS (Res b P) (BoundOutput (Name a) b P')
[SUM1]
    !P Q Rs. TRANS P Rs ==> TRANS (Sum P Q) Rs
[SUM2]
    !P Q Rs. TRANS Q Rs ==> TRANS (Sum P Q) Rs

[PAR1_I]
    !P P' Q a x.
       TRANS P (InputS (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       TRANS (Par P Q) (InputS (Name a) x (Par P' Q))
[PAR1_BO]
    !P P' Q a x.
       TRANS P (BoundOutput (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       TRANS (Par P Q) (BoundOutput (Name a) x (Par P' Q))
[PAR1_FO]
    !P P' Q a b.
       TRANS P (FreeOutput (Name a) (Name b) P') ==>
       TRANS (Par P Q) (FreeOutput (Name a) (Name b) (Par P' Q))
[PAR1_T]
    !P P' Q. TRANS P (TauR P') ==> TRANS (Par P Q) (TauR (Par P' Q))

[PAR2_I]
    !P Q Q' a x.
       TRANS Q (InputS (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       TRANS (Par P Q) (InputS (Name a) x (Par P Q'))
[PAR2_BO]
    !P Q Q' a x.
       TRANS Q (BoundOutput (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       TRANS (Par P Q) (BoundOutput (Name a) x (Par P Q'))
[PAR2_FO]
    !P Q Q' a b.
       TRANS Q (FreeOutput (Name a) (Name b) Q') ==>
       TRANS (Par P Q) (FreeOutput (Name a) (Name b) (Par P Q'))
[PAR2_T]
    !P Q Q'. TRANS Q (TauR Q') ==> TRANS (Par P Q) (TauR (Par P Q'))

[COMM1] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a b x.
       TRANS P (InputS (Name a) x P') /\ TRANS Q (FreeOutput (Name a) (Name b) Q') /\
       x # P /\ x # Q /\ x <> a /\ x <> b /\ x # Q' ==>
       TRANS (Par P Q) (TauR (Par (tpm [(x,b)] P') Q'))
[COMM2] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a b x.
       TRANS P (FreeOutput (Name a) (Name b) P') /\ TRANS Q (InputS (Name a) x Q') /\
       x # Q /\ x # P /\ x <> a /\ x <> b /\ x # P' ==>
       TRANS (Par P Q) (TauR (Par P' (tpm [(x,b)] Q')))
[CLOSE1] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a x y.
       TRANS P (InputS (Name a) x P') /\
       TRANS Q (BoundOutput (Name a) y Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # Q' /\ y <> a /\ y # P' /\ x <> y ==>
       TRANS (Par P Q) (TauR (Res y (Par (tpm [(x,y)] P') Q')))
[CLOSE2] (* TODO: tpm should change to SUB *)
    !P P' Q Q' a x y.
       TRANS P (BoundOutput (Name a) y P') /\
       TRANS Q (InputS (Name a) x Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # P' /\ y <> a /\ y # Q' /\ x <> y ==>
       TRANS (Par P Q) (TauR (Res y (Par P' (tpm [(x,y)] Q'))))
[RES_I]
    !P P' a x y.
       TRANS P (InputS (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       TRANS (Res y P) (InputS (Name a) x (Res y P'))
[RES_BO]
    !P P' a x y.
       TRANS P (BoundOutput (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       TRANS (Res y P) (BoundOutput (Name a) x (Res y P'))
[RES_FO]
    !P P' a b y.
       TRANS P (FreeOutput (Name a) (Name b) P') /\
       y <> a /\ y <> b ==>
       TRANS (Res y P) (FreeOutput (Name a) (Name b) (Res y P'))
[RES_T]
    !P P' y.
       TRANS P (TauR P') ==> TRANS (Res y P) (TauR (Res y P'))
End

(* Open transition relation w.r.t. distinction *)
Inductive DTRANS :
[DTAU]
    !D P. DTRANS (D :dist) (Tau P) (TauR P)
[DINPUT]
    !D a x P. x <> a ==> DTRANS D (Input (Name a) x P) (InputS (Name a) x P)
[DOUTPUT]
    !D a b P. DTRANS D (Output (Name a) (Name b) P)
                       (FreeOutput (Name a) (Name b) P)
[DMATCH]
    !D P Rs b. DTRANS D P Rs ==> DTRANS D (Match (Name b) (Name b) P) Rs
[DMISMACH]
    !D P Rs a b.
       distinction D /\ (a,b) IN D /\ DTRANS D P Rs ==>
       DTRANS D (Mismatch (Name a) (Name b) P) Rs

[DOPEN]
    !D D' P P' a b.
    (* begin extra antecedents *)
       distinction D /\ b # D /\
       D' = D UNION sc {(a,s) | s IN FV (Res b P)} /\
    (* end extra antecedents *)
       DTRANS D' P (FreeOutput (Name a) (Name b) P') /\ a <> b ==>
       DTRANS D (Res b P) (BoundOutput (Name a) b P')
[DSUM1]
    !D P Q Rs. DTRANS D P Rs ==> DTRANS D (Sum P Q) Rs
[DSUM2]
    !D P Q Rs. DTRANS D Q Rs ==> DTRANS D (Sum P Q) Rs

[DPAR1_I]
    !D P P' Q a x.
       DTRANS D P (InputS (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       DTRANS D (Par P Q) (InputS (Name a) x (Par P' Q))
[DPAR1_BO]
    !D P P' Q a x.
       DTRANS D P (BoundOutput (Name a) x P') /\ x # P /\ x # Q /\ x <> a ==>
       DTRANS D (Par P Q) (BoundOutput (Name a) x (Par P' Q))
[DPAR1_FO]
    !D P P' Q a b.
       DTRANS D P (FreeOutput (Name a) (Name b) P') ==>
       DTRANS D (Par P Q) (FreeOutput (Name a) (Name b) (Par P' Q))
[DPAR1_T]
    !D P P' Q. DTRANS D P (TauR P') ==> DTRANS D (Par P Q) (TauR (Par P' Q))

[DPAR2_I]
    !D P Q Q' a x.
       DTRANS D Q (InputS (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       DTRANS D (Par P Q) (InputS (Name a) x (Par P Q'))
[DPAR2_BO]
    !D P Q Q' a x.
       DTRANS D Q (BoundOutput (Name a) x Q') /\ x # Q /\ x # P /\ x <> a ==>
       DTRANS D (Par P Q) (BoundOutput (Name a) x (Par P Q'))
[DPAR2_FO]
    !D P Q Q' a b.
       DTRANS D Q (FreeOutput (Name a) (Name b) Q') ==>
       DTRANS D (Par P Q) (FreeOutput (Name a) (Name b) (Par P Q'))
[DPAR2_T]
    !D P Q Q'. DTRANS D Q (TauR Q') ==> DTRANS D (Par P Q) (TauR (Par P Q'))

[DCOMM1] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a b x.
       DTRANS D P (InputS (Name a) x P') /\
       DTRANS D Q (FreeOutput (Name a) (Name b) Q') /\
       x # P /\ x # Q /\ x <> a /\ x <> b /\ x # Q' ==>
       DTRANS D (Par P Q) (TauR (Par (tpm [(x,b)] P') Q'))
[DCOMM2] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a b x.
       DTRANS D P (FreeOutput (Name a) (Name b) P') /\
       DTRANS D Q (InputS (Name a) x Q') /\
       x # Q /\ x # P /\ x <> a /\ x <> b /\ x # P' ==>
       DTRANS D (Par P Q) (TauR (Par P' (tpm [(x,b)] Q')))
[DCLOSE1] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a x y.
       DTRANS D P (InputS (Name a) x P') /\
       DTRANS D Q (BoundOutput (Name a) y Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # Q' /\ y <> a /\ y # P' /\ x <> y ==>
       DTRANS D (Par P Q) (TauR (Res y (Par (tpm [(x,y)] P') Q')))
[DCLOSE2] (* TODO: tpm should change to SUB *)
    !D P P' Q Q' a x y.
       DTRANS D P (BoundOutput (Name a) y P') /\
       DTRANS D Q (InputS (Name a) x Q') /\
       x # P /\ x # Q /\ y # P /\ y # Q /\
       x <> a /\ x # P' /\ y <> a /\ y # Q' /\ x <> y ==>
       DTRANS D (Par P Q) (TauR (Res y (Par P' (tpm [(x,y)] Q'))))

[DRES_I]
    !D D' P P' a x y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (InputS (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       DTRANS D (Res y P) (InputS (Name a) x (Res y P'))
[DRES_BO]
    !D D' P P' a x y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (BoundOutput (Name a) x P') /\
       y <> a /\ y <> x /\ x # P /\ x <> a ==>
       DTRANS D (Res y P) (BoundOutput (Name a) x (Res y P'))
[DRES_FO]
    !D D' P P' a b y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (FreeOutput (Name a) (Name b) P') /\
       y <> a /\ y <> b ==>
       DTRANS D (Res y P) (FreeOutput (Name a) (Name b) (Res y P'))
[DRES_T]
    !D D' P P' y.
    (* begin extra antecedents *)
       distinction D /\
       D' = D UNION sc {(y,s) | s | s IN FV (Res y P)} /\
    (* end extra antecedents *)
       DTRANS D' P (TauR P') ==> DTRANS D (Res y P) (TauR (Res y P'))
End

(* NOTE: "simulation" is a property of 3-way relation R as tuples (P, Q, D), where
   P and Q are pi-agents, D is a distinction.
 *)
Definition dist_simulation_def :
    dist_simulation (R :(pi # pi # dist) set) <=>
    !P Q D. (P,Q,D) IN R ==>
    (* 0 *)
       distinction D /\
    (* 1 *)
      (!pi. (tpm pi P, tpm pi Q, dpm pi D) IN R) /\
    (* 2 *)
      (!D'. D SUBSET D' /\ distinction D' ==> (P,Q,D') IN R) /\
    (* 3a *)
      (!P'. DTRANS D P (TauR P') ==>
            ?Q'. DTRANS D Q (TauR Q') /\ (P',Q',D) IN R) /\
    (* 3b: enriched with ‘x # D /\ x # P’ *)
      (!a x P'. DTRANS D P (InputS (Name a) x P') /\ x # D /\ x # P /\ x # Q ==>
                ?Q'. DTRANS D Q (InputS (Name a) x Q') /\ (P',Q',D) IN R) /\
    (* 3c *)
      (!a b P'. DTRANS D P (FreeOutput (Name a) (Name b) P') ==>
                ?Q'. DTRANS D Q (FreeOutput (Name a) (Name b) Q') /\
                    (P',Q',D) IN R) /\
    (* 4 *)
      (!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==>
                ?Q' D'. DTRANS D Q (BoundOutput (Name b) x Q') /\
                        D' = D UNION sc {(b, x) | x | x IN FV (Res b Q)} /\
                       (P',Q',D') IN R)
End

Theorem dist_simulation_id :
    dist_simulation {x | ?P D. x = (P,P,D) /\ distinction D}
Proof
    rw [dist_simulation_def]
 >> MATCH_MP_TAC distinction_union >> art []
 >> rw [distinction_def]
 >- (MATCH_MP_TAC finite_sc \\
     qmatch_abbrev_tac ‘FINITE s’ \\
     irule SUBSET_FINITE \\
     Q.EXISTS_TAC ‘{(b,y) | y | y IN FV P}’ \\
     qunabbrev_tac ‘s’ \\
     reverse CONJ_TAC >- rw [SUBSET_DEF] \\
     qmatch_abbrev_tac ‘FINITE s’ \\
     Know ‘s = IMAGE (\y. (b,y)) (FV P)’
     >- rw [Abbr ‘s’, Once EXTENSION] >> Rewr' \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [])
 >> MATCH_MP_TAC sc_irreflexive
 >> rw [irreflexive_def]
QED

Theorem dist_simulation_union :
    !R1 R2. dist_simulation R1 /\ dist_simulation R2 ==>
            dist_simulation (R1 UNION R2)
Proof
    rw [dist_simulation_def] (* 7+7 subgoals *)
 (* goal 1 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
      (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [])
 (* goal 2 (of 14) *)
 >- (DISJ1_TAC \\
     Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [])
 (* goal 3 (of 14) *)
 >- (DISJ1_TAC \\
     Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [])
 (* goal 4 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!P'. DTRANS D P (TauR P') ==> _’
       (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 5 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!a x P'.
                       DTRANS D P (InputS (Name a) x P') /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘a’, ‘x’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 6 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!a b P'.
                       DTRANS D P (FreeOutput (Name a) (Name b) P') ==> _’
       (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 7 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R1 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==> _’
       (MP_TAC o Q.SPECL [‘b’, ‘x’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 8 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [])
 (* goal 9 (of 14) *)
 >- (DISJ2_TAC \\
     Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [])
 (* goal 10 (of 14) *)
 >- (DISJ2_TAC \\
     Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [])
 (* goal 11 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!P'. DTRANS D P (TauR P') ==> _’
       (MP_TAC o Q.SPEC ‘P'’) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 12 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!a x P'.
                       DTRANS D P (InputS (Name a) x P') /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘a’, ‘x’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 13 (of 14) *)
 >- (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!a b P'.
                       DTRANS D P (FreeOutput (Name a) (Name b) P') ==> _’
       (MP_TAC o Q.SPECL [‘a’, ‘b’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
 (* goal 14 (of 14) *)
 >> (Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R2 ==> _’
       (MP_TAC o Q.SPECL [‘P’, ‘Q’, ‘D’]) >> rw [] \\
     Q.PAT_X_ASSUM ‘!b x P'. DTRANS D P (BoundOutput (Name b) x P') ==> _’
       (MP_TAC o Q.SPECL [‘b’, ‘x’, ‘P'’]) >> rw [] \\
     Q.EXISTS_TAC ‘Q'’ >> rw [])
QED

Theorem dist_simulation_imp_distinction :
    !R P Q D. dist_simulation R /\ (P,Q,D) IN R ==> distinction D
Proof
    rw [dist_simulation_def]
 >> FIRST_X_ASSUM drule >> rw []
QED

Theorem dist_simulation_open_distinction :
    !R P Q D D'. dist_simulation R /\ (P,Q,D) IN R /\ D SUBSET D' /\
                 distinction D' ==> (P,Q,D') IN R
Proof
    rw [dist_simulation_def]
 >> Q.PAT_X_ASSUM ‘!P Q D. (P,Q,D) IN R ==> _’ drule >> rw []
QED

Definition dist_bisimulation_def :
    dist_bisimulation (R :(pi # pi # dist) set) <=>
    dist_simulation R /\ dist_simulation {(Q,P,D) | (P,Q,D) IN R}
End

Definition dist_bisimilar :
    dist_bisimilar P Q D <=> ?R. dist_bisimulation R /\ (P,Q,D) IN R
End

(* |- !P Q D.
        dist_bisimilar P Q D <=>
        ?R. (dist_simulation R /\ dist_simulation {(Q,P,D) | (P,Q,D) IN R}) /\
            (P,Q,D) IN R
 *)
Theorem dist_bisimilar_def =
        dist_bisimilar |> REWRITE_RULE [dist_bisimulation_def]

Theorem dist_bisimilar_imp_distinction :
    !P Q D. dist_bisimilar P Q D ==> distinction D
Proof
    rw [dist_bisimilar_def, dist_simulation_def]
 >> FIRST_X_ASSUM drule >> rw []
QED

Theorem dist_bisimilar_reflexive :
    !P D. distinction D ==> dist_bisimilar P P D
Proof
    rw [dist_bisimilar_def]
 >> Q.EXISTS_TAC ‘{x | ?P D. x = (P,P,D) /\ distinction D}’
 >> simp [dist_simulation_id]
 >> qmatch_abbrev_tac ‘dist_simulation R’
 >> Suff ‘R = {x | (?P D. x = (P,P,D) /\ distinction D)}’
 >- rw [dist_simulation_id]
 >> rw [Abbr ‘R’, Once EXTENSION]
QED

Theorem dist_bisimilar_symmetric :
    !P Q D. dist_bisimilar P Q D ==> dist_bisimilar Q P D
Proof
    rw [dist_bisimilar_def]
 >> qabbrev_tac ‘R' = {(Q,P,D) | (P,Q,D) IN R}’
 >> Q.EXISTS_TAC ‘R UNION R'’
 >> reverse CONJ_TAC
 >- (simp [] \\
     DISJ2_TAC >> rw [Abbr ‘R'’])
 >> CONJ_TAC
 >- (MATCH_MP_TAC dist_simulation_union >> art [])
 >> qmatch_abbrev_tac ‘dist_simulation R2’
 >> Suff ‘R2 = R UNION R'’
 >- (Rewr' \\
     MATCH_MP_TAC dist_simulation_union >> art [])
 >> rw [Once EXTENSION, Abbr ‘R2’, Abbr ‘R'’]
 >> EQ_TAC >> rw []
 >> PairCases_on ‘x’ (* this asserts (x0,x1,x2) *)
 >> rename1 ‘(P',Q',D') IN R’
 >> qexistsl_tac [‘P'’, ‘Q'’, ‘D'’] >> simp []
QED

val _ = export_theory ();
val _ = html_theory "open_bisimulation";
