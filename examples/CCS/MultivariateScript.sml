(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Unique Solution of CCS Equations (Multivariate Version)    *)
(*                                                                            *)
(* COPYRIGHTS    : 2019-2020 Fondazione Bruno Kessler, Italy (Chun Tian)      *)
(*                 2023-2024 The Australian National University (Chun Tian)   *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open combinTheory relationTheory pred_setTheory pred_setLib finite_mapTheory
     arithmeticTheory listTheory;

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory TraceTheory
     ObsCongrTheory ContractionTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory;

val _ = new_theory "Multivariate";

(* ========================================================================== *)
(*                             TABLE OF CONTENTS                              *)
(* -------------------------------------------------------------------------- *)
(*  Prologue:    Design Notes . . . . . . . . . . . . . . . . . . . . . L41   *)
(*  Section I:   Multivariate variable substitution . . . . . . . . . . L160  *)
(*  Section II:  Multivariate CCS contexts. . . . . . . . . . . . . . . L635  *)
(*  Section III: Weakly-guarded contexts. . . . . . . . . . . . . . . . L1240 *)
(*  Section IV:  Unique Solution of Equations . . . . . . . . . . . . . L1687 *)
(*  Section V:   Unique Solution of (Rooted) Contractions . . . . . . . L2791 *)
(*  Appendix:    Bibliography and some unfinished work. . . . . . . . . L3485 *)
(* ========================================================================== *)

val lset_ss = list_ss ++ PRED_SET_ss; (* list + pred_set *)

val _ = overload_on ( "STRONG_EQUIV", ``LIST_REL  STRONG_EQUIV``);
val _ = overload_on (   "WEAK_EQUIV", ``LIST_REL    WEAK_EQUIV``);
val _ = overload_on (    "OBS_CONGR", ``LIST_REL     OBS_CONGR``);
val _ = overload_on ("OBS_contracts", ``LIST_REL OBS_contracts``);

(* hide all other possible definitions of `fromList` -- this is a common name *)
val _ = hide "fromList";

(*                         -- DESIGN NOTES --

1. What's a multivariate CCS equation?

   - Xs: A list of equation variables: [X1; X2; ...; Xn] :'a list
   - Es: A list of arbitrary CCS terms: [E1; E2; ...; En] :'a CCS list

   ``ALL_DISTINCT Xs /\ (LENGTH Xs = LENGTH Es)`` must hold.

   The multivariete equation is actually the following equation group:

    / var (EL 0 Xs) = (EL 0 Es)
    | var (EL 1 Xs) = (EL 1 Es)
    + var (EL 2 Xs) = (EL 2 Es)   or   `MAP var Xs = Es`
    |              ...
    \ var (EL n Xs) = (EL n Es)

   The `=` (at left) could be `STRONG_EQUIV`, `WEAK_EQUIV`, `OBS_CONGR`
   or even `contracts`. (In the last case it's actually an inequation group.)

   Note that, it does NOT matter each `(EL i Es)` contains what variables:
   those free variables outside of X simply lead to no transition
   (like nil) according to [VAR_NO_TRANS]; those in X but not in `(EL i n)`
   simply causes `(EL i n)` not changed after the substitution.

   Also, we never need to express such this equation (group) in any
   theorem. Instead, we only need to express their solution(s).

2. What's a solution of (above) multiviriate CCS equation (group)?

   - Ps: A list of arbitrary CCS terms: [P1; P2; ...; Pn] :'a CCS list

   `Ps` is a solution of (above) multivariate CCS equation (group) iff:

    / (EL 0 Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)
    | (EL 1 Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)
    + (EL 2 Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)
    |          ...
    \ (EL n Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)

   or

    Ps = MAP (SUBST (ZIP Xs Ps)) Es

   (where ``ZIP Xs Ps`` is an alist of type ``:('a # 'a CCS) list``)

   or (abbrev.)

    (CCS_solution Es Xs Ps) : bool

   and

    (CCS_solution Es Xs) is the set of all solutions of `MAP var Xs = Es`.

3. What's an unique solution of (above) multivariate CCS equation (group)?

   If Ps and Qs are both solutions of `MAP var Xs = Es`, i.e.

      `CCS_solution Ps $= Es Xs /\ CCS_solution Qs $= Es Xs`,

   then, beside ``Ps = Qs`, we may also have:

      `(LIST_REL STRONG_EQUIV) Ps Qs`, or
      `(LIST_REL WEAK_EQUIV) Ps Qs`, or
      `(LIST_REL OBS_EQUIV) Ps Qs`

   Ps (or Qs) is called an "unique" solution (up to the corresponding
   equivalence relation).

4. What's a "weakly guarded" multivariate CCS equation (group)?

   An equation group is weakly guarded iff so is each equation in it.

  `weakly_guarded Xs E` means, for each X in Xs, if X is replaced by a
   hole [], the resulting context as lambda-term (\t. CCS_Subst E t X)
   must be WG:

   weakly_guarded Es Xs =
     !E X. MEM E Es /\ MEM X Xs ==> WG (\t. CCS_Subst E t X)

   NOTE 1: using `!e. CONTEXT e /\ (e (var X) = E) ==> WG e` is wrong.
   It appears in the conclusion of our EXPRESS/SOS'18 paper. The problem
   is, it's possible that there's no such CONTEXT e at all, e.g.
   when equation variables appear inside recursion operators, then
   `E` is still identified as a weakly guarded equation.

   Currently, there's a limitation that, our definition of WG
   doesn't have any recursion operator (unless in an irrelevant `p` of
   `\t. p`). This means, our equation (free) variables can never be
   wrapped by another bounded variable in the CCS equations.  Fixing
   this limitation may falsify the entire unique-solution of
   contraction theorm as I currently observed (but didn't say anywhere
   else), simply because certain proof steps cannot be fixed under
   this possibility. This is a potential future direction in the future.

   NOTE 2: using `?e. CONTEXT e /\ (e (var X) = E) /\ WG e` is even
   worse, because `E` may contain multiple `var X` as free variables,
   thus it's possible that there exists two different CONTEXTs, say
   `e1` and `e2`, such that

     e1 <> e2 /\ (e1 (var X) = e2 (var X) = E) /\ WG e1 /\ WG e2

   but none of them are really weakly guarded for all appearences of
   (var X) in E.

   NOTE 3: the "weak guardedness" of Es is always connected with Xs,
   as we don't need to care about those (free) variables in Es that
   are outside of Xs. Even they're not weakly guarded, we don't care,
   as they will be never substituted as an equation variable, instead
   they just function like a nil (with no further transition).  In
   this way, we eliminated the needs of using possibly-wrong
   definition of EV (the set of equation variables), as the same
   variable may appear both free and bounded in different sub-term of
   the same CCS term.

   -- Chun Tian, Aug 10, 2019 (Giardino di via Fermi, Trento, Italy)
*)

(* ========================================================================== *)
(*  Section I: Multivariate Variable Substitution                             *)
(* ========================================================================== *)

(* This is now ‘ssub’ defined in CCSTheory. Original notes by Konrad Slind:

  "There are all kinds of issues with substitutions and applying them
   to term-like structures. I would probably start by choosing finite
   maps (finite_mapTheory) as the representation for variable
   substitutions since they get rid of most if not all the issues
   with ordering of replacements. The alistTheory provides a more
   computationally friendly version, and provides a formal connection
   back to fmaps.

   Also see <holdir>/examples/unification/triangular/first-order
   for a unification case study."
 *)
val _ = TeX_notation {hol = "\\\\", TeX = ("\\ensuremath{\\setminus}", 1)};

Overload CCS_SUBST[local] = “ssub”

Theorem CCS_SUBST_def = ssub_thm
Theorem CCS_SUBST_FEMPTY[local] = ssub_FEMPTY
Theorem CCS_SUBST_SING[local] = FEMPTY_update_apply

(* from a key list and a value list (of same length) to an alist *)
Definition fromList_def :
    fromList (Xs :string list) (Ps :'a CCS list) = FEMPTY |++ ZIP (Xs,Ps)
End

(* new pretty print format: ``[Ps/Xs] E`` (from termTheory) *)
val _ = overload_on ("SUB", ``\Ps Xs. CCS_SUBST (fromList Xs Ps)``);

Theorem CCS_SUBST_sing :
    !X E E'. CCS_SUBST (fromList [X] [E']) E = CCS_Subst E E' X
Proof
    RW_TAC list_ss [fromList_def, ZIP, FUPDATE_LIST_THM]
 >> rw [CCS_SUBST_SING, CCS_Subst]
QED

Theorem fromList_EMPTY :
    fromList [] [] = FEMPTY
Proof
    SRW_TAC [] [fromList_def, FUPDATE_LIST_THM]
QED

Theorem fromList_HD :
    !X Xs P Ps. ~MEM X Xs /\ (LENGTH Ps = LENGTH Xs) ==>
                (fromList (X::Xs) (P::Ps) = (fromList Xs Ps) |+ (X,P))
Proof
    SRW_TAC [] [fromList_def, FUPDATE_LIST_THM]
 >> MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES
 >> METIS_TAC [MAP_ZIP]
QED

Theorem FDOM_fromList :
    !Xs Ps. (LENGTH Ps = LENGTH Xs) ==> (FDOM (fromList Xs Ps) = set Xs)
Proof
    SRW_TAC [] [fromList_def, FDOM_FUPDATE_LIST, MAP_ZIP]
QED

Theorem fromList_DOMSUB_NOT_IN_DOM :
    !X Xs Ps. ~MEM X Xs /\ (LENGTH Ps = LENGTH Xs) ==>
              (fromList Xs Ps) \\ X = fromList Xs Ps
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DOMSUB_NOT_IN_DOM
 >> fs [FDOM_fromList]
QED

Theorem fromList_FAPPLY_HD :
    !X Xs P Ps n. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) ==>
                  ((fromList (X::Xs) (P::Ps)) ' X = P)
Proof
    RW_TAC std_ss [fromList_HD, FAPPLY_FUPDATE]
QED

Theorem fromList_FAPPLY_EL :
    !Xs Ps n. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\ n < LENGTH Xs ==>
              ((fromList Xs Ps) ' (EL n Xs) = EL n Ps)
Proof
    RW_TAC std_ss [fromList_def]
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC `n`
 >> fs [LENGTH_ZIP, MAP_ZIP]
 >> RW_TAC list_ss []
 >> CCONTR_TAC >> fs []
 >> `n < LENGTH Xs /\ m <> n` by RW_TAC arith_ss []
 >> METIS_TAC [ALL_DISTINCT_EL_IMP]
QED

Theorem fromList_FAPPLY_EL' :
    !X P Xs Ps n. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
                  n < LENGTH Xs ==>
                  ((fromList (X::Xs) (P::Ps)) ' (EL n Xs) = EL n Ps)
Proof
    RW_TAC std_ss [fromList_HD, fromList_def]
 >> Know `((FEMPTY |++ ZIP (Xs,Ps)) |+ (X,P)) = ((FEMPTY |+ (X,P)) |++ ZIP (Xs,Ps))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES \\
     fs [MAP_ZIP])
 >> Rewr'
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC `n`
 >> fs [LENGTH_ZIP, MAP_ZIP]
 >> RW_TAC list_ss []
 >> CCONTR_TAC >> fs []
 >> `n < LENGTH Xs /\ m <> n` by RW_TAC arith_ss []
 >> METIS_TAC [ALL_DISTINCT_EL_IMP]
QED

(* slightly more general then CCS_SUBST_elim *)
Theorem CCS_SUBST_elim'[local] = GEN_ALL ssub_14b

(* KEY result: if Xs is disjoint with free variables of E, then E{? / Xs} = E *)
Theorem CCS_SUBST_elim :
    !Xs Ps E. DISJOINT (FV E) (set Xs) /\ (LENGTH Ps = LENGTH Xs) ==>
             (CCS_SUBST (fromList Xs Ps) E = E)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC CCS_SUBST_elim' >> fs [FDOM_fromList]
QED

Theorem lemma0[local] :
    !X P E fm. X NOTIN (FDOM fm) /\ DISJOINT (FDOM fm) (FV P) /\
               FEVERY (\(k,v). X NOTIN (FV v)) fm ==>
              (CCS_SUBST (fm |+ (X,P)) E = CCS_Subst (CCS_SUBST fm E) P X)
Proof
    rw [CCS_Subst]
 (* applying ssub_update_apply_subst *)
 >> Know ‘CCS_SUBST (fm |+ (X,P)) E = [CCS_SUBST fm P/X] (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_update_apply_SUBST' >> fs [FEVERY_DEF])
 >> Rewr'
 >> Suff ‘CCS_SUBST fm P = P’ >- rw []
 >> MATCH_MP_TAC ssub_14b >> rw [DISJOINT_SYM]
QED

(* CCS_SUBST_reduce leads to CCS_SUBST_FOLDR

   NOTE: added ‘DISJOINT (set Xs) (FV P)’ when switching to ‘ssub’
 *)
Theorem CCS_SUBST_reduce :
    !X Xs P Ps. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
                EVERY (\e. X NOTIN (FV e)) Ps /\
                DISJOINT (set Xs) (FV P) ==>
         !E. CCS_SUBST (fromList (X::Xs) (P::Ps)) E =
             CCS_Subst (CCS_SUBST (fromList Xs Ps) E) P X
Proof
    rpt STRIP_TAC
 >> Know `fromList (X::Xs) (P::Ps) = (fromList Xs Ps) |+ (X,P)`
 >- (MATCH_MP_TAC fromList_HD >> art [])
 >> Rewr'
 >> MATCH_MP_TAC lemma0
 >> fs [FDOM_fromList, FEVERY_DEF]
 >> RW_TAC std_ss []
 >> rename1 `MEM Y Xs`
 >> `?n. n < LENGTH Xs /\ (Y = EL n Xs)` by PROVE_TAC [MEM_EL]
 >> fs [fromList_FAPPLY_EL, EVERY_MEM]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw [MEM_EL]
 >> Q.EXISTS_TAC `n` >> art []
QED

(* CCS_SUBST_reduce in another form *)
Theorem lemma1[local] :
   !E E' map.
      map <> [] /\
      ~MEM (FST (HD map)) (MAP FST (TL map)) /\
      ALL_DISTINCT (MAP FST (TL map)) /\
      DISJOINT (set (MAP FST (TL map))) (FV (SND (HD map))) /\
      EVERY (\e. (FST (HD map)) NOTIN (FV e)) (MAP SND (TL map)) /\
      CCS_SUBST (FEMPTY |++ (TL map)) E = E'
   ==>
      CCS_SUBST (FEMPTY |++ map) E = CCS_Subst E' (SND (HD map)) (FST (HD map))
Proof
    rpt GEN_TAC
 >> Cases_on `map` >- SRW_TAC [] []
 >> RW_TAC std_ss [HD, TL]
 >> Cases_on `h` >> fs []
 >> Q.ABBREV_TAC `Xs = FST (UNZIP t)`
 >> Q.ABBREV_TAC `Ps = SND (UNZIP t)`
 >> Know `t = ZIP (Xs,Ps)` >- (unset [`Xs`, `Ps`] >> fs [])
 >> Know `LENGTH Ps = LENGTH Xs` >- (unset [`Xs`, `Ps`] >> fs [])
 >> RW_TAC std_ss []
 >> Know `(MAP FST (ZIP (Xs,Ps))) = Xs` >- PROVE_TAC [MAP_ZIP]
 >> DISCH_THEN (fs o wrap)
 >> Know `(MAP SND (ZIP (Xs,Ps))) = Ps` >- PROVE_TAC [MAP_ZIP]
 >> DISCH_THEN (fs o wrap)
 >> rename1 ‘~MEM X Xs’
 >> MP_TAC (REWRITE_RULE [fromList_def] (Q.SPECL [`X`,`Xs`,`r`,`Ps`] CCS_SUBST_reduce))
 >> simp []
QED

(* Let map = ZIP(Xs,Ps), to convert CCS_SUBST to a folding of CCS_Subst, each P
   of Ps must contains free variables up to the corresponding X of Xs.
 *)
Theorem lemma2[local] :
    !E map. ALL_DISTINCT (MAP FST map) /\
            EVERY (\(x,p). DISJOINT (set (MAP FST map)) (FV p)) map ==>
           (CCS_SUBST (FEMPTY |++ map) E =
            FOLDR (\l e. CCS_Subst e (SND l) (FST l)) E map)
Proof
    GEN_TAC >> Induct_on `map`
 >- SRW_TAC [] [FUPDATE_LIST_THM, CCS_SUBST_FEMPTY]
 >> rpt STRIP_TAC >> fs [MAP]
 >> MP_TAC (Q.SPECL [`E`, `CCS_SUBST (FEMPTY |++ map) E`,
                     `h::map`] lemma1) >> fs []
 >> Know ‘DISJOINT (set (MAP FST map)) (FV (SND h)) /\
          EVERY (\e. FST h # e) (MAP SND map)’
 >- (Cases_on ‘h’ >> fs [] \\
     Q.PAT_X_ASSUM ‘EVERY (\(x,p). DISJOINT (set (MAP FST map)) (FV p) /\ q # p) map’
       MP_TAC >> rw [EVERY_MEM, MEM_MAP] \\
     Q.PAT_X_ASSUM ‘!e. MEM e map ==> _’ (MP_TAC o (Q.SPEC ‘y’)) \\
     Cases_on ‘y’ >> rw [])
 >> rw []
 >> Cases_on `h` >> fs []
 >> rename1 `X # P`
 >> Suff ‘CCS_SUBST (FEMPTY |++ map) E =
          FOLDR (\l e. CCS_Subst e (SND l) (FST l)) E map’ >- rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.PAT_X_ASSUM
     ‘EVERY (\(x,p). DISJOINT (set (MAP FST map)) (FV p) /\ X # p) map’ MP_TAC
 >> rw [EVERY_MEM]
 >> Q.PAT_X_ASSUM ‘!e. MEM e map ==> _’ (MP_TAC o (Q.SPEC ‘e’))
 >> Cases_on ‘e’ >> rw []
QED

(* lemma2 in another form; this is less general than CCS_SUBST_reduce *)
Theorem CCS_SUBST_FOLDR :
    !Xs Ps E. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\
              EVERY (\p. DISJOINT (set Xs) (FV p)) Ps ==>
             (CCS_SUBST (fromList Xs Ps) E =
              FOLDR (\(x,y) e. CCS_Subst e y x) E (ZIP (Xs,Ps)))
Proof
    RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`E`, `ZIP (Xs,Ps)`] lemma2)
 >> RW_TAC std_ss [MAP_ZIP, fromList_def]
 >> Know `(\l e. CCS_Subst e (SND l) (FST l)) = (\(x,y) e. CCS_Subst e y x)`
 >- (rw [FUN_EQ_THM] >> Cases_on `l` >> rw [])
 >> DISCH_THEN (fs o wrap)
 >> POP_ASSUM MATCH_MP_TAC
 >> POP_ASSUM MP_TAC >> rw [EVERY_MEM, MEM_ZIP]
 >> simp []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [MEM_EL]
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

Theorem CCS_SUBST_FOLDR' :
    !Xs Ps E. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\
              EVERY (\p. DISJOINT (set Xs) (FV p)) Ps ==>
             (CCS_SUBST (fromList Xs Ps) E =
              FOLDR (\(x,y) e. CCS_Subst e y x) E (ZIP (Xs,Ps)))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC CCS_SUBST_FOLDR >> art []
 >> fs [FEVERY_DEF, EVERY_MEM]
 >> RW_TAC std_ss [MEM_ZIP]
QED

(* A FOLDL-like version of CCS_SUBST_reduce
Theorem CCS_SUBST_reduce' :
    !E X P Xs Ps. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
                  EVERY (\(x,p). FV p SUBSET {x}) (ZIP (Xs,Ps)) /\
                  DISJOINT (BV E) (set (X::Xs)) ==>
                 (CCS_SUBST (fromList (X::Xs) (P::Ps)) E =
                  CCS_SUBST (fromList Xs Ps) (CCS_Subst E P X))
Proof
    NTAC 3 GEN_TAC
 >> Induct_on `Xs` >> SRW_TAC [][]
QED
 *)

Theorem CCS_SUBST_self :
    !E Xs. ALL_DISTINCT Xs ==> (CCS_SUBST (fromList Xs (MAP var Xs)) E = E)
Proof
    GEN_TAC >> Induct_on `Xs`
 >> SRW_TAC [] [CCS_SUBST_FEMPTY, fromList_EMPTY]
 >> Q.PAT_X_ASSUM `ALL_DISTINCT Xs ==> _` MP_TAC
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`h`, `Xs`, `var h`, `MAP var Xs`] CCS_SUBST_reduce)
 >> `LENGTH (MAP var Xs) = LENGTH Xs` by PROVE_TAC [LENGTH_MAP]
 >> simp []
 >> Suff ‘EVERY (\e. h # e) (MAP var Xs)’
 >- RW_TAC std_ss [EVERY_MEM, MEM_MAP]
 >> rw [EVERY_MAP, EVERY_MEM, FV_thm]
QED

Theorem CCS_SUBST_nested :
    !Xs Ps Es E.
        ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\ (LENGTH Es = LENGTH Xs) ==>
       (CCS_SUBST (fromList Xs Ps) (CCS_SUBST (fromList Xs Es) E) =
        CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Ps)) Es)) E)
Proof
    Suff (* rewriting for induction *)
   `!Xs Ps Es. ALL_DISTINCT Xs /\
              (LENGTH Ps = LENGTH Xs) /\ (LENGTH Es = LENGTH Xs) ==>
        !E. CCS_SUBST (fromList Xs Ps)
                      (CCS_SUBST (fromList Xs Es) E) =
            CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Ps)) Es)) E`
 >- METIS_TAC []
 >> rpt GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> qabbrev_tac ‘fm2 = fromList Xs Ps’
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Es))
                         UNION BIGUNION (IMAGE FV (set Ps))
                         UNION BIGUNION (IMAGE (\e. FV (CCS_SUBST fm2 e)) (set Es))’
 >> rw [Abbr ‘fm2’, FDOM_fromList] (* 5 subgoals *)
 >> TRY (rw [FINITE_FV]) (* 2 subgoals left *)
 >- (fs [MEM_EL] >> rename1 `X = EL n Xs` \\
    `LENGTH (MAP (CCS_SUBST (fromList Xs Ps)) Es) = LENGTH Xs`
       by PROVE_TAC [LENGTH_MAP] \\
     ASM_SIMP_TAC std_ss [fromList_FAPPLY_EL, EL_MAP])
 >> `LENGTH (MAP (CCS_SUBST (fromList Xs Ps)) Es) = LENGTH Xs`
       by PROVE_TAC [LENGTH_MAP]
 (* stage work *)
 >> qabbrev_tac ‘fm1 = fromList Xs Es’
 >> qabbrev_tac ‘fm2 = fromList Xs Ps’
 (* applying ssub_rec *)
 >> Know ‘CCS_SUBST fm1 (rec y E) = rec y (CCS_SUBST fm1 E)’
 >- (MATCH_MP_TAC ssub_rec >> rw [Abbr ‘fm1’, FDOM_fromList] \\
     fs [MEM_EL] >> rename1 `X = EL n Xs` \\
     ASM_SIMP_TAC std_ss [fromList_FAPPLY_EL, EL_MAP] \\
     METIS_TAC [])
 >> Rewr'
 >> Know ‘CCS_SUBST fm2 (rec y (CCS_SUBST fm1 E)) =
          rec y (CCS_SUBST fm2 (CCS_SUBST fm1 E))’
 >- (MATCH_MP_TAC ssub_rec >> rw [Abbr ‘fm2’, FDOM_fromList] \\
     fs [MEM_EL] >> rename1 `X = EL n Xs` \\
     ASM_SIMP_TAC std_ss [fromList_FAPPLY_EL, EL_MAP] \\
     METIS_TAC [])
 >> Rewr'
 >> qabbrev_tac ‘fm3 = fromList Xs (MAP (CCS_SUBST fm2) Es)’
 >> Know ‘CCS_SUBST fm3 (rec y E) = rec y (CCS_SUBST fm3 E)’
 >- (MATCH_MP_TAC ssub_rec >> rw [Abbr ‘fm3’, FDOM_fromList] \\
     FULL_SIMP_TAC std_ss [MEM_EL] >> rename1 `X = EL n Xs` \\
     ASM_SIMP_TAC std_ss [fromList_FAPPLY_EL, EL_MAP] \\
     (* NOTE: this is why we put
          ‘BIGUNION (IMAGE (\e. FV (CCS_SUBST fm2 e)) (set Es))’
        into the exclusive set required by nc_INDUCTION2. *)
     METIS_TAC [])
 >> Rewr'
 >> rw [rec_eq_thm]
QED

(* Now consider a (non-trivial) generalization of FV_SUBSET and BV_SUBSET:

   [FV_SUBSET]  Theorem
      ⊢ !X E E'. FV (CCS_Subst E E' X) SUBSET FV E UNION FV E'

   If, instead of just substituting one (free) variable of E, we
   substitute more of them, can we say that:

   [FV_SUBSET_BIGUNION]
   |- !Xs Ps E. FV (CCS_SUBST (Xs |-> Ps) E) SUBSET
                (FV E) UNION BIGUNION (IMAGE FV (set Ps))`
 *)

(* `ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs)` is not really necessary
   but makes the proof (much) easier.
 *)
Theorem FV_SUBSET_BIGUNION :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) ==>
              FV (CCS_SUBST (fromList Xs Ps) E) SUBSET
                 (FV E) UNION BIGUNION (IMAGE FV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Ps))’
 >> rw [FDOM_fromList, ssub_thm] (* 7 subgoals *)
 >- (fs [MEM_EL, fromList_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] >> ASM_SET_TAC [])
 >> TRY (rw [FINITE_FV] >> ASM_SET_TAC [])
 >> qabbrev_tac ‘fm = fromList Xs Ps’
 >> Know ‘CCS_SUBST fm (rec y E) = rec y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] \\
     METIS_TAC [])
 >> Rewr'
 >> fs [FV_rec]
 >> qabbrev_tac ‘A = CCS_SUBST fm E’
 >> qabbrev_tac ‘B = BIGUNION (IMAGE FV (set Ps))’
 >> Q.PAT_X_ASSUM ‘FV A SUBSET FV E UNION B’ MP_TAC
 >> SET_TAC []
QED

(* A more precise estimation with `set Xs` *)
Theorem FV_SUBSET_BIGUNION' :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) ==>
              FV (CCS_SUBST (fromList Xs Ps) E) SUBSET
                 ((FV E) DIFF (set Xs)) UNION BIGUNION (IMAGE FV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Ps))’
 >> rw [FDOM_fromList, ssub_thm] (* 7 subgoals *)
 >- (fs [MEM_EL, fromList_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] >> ASM_SET_TAC [])
 >> TRY (rw [FINITE_FV] >> ASM_SET_TAC [])
 >> qabbrev_tac ‘fm = fromList Xs Ps’
 >> Know ‘CCS_SUBST fm (rec y E) = rec y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] \\
     METIS_TAC []) >> Rewr'
 >> fs [FV_rec]
 >> qabbrev_tac ‘A = CCS_SUBST fm E’
 >> qabbrev_tac ‘B = BIGUNION (IMAGE FV (set Ps))’
 >> Q.PAT_X_ASSUM ‘FV A SUBSET FV E DIFF set Xs UNION B’ MP_TAC
 >> SET_TAC []
QED

(* KEY result *)
Theorem CCS_SUBST_IS_PROC :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              ALL_PROC Ps /\ FV E SUBSET (set Xs) ==>
              IS_PROC (CCS_SUBST (fromList Xs Ps) E)
Proof
    RW_TAC lset_ss [IS_PROC_def, ALL_PROC_def, EVERY_MEM]
 >> Suff `FV (CCS_SUBST (fromList Xs Ps) E) SUBSET {}` >- SET_TAC []
 >> Know `FV (CCS_SUBST (fromList Xs Ps) E) SUBSET
           ((FV E) DIFF (set Xs)) UNION BIGUNION (IMAGE FV (set Ps))`
 >- PROVE_TAC [FV_SUBSET_BIGUNION']
 >> Know `FV E DIFF (set Xs) = {}` >- ASM_SET_TAC [] >> Rewr'
 >> Know `BIGUNION (IMAGE FV (set Ps)) = {}`
 >- rw [NOT_IN_EMPTY, IN_BIGUNION_IMAGE, IMAGE_EQ_SING] >> Rewr'
 >> REWRITE_TAC [UNION_EMPTY]
QED

(* `DISJOINT (BV P) (set Xs)` is due to the limitation of
   "CCS_SUBST_elim" (or "CCS_SUBST_elim");
   `LENGTH Ps = LENGTH Xs` is due to the limitation of "MAP_ZIP"
 *)
Theorem CCS_SUBST_elim_closed :
    !Xs Ps P. LENGTH Ps = LENGTH Xs /\ IS_PROC P ==>
              CCS_SUBST (fromList Xs Ps) P = P
Proof
    RW_TAC std_ss [IS_PROC_def]
 >> MATCH_MP_TAC CCS_SUBST_elim >> art [DISJOINT_EMPTY]
QED

(* ========================================================================== *)
(*  Section II: Multivariate CCS contexts                                     *)
(* ========================================================================== *)

Definition context_def :
    context Xs E <=> EVERY (\X. CONTEXT (\t. CCS_Subst E t X)) Xs
End

Theorem context_nil :
    !Xs. context Xs nil
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, CCS_Subst_def,
                   DISJOINT_EMPTY, CONTEXT2]
QED

Theorem context_prefix :
    !Xs u E. context Xs (prefix u E) ==> context Xs E
Proof
    RW_TAC std_ss [context_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. prefix u (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC CONTEXT3_backward
QED

Theorem context_prefix_rule :
    !Xs u E. context Xs E ==> context Xs (prefix u E)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. prefix u (e t))`
 >- (MATCH_MP_TAC CONTEXT3 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem context_prefix_rewrite :
    !Xs u E. context Xs (prefix u E) <=> context Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC context_prefix
 >> MATCH_MP_TAC context_prefix_rule >> art []
QED

Theorem context_sum :
    !Xs E1 E2. context Xs (sum E1 E2) ==> context Xs E1 /\ context Xs E2
Proof
    RW_TAC std_ss [context_def, EVERY_MEM] (* 2 subgoals, same tactics *)
 >> ( RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `CONTEXT (\t. e1 t + e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC CONTEXT4_backward )
QED

Theorem context_sum_rule :
    !Xs E1 E2. context Xs E1 /\ context Xs E2 ==> context Xs (sum E1 E2)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, CCS_Subst_def]
 >> TRY (ASM_SET_TAC [])
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `CONTEXT (\t. e1 t) /\ CONTEXT (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. e1 t + e2 t)`
 >- (MATCH_MP_TAC CONTEXT4 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem context_sum_rewrite :
    !Xs E1 E2. context Xs (sum E1 E2) <=>
               context Xs E1 /\ context Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC context_sum >> art [])
 >> MATCH_MP_TAC context_sum_rule >> art []
QED

Theorem context_par :
    !Xs E1 E2. context Xs (par E1 E2) ==> context Xs E1 /\ context Xs E2
Proof
    RW_TAC std_ss [context_def, EVERY_MEM]
 >> ( RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `CONTEXT (\t. e1 t || e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC CONTEXT5_backward )
QED

Theorem context_par_rule :
    !Xs E1 E2. context Xs E1 /\ context Xs E2 ==> context Xs (par E1 E2)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, CCS_Subst_def]
 >> TRY (ASM_SET_TAC [])
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `CONTEXT (\t. e1 t) /\ CONTEXT (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. e1 t || e2 t)`
 >- (MATCH_MP_TAC CONTEXT5 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem context_par_rewrite :
    !Xs E1 E2. context Xs (par E1 E2) <=>
               context Xs E1 /\ context Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC context_par >> art [])
 >> MATCH_MP_TAC context_par_rule >> art []
QED

Theorem context_restr :
    !Xs L E. context Xs (restr L E) ==> context Xs E
Proof
    RW_TAC std_ss [context_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. restr L (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC CONTEXT6_backward
QED

Theorem context_restr_rule :
    !Xs L E. context Xs E ==> context Xs (restr L E)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. restr L (e t))`
 >- (MATCH_MP_TAC CONTEXT6 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem context_restr_rewrite :
    !Xs L E. context Xs (restr L E) <=> context Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC context_restr
 >> MATCH_MP_TAC context_restr_rule >> art []
QED

Theorem context_relab :
    !Xs E rf. context Xs (relab E rf) ==> context Xs E
Proof
    RW_TAC std_ss [context_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. relab (e t) rf)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC CONTEXT7_backward
QED

Theorem context_relab_rule :
    !Xs E rf. context Xs E ==> context Xs (relab E rf)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. relab (e t) rf)`
 >- (MATCH_MP_TAC CONTEXT7 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem context_relab_rewrite :
    !Xs E rf. context Xs (relab E rf) <=> context Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC context_relab
 >> MATCH_MP_TAC context_relab_rule >> art []
QED

Theorem context_var :
    !Xs Y. context Xs (var Y)
Proof
    RW_TAC lset_ss [context_def, EVERY_MEM, CCS_Subst_def]
 >> Cases_on `Y = X` >> fs [CONTEXT_rules]
QED

Theorem context_rec :
    !Xs Y E. context Xs (rec Y E) ==> DISJOINT (FV E DELETE Y) (set Xs)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> fs [context_def, EVERY_MEM]
 >> CCONTR_TAC >> fs [IN_DISJOINT]
 >> rename1 ‘X <> Y’
 >> `Y <> X` by PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘!X. MEM X Xs ==> P’ (MP_TAC o (Q.SPEC ‘X’))
 >> RW_TAC std_ss []
 >> rw [Once CONTEXT_cases, FUN_EQ_THM]
 (* 7 subgoals *)
 >- (Q.EXISTS_TAC ‘var X’ >> rw [])
 >- (CCONTR_TAC >> fs [] \\
     Know ‘X # rec Y E’
     >- (MATCH_MP_TAC CCS_Subst_EQ_IMP_NOTIN_FV >> rw []) \\
     rw [FV_thm])
 >> DISJ1_TAC >> Q.EXISTS_TAC ‘var X’ >> rw []
QED

(* a collection of all (forward) rules of `context` *)
val context_rules = save_thm
  ("context_rules",
    LIST_CONJ [context_nil, context_var, context_prefix_rule,
               context_sum_rule, context_par_rule,
               context_restr_rule, context_relab_rule]);

(* a collection of all backward rules of `context` *)
val context_backward_rules = save_thm
  ("context_backward_rules",
    LIST_CONJ [context_prefix, context_sum, context_par,
               context_restr, context_relab, context_rec]);

(* c.f. STRONG_EQUIV_SUBST_CONTEXT *)
Theorem STRONG_EQUIV_subst_context :
    !Xs Ps Qs. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
               LIST_REL STRONG_EQUIV Ps Qs ==>
        !E. context Xs E ==>
            STRONG_EQUIV (CCS_SUBST (fromList Xs Ps) E)
                         (CCS_SUBST (fromList Xs Qs) E)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION (BIGUNION (IMAGE FV (set Ps)))
                         UNION (BIGUNION (IMAGE FV (set Qs)))’
 >> rw [ssub_thm, STRONG_EQUIV_REFL] >> rw [FINITE_FV]
 (* 9 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL])
 (* 8 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 7 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 6 subgoals left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_prefix)
 (* 5 subgoals left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM \\
     IMP_RES_TAC context_sum \\
     RES_TAC >> art [])
 (* 4 subgoals left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
     IMP_RES_TAC context_par \\
     RES_TAC >> art [])
 (* 3 subgoals left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_restr)
 (* 2 subgoals left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_relab)
 (* 1 subgoal left *)
 >> IMP_RES_TAC context_rec
 >> `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH]
 (* applying ssub_rec *)
 >> qabbrev_tac ‘fm = fromList Xs Ps’
 >> Know ‘CCS_SUBST fm (rec y E) = rec y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> qabbrev_tac ‘fm' = fromList Xs Qs’
 >> Know ‘CCS_SUBST fm' (rec y E) = rec y (CCS_SUBST fm' E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm'’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> qunabbrevl_tac [‘fm’, ‘fm'’]
 >> Know `CCS_SUBST (fromList Xs Ps) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> Rewr'
 >> Know `CCS_SUBST (fromList Xs Qs) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> Rewr'
 >> REWRITE_TAC [STRONG_EQUIV_REFL]
QED

(* c.f. OBS_CONGR_SUBST_CONTEXT *)
Theorem OBS_CONGR_subst_context :
    !Xs Ps Qs. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
               LIST_REL OBS_CONGR Ps Qs ==>
        !E. context Xs E ==>
            OBS_CONGR (CCS_SUBST (fromList Xs Ps) E)
                      (CCS_SUBST (fromList Xs Qs) E)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION (BIGUNION (IMAGE FV (set Ps)))
                         UNION (BIGUNION (IMAGE FV (set Qs)))’
 >> rw [ssub_thm, OBS_CONGR_REFL] >> rw [FINITE_FV]
 (* 9 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL])
 (* 8 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 7 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 6 subgoals left *)
 >- (MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_prefix)
 (* 5 subgoals left *)
 >- (MATCH_MP_TAC OBS_CONGR_PRESD_BY_SUM \\
     IMP_RES_TAC context_sum \\
     RES_TAC >> art [])
 (* 4 subgoals left *)
 >- (MATCH_MP_TAC OBS_CONGR_PRESD_BY_PAR \\
     IMP_RES_TAC context_par \\
     RES_TAC >> art [])
 (* 3 subgoals left *)
 >- (MATCH_MP_TAC OBS_CONGR_SUBST_RESTR \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_restr)
 (* 2 subgoals left *)
 >- (MATCH_MP_TAC OBS_CONGR_SUBST_RELAB \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_relab)
 (* 1 subgoal left *)
 >> IMP_RES_TAC context_rec
 >> `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH]
 (* applying ssub_rec *)
 >> qabbrev_tac ‘fm = fromList Xs Ps’
 >> Know ‘CCS_SUBST fm (rec y E) = rec y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> qabbrev_tac ‘fm' = fromList Xs Qs’
 >> Know ‘CCS_SUBST fm' (rec y E) = rec y (CCS_SUBST fm' E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm'’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> qunabbrevl_tac [‘fm’, ‘fm'’]
 >> Know `CCS_SUBST (fromList Xs Ps) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> Rewr'
 >> Know `CCS_SUBST (fromList Xs Qs) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> Rewr'
 >> REWRITE_TAC [OBS_CONGR_REFL]
QED

(* c.f. OBS_contracts_SUBST_CONTEXT *)
Theorem OBS_contracts_subst_context :
    !Xs Ps Qs. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
               LIST_REL OBS_contracts Ps Qs ==>
        !E. context Xs E ==>
            OBS_contracts (CCS_SUBST (fromList Xs Ps) E)
                          (CCS_SUBST (fromList Xs Qs) E)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION (BIGUNION (IMAGE FV (set Ps)))
                         UNION (BIGUNION (IMAGE FV (set Qs)))’
 >> rw [ssub_thm, OBS_contracts_REFL] >> rw [FINITE_FV]
 (* 9 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL])
 (* 8 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 7 subgoals left *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 6 subgoals left *)
 >- (MATCH_MP_TAC OBS_contracts_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_prefix)
 (* 5 subgoals left *)
 >- (MATCH_MP_TAC OBS_contracts_PRESD_BY_SUM \\
     IMP_RES_TAC context_sum \\
     RES_TAC >> art [])
 (* 4 subgoals left *)
 >- (MATCH_MP_TAC OBS_contracts_PRESD_BY_PAR \\
     IMP_RES_TAC context_par \\
     RES_TAC >> art [])
 (* 3 subgoals left *)
 >- (MATCH_MP_TAC OBS_contracts_SUBST_RESTR \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_restr)
 (* 2 subgoals left *)
 >- (MATCH_MP_TAC OBS_contracts_SUBST_RELAB \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_relab)
 (* 1 subgoal left *)
 >> IMP_RES_TAC context_rec
 >> `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH]
 (* applying ssub_rec *)
 >> qabbrev_tac ‘fm = fromList Xs Ps’
 >> Know ‘CCS_SUBST fm (rec y E) = rec y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> qabbrev_tac ‘fm' = fromList Xs Qs’
 >> Know ‘CCS_SUBST fm' (rec y E) = rec y (CCS_SUBST fm' E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm'’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> qunabbrevl_tac [‘fm’, ‘fm'’]
 >> Know `CCS_SUBST (fromList Xs Ps) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> Rewr'
 >> Know `CCS_SUBST (fromList Xs Qs) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> Rewr'
 >> REWRITE_TAC [OBS_contracts_REFL]
QED

(* KEY result: multivariate version of CongruenceTheory.CONTEXT_combin *)
Theorem context_combin :
    !Xs Es C. ALL_DISTINCT Xs /\ context Xs C /\
              EVERY (context Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
              context Xs (CCS_SUBST (fromList Xs Es) C)
Proof
    Suff `!Xs. ALL_DISTINCT Xs ==>
               !Es C. context Xs C ==>
                      EVERY (context Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
                      context Xs (CCS_SUBST (fromList Xs Es) C)` >- METIS_TAC []
 >> NTAC 3 STRIP_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION (BIGUNION (IMAGE FV (set Es)))’
 >> rw [ssub_thm] >> rw [FINITE_FV]
 (* 7 subgoals left *)
 >- (fs [FDOM_fromList, EVERY_MEM, MEM_EL] \\
     fs [fromList_FAPPLY_EL] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> art [])
 (* 6 subgoals left *)
 >- (rename1 ‘context Xs (u..[Es/Xs] C0)’ \\
     Q.PAT_X_ASSUM `context Xs C0 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     IMP_RES_TAC context_prefix >> RES_TAC \\
     MATCH_MP_TAC context_prefix_rule >> art [])
 (* 5 subgoals *)
 >- (IMP_RES_TAC context_sum \\
     rename1 ‘context Xs ([Es/Xs] C1 + [Es/Xs] C2)’ \\
     Q.PAT_X_ASSUM `context Xs C1 ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C2 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_sum_rule >> art [])
 (* 4 subgoals *)
 >- (IMP_RES_TAC context_par \\
     rename1 ‘context Xs ([Es/Xs] C1 || [Es/Xs] C2)’ \\
     Q.PAT_X_ASSUM `context Xs C1 ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C2 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_par_rule >> art [])
 (* 3 subgoals *)
 >- (IMP_RES_TAC context_restr \\
     rename1 ‘context Xs (restr L ([Es/Xs] C0))’ \\
     Q.PAT_X_ASSUM `context Xs C0 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_restr_rule >> art [])
 (* 2 subgoals *)
 >- (IMP_RES_TAC context_relab \\
     rename1 ‘context Xs (relab ([Es/Xs] C0) rf)’ \\
     Q.PAT_X_ASSUM `context Xs C0 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_relab_rule >> art [])
 (* 1 subgoal *)
 >> rename1 ‘context Xs (rec Y E)’
 >> IMP_RES_TAC context_rec
 (* applying ssub_rec *)
 >> qabbrev_tac ‘fm = fromList Xs Es’
 >> Know ‘CCS_SUBST fm (rec Y E) = rec Y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> gs [Abbr ‘fm’]
 >> Suff `CCS_SUBST (fromList Xs Es) E = E` >- rw []
 >> MATCH_MP_TAC CCS_SUBST_elim'
 >> fs [FDOM_fromList] >> ASM_SET_TAC []
QED

Theorem LIST_REL_equivalence : (* unused *)
    !R. equivalence R ==> equivalence (LIST_REL R)
Proof
    RW_TAC list_ss [equivalence_def, reflexive_def, symmetric_def,
                    transitive_def, LIST_REL_EL_EQN]
 >- (EQ_TAC >> RW_TAC std_ss [])
 >> Q.PAT_X_ASSUM `!x y z. R x y /\ R y z ==> R x z` MATCH_MP_TAC
 >> Q.EXISTS_TAC `EL n y`
 >> CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* ========================================================================== *)
(*  Section III: Weakly guarded equations                                     *)
(* ========================================================================== *)

(* A list of variables Xs are weakly guarded in E iff:

   1. Xs is DISJOINT with the set of all bound variables (BV) used by
      recursion operators in E;
   2. For each X in Xs, if all subterms (var X) were replaced by holes,
      the resulting multi-hole context (\t. CCS_Subst E t X) is a WG.
 *)
Definition weakly_guarded_def :
    weakly_guarded Xs E <=> EVERY (\X. WG (\t. CCS_Subst E t X)) Xs
End

val _ = overload_on ("weakly_guarded",
                    ``\Xs Es. EVERY (weakly_guarded Xs) Es``);

Theorem weakly_guarded_imp_context :
    !Xs E. weakly_guarded Xs E ==> context Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, context_def, EVERY_MEM]
 >> MATCH_MP_TAC WG_IMP_CONTEXT
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem EVERY_weakly_guarded :
    !Xs Es. EVERY (weakly_guarded Xs) Es ==>
            !E X. MEM E Es /\ MEM X Xs ==> WG (\t. CCS_Subst E t X)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
QED

Theorem weakly_guarded_nil :
    !Xs. weakly_guarded Xs nil
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, CCS_Subst_def,
                   DISJOINT_EMPTY, WG2]
QED

Theorem weakly_guarded_prefix :
    !Xs u E. weakly_guarded Xs (prefix u E) ==> context Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, context_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. prefix u (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC WG3_backward
QED

Theorem weakly_guarded_prefix_rule :
    !Xs u E. context Xs E ==> weakly_guarded Xs (prefix u E)
Proof
    RW_TAC std_ss [weakly_guarded_def, context_def, EVERY_MEM]
 >> RES_TAC >> rw [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. prefix u (CCS_Subst E t X)) = WG (\t. prefix u (e t))`
 >- (Q.UNABBREV_TAC `e` >> rw []) >> Rewr'
 >> MATCH_MP_TAC WG3 >> art []
QED

Theorem weakly_guarded_sum :
    !Xs E1 E2. weakly_guarded Xs (sum E1 E2) ==>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
 >> ( RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `WG (\t. e1 t + e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC WG4_backward )
QED

Theorem weakly_guarded_sum_rule :
    !Xs E1 E2. weakly_guarded Xs E1 /\ weakly_guarded Xs E2 ==>
               weakly_guarded Xs (sum E1 E2)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, CCS_Subst_def]
 >> TRY (ASM_SET_TAC [])
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `WG (\t. e1 t) /\ WG (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. e1 t + e2 t)`
 >- (MATCH_MP_TAC WG4 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_sum_rewrite :
    !Xs E1 E2. weakly_guarded Xs (sum E1 E2) <=>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC weakly_guarded_sum >> art [])
 >> MATCH_MP_TAC weakly_guarded_sum_rule >> art []
QED

Theorem weakly_guarded_par :
    !Xs E1 E2. weakly_guarded Xs (par E1 E2) ==>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
 >> ( RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `WG (\t. e1 t || e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC WG5_backward )
QED

Theorem weakly_guarded_par_rule :
    !Xs E1 E2. weakly_guarded Xs E1 /\ weakly_guarded Xs E2 ==>
               weakly_guarded Xs (par E1 E2)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, CCS_Subst_def]
 >> TRY (ASM_SET_TAC [])
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `WG (\t. e1 t) /\ WG (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. e1 t || e2 t)`
 >- (MATCH_MP_TAC WG5 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_par_rewrite :
    !Xs E1 E2. weakly_guarded Xs (par E1 E2) <=>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC weakly_guarded_par >> art [])
 >> MATCH_MP_TAC weakly_guarded_par_rule >> art []
QED

Theorem weakly_guarded_restr :
    !Xs L E. weakly_guarded Xs (restr L E) ==> weakly_guarded Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. restr L (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC WG6_backward
QED

Theorem weakly_guarded_restr_rule :
    !Xs L E. weakly_guarded Xs E ==> weakly_guarded Xs (restr L E)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. restr L (e t))`
 >- (MATCH_MP_TAC WG6 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_restr_rewrite :
    !Xs L E. weakly_guarded Xs (restr L E) <=> weakly_guarded Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC weakly_guarded_restr
 >> MATCH_MP_TAC weakly_guarded_restr_rule >> art []
QED

Theorem weakly_guarded_relab :
    !Xs E rf. weakly_guarded Xs (relab E rf) ==> weakly_guarded Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. relab (e t) rf)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC WG7_backward
QED

Theorem weakly_guarded_relab_rule :
    !Xs E rf. weakly_guarded Xs E ==> weakly_guarded Xs (relab E rf)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. relab (e t) rf)`
 >- (MATCH_MP_TAC WG7 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_relab_rewrite :
    !Xs E rf. weakly_guarded Xs (relab E rf) <=> weakly_guarded Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC weakly_guarded_relab
 >> MATCH_MP_TAC weakly_guarded_relab_rule >> art []
QED

Theorem weakly_guarded_var :
    !Xs Y. weakly_guarded Xs (var Y) ==> ~MEM Y Xs
Proof
    rpt GEN_TAC
 >> Suff `MEM Y Xs ==> ~weakly_guarded Xs (var Y)` >- METIS_TAC []
 >> DISCH_TAC >> CCONTR_TAC
 >> fs [weakly_guarded_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def, NO_WG0]
QED

Theorem weakly_guarded_var_rule :
    !Xs Y. ~MEM Y Xs ==> weakly_guarded Xs (var Y)
Proof
    RW_TAC lset_ss [weakly_guarded_def, EVERY_MEM, CCS_Subst_def]
 >> Cases_on `Y = X` >> fs [WG_rules]
QED

Theorem weakly_guarded_rec :
    !Xs Y E. weakly_guarded Xs (rec Y E) ==> DISJOINT (FV E DELETE Y) (set Xs)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC context_rec
 >> MATCH_MP_TAC weakly_guarded_imp_context >> art []
QED

(* a collection of all (forward) rules of `weakly_guarded` *)
val weakly_guarded_rules = save_thm
  ("weakly_guarded_rules",
    LIST_CONJ [weakly_guarded_nil,
               weakly_guarded_var_rule,
               weakly_guarded_prefix_rule,
               weakly_guarded_sum_rule,
               weakly_guarded_par_rule,
               weakly_guarded_restr_rule,
               weakly_guarded_relab_rule]);

(* a collection of all backward rules of `weakly_guarded` *)
val weakly_guarded_backward_rules = save_thm
  ("weakly_guarded_backward_rules",
    LIST_CONJ [weakly_guarded_var,
               weakly_guarded_prefix,
               weakly_guarded_sum,
               weakly_guarded_par,
               weakly_guarded_restr,
               weakly_guarded_relab,
               weakly_guarded_rec]);

Theorem disjoint_imp_weakly_guarded :
    !Xs E. DISJOINT (FV E) (set Xs) ==> weakly_guarded Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
 >> MATCH_MP_TAC WG_CONST
 >> RW_TAC std_ss [IS_CONST_def]
 >> `X NOTIN (FV E)` by ASM_SET_TAC []
 >> fs [CCS_Subst_elim]
QED

Theorem disjoint_imp_context :
    !Xs E. DISJOINT (FV E) (set Xs) ==> context Xs E
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC weakly_guarded_imp_context
 >> MATCH_MP_TAC disjoint_imp_weakly_guarded >> art []
QED

(* c.f. CONTEXT_WG_combin *)
Theorem weakly_guarded_combin :
    !Xs Es C. ALL_DISTINCT Xs /\ context Xs C /\
              EVERY (weakly_guarded Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
              weakly_guarded Xs (CCS_SUBST (fromList Xs Es) C)
Proof
    Suff `!Xs. ALL_DISTINCT Xs ==>
               !Es C. context Xs C ==>
                      EVERY (weakly_guarded Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
                      weakly_guarded Xs (CCS_SUBST (fromList Xs Es) C)`
 >- METIS_TAC []
 >> NTAC 3 STRIP_TAC (* up to `!C.` *)
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION (BIGUNION (IMAGE FV (set Es)))’
 >> rw [ssub_thm] >> rw [FINITE_FV]
 (* 9 subgoals *)
 >- (fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL] \\
     fs [EVERY_EL])
 (* 8 subgoals *)
 >- (fs [FDOM_fromList] \\
     MATCH_MP_TAC weakly_guarded_var_rule >> art [])
 (* 7 subgoals *)
 >- (rw [weakly_guarded_nil])
 (* 6 subgoals *)
 >- (IMP_RES_TAC context_prefix \\
     rename1 ‘weakly_guarded Xs (u..[Es/Xs] C0)’ \\
     Q.PAT_X_ASSUM `context Xs C0 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_prefix_rule \\
     MATCH_MP_TAC weakly_guarded_imp_context >> art [])
 (* 5 subgoals *)
 >- (IMP_RES_TAC context_sum \\
     rename1 ‘weakly_guarded Xs ([Es/Xs] C1 + [Es/Xs] C2)’ \\
     Q.PAT_X_ASSUM `context Xs C1 ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C2 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_sum_rule >> art [])
 (* 4 subgoals *)
 >- (IMP_RES_TAC context_par \\
     rename1 ‘weakly_guarded Xs ([Es/Xs] C1 || [Es/Xs] C2)’ \\
     Q.PAT_X_ASSUM `context Xs C1 ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C2 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_par_rule >> art [])
 (* 3 subgoals *)
 >- (IMP_RES_TAC context_restr \\
     rename1 ‘weakly_guarded Xs (restr L ([Es/Xs] C0))’ \\
     Q.PAT_X_ASSUM `context Xs C0 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_restr_rule >> art [])
 (* 2 subgoals *)
 >- (IMP_RES_TAC context_relab \\
     rename1 ‘weakly_guarded Xs (relab ([Es/Xs] C0) rf)’ \\
     Q.PAT_X_ASSUM `context Xs C0 ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_relab_rule >> art [])
 (* 1 subgoal *)
 >> rename1 ‘context Xs (rec Y E)’
 >> IMP_RES_TAC context_rec
 (* applying ssub_rec *)
 >> qabbrev_tac ‘fm = fromList Xs Es’
 >> Know ‘CCS_SUBST fm (rec Y E) = rec Y (CCS_SUBST fm E)’
 >- (MATCH_MP_TAC ssub_rec \\
     rw [Abbr ‘fm’, FDOM_fromList] \\
     fs [MEM_EL, fromList_FAPPLY_EL] >> METIS_TAC [])
 >> Rewr'
 >> gs [Abbr ‘fm’]
 >> Know `CCS_SUBST (fromList Xs Es) E = E`
 >- (MATCH_MP_TAC CCS_SUBST_elim' \\
     fs [FDOM_fromList] >> ASM_SET_TAC [])
 >> DISCH_THEN (fs o wrap)
 >> MATCH_MP_TAC disjoint_imp_weakly_guarded
 >> rw [FV_thm]
QED

(* ========================================================================== *)
(*  Section IV: Unique Solution of Equations                                  *)
(* ========================================================================== *)

(* NOTE: each E in Es MUST contain free variables up to Xs *)
Definition CCS_equation_def :
    CCS_equation (Xs :string list) (Es :'a CCS list) <=>
        ALL_DISTINCT Xs /\ LENGTH Es = LENGTH Xs /\
        EVERY (\e. (FV e) SUBSET (set Xs)) Es
End

(* A solution Ps of the CCS equation (group) Es[Xs] up to R,
  `ALL_PROC Ps` is required in (all) unique-solution proofs.
 *)
Definition CCS_solution_def :
    CCS_solution R Xs Es Ps <=>
        ALL_PROC Ps /\
        LIST_REL R Ps (MAP (CCS_SUBST (fromList Xs Ps)) Es)
End

(* Each solution contains the same number of CCS processes as the
   variables - this is derived from LIST_REL's properties *)
Theorem CCS_solution_length :
    !Xs Es R Ps. CCS_equation Xs Es /\ CCS_solution R Xs Es Ps ==>
                 (LENGTH Ps = LENGTH Xs)
Proof
    RW_TAC list_ss [CCS_equation_def, CCS_solution_def]
 >> IMP_RES_TAC LIST_REL_LENGTH
 >> fs [LENGTH_MAP]
QED

(* Lemma 4.13 of [1] (the full version):

  "If the variable X is weakly guarded in E, and E{Ps/Xs} --u-> P',
   then P' takes the form E'{Ps/Xs} (for some context E'), and
   moreover, for any Qs, E{Qs/Xs} --u-> E'{Qs/Xs}."

   This lemma is used in proving both "strong_unique_solution"
   and "unique_solution_of_rooted_contractions" theorems.

   NOTE1: `ALL_PROC Ps` is not required here.
   NOTE2: `FV E SUBSET (set Xs)` and `FV E' SUBSET (set Xs)` were added
 *)
Theorem strong_unique_solution_lemma :
    !Xs E. weakly_guarded Xs E /\ FV E SUBSET (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==>
                !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
                       ?E'. context Xs E' /\
                            FV E' SUBSET (set Xs) /\
                           (P' = CCS_SUBST (fromList Xs Ps) E') /\
                            !Qs. (LENGTH Qs = LENGTH Xs) ==>
                                 TRANS (CCS_SUBST (fromList Xs Qs) E) u
                                       (CCS_SUBST (fromList Xs Qs) E')
Proof
    Q.X_GEN_TAC `Xs`
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs’ >> rw [FDOM_fromList] (* 8 subgoals *)
 (* Case 0: E = var s, impossible *)
 >- (rename1 `weakly_guarded Xs (var Y)` \\
     IMP_RES_TAC weakly_guarded_var)
 (* Case 1: E = nil, still impossible *)
 >- (fs [NIL_NO_TRANS])
 (* Case 2: E = b.E' *)
 >- (rename1 `weakly_guarded Xs (prefix b E)` \\
     fs [CCS_SUBST_def, TRANS_PREFIX_EQ] \\
     Q.EXISTS_TAC `E` >> art [] \\
     IMP_RES_TAC weakly_guarded_prefix)
 (* Case 3: E = E1 + E2 *)
 >- (IMP_RES_TAC weakly_guarded_sum \\
     fs [CCS_SUBST_def, TRANS_SUM_EQ] \\ (* 2 subgoals, same tactics *)
     RES_TAC >> Q.EXISTS_TAC `E''` >> fs [])
 (* Case 4: E = E1 || E2 *)
 >- (rename1 `weakly_guarded Xs (E1 || E2)` \\
     IMP_RES_TAC weakly_guarded_par \\
     fs [CCS_SUBST_def, TRANS_PAR_EQ, FV_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         K_TAC >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E1'`])) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `E' || E2` \\
       CONJ_TAC (* context Xs (E' || E2) *)
       >- (MATCH_MP_TAC context_par_rule >> art [] \\
           MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       CONJ_TAC >- ASM_SET_TAC [FV_def] \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E'` >> REWRITE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         K_TAC \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E1'`])) >> RW_TAC std_ss [] \\
       rename1 `context Xs E''` \\ (* fixes for stdknl *)
       Q.EXISTS_TAC `E1 || E''` \\
       CONJ_TAC (* context Xs (E1 || E'') *)
       >- (MATCH_MP_TAC context_par_rule >> art [] \\
           MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       CONJ_TAC >- ASM_SET_TAC [FV_def] \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ2_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E''` >> REWRITE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`label l`, `E1'`])) \\
       RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`label (COMPL l)`, `E2'`])) \\
       RW_TAC std_ss [] \\
       Q.EXISTS_TAC `E' || E''` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art []) \\
       CONJ_TAC >- ASM_SET_TAC [FV_def] \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
       GEN_TAC >> DISCH_TAC >> NTAC 2 DISJ2_TAC \\
       take [`CCS_SUBST (fromList Xs Qs) E'`,
             `CCS_SUBST (fromList Xs Qs) E''`, `l`] >> fs [] ])
 (* Case 5: E = restr f E' *)
 >- (IMP_RES_TAC weakly_guarded_restr \\
     fs [CCS_SUBST_def, TRANS_RESTR_EQ, FV_def] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!Ps. (LENGTH Ps = LENGTH Xs) ==> _` (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`tau`, `E''`])) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `restr L E'` \\
       rfs [CCS_SUBST_def, FV_def] \\
       MATCH_MP_TAC context_restr_rule >> art [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!Ps. (LENGTH Ps = LENGTH Xs) ==> _` (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`label l`, `E''`])) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `restr L E'` \\
       rfs [CCS_SUBST_def, FV_def] \\
       MATCH_MP_TAC context_restr_rule >> art [] ])
 (* Case 6: E = relab E' R *)
 >- (IMP_RES_TAC weakly_guarded_relab \\
     Q.PAT_X_ASSUM `weakly_guarded Xs E /\ _ ==> _` MP_TAC \\
     fs [FV_def] >> rpt STRIP_TAC \\
     POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
     fs [CCS_SUBST_def, TRANS_RELAB_EQ] \\
     POP_ASSUM (MP_TAC o (Q.SPECL [`u'`, `E''`])) >> RW_TAC std_ss [] \\
     Q.EXISTS_TAC `relab E' rf` \\
     CONJ_TAC >- (MATCH_MP_TAC context_relab_rule >> art []) \\
     ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
     GEN_TAC >> DISCH_TAC \\
     take [`u'`, `CCS_SUBST (fromList Xs Qs) E'`] >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* Case 7 (difficult): E = rec Y E' *)
 >> IMP_RES_TAC weakly_guarded_rec
 >> `DISJOINT (FV (rec y E)) (set Xs)` by ASM_SET_TAC [FV_def]
 (* simplify `CCS_Subst (rec y E) (Ps |-> Qs)` *)
 >> Know `CCS_SUBST (fromList Xs Ps) (rec y E) = rec y E`
 >- (MATCH_MP_TAC CCS_SUBST_elim >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 (* KEY step: let E' = P' *)
 >> Q.EXISTS_TAC `P'`
 >> Know `DISJOINT (FV P') (set Xs)`
 >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC `FV (rec y E)` >> art [] \\
     MATCH_MP_TAC TRANS_FV \\
     Q.EXISTS_TAC `u` >> art []) >> DISCH_TAC
 >> CONJ_TAC (* context Xs P' *)
 >- (RW_TAC std_ss [context_def, EVERY_MEM] \\
     Suff `!t. CCS_Subst P' t X = P'`
     >- (Rewr' >> REWRITE_TAC [CONTEXT2]) \\
     MATCH_MP_TAC CCS_Subst_elim >> ASM_SET_TAC [])
 >> CONJ_TAC (* FV P' SUBSET set Xs *)
 >- (`FV P' SUBSET FV (rec y E)` by PROVE_TAC [TRANS_FV] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `FV (rec y E)` >> rw []) (* Yeah! *)
 >> CONJ_TAC (* P' = CCS_SUBST (Xs |-> Ps) P' *)
 >- (MATCH_MP_TAC EQ_SYM >> irule CCS_SUBST_elim >> art [])
 >> rpt STRIP_TAC
 >> Know `CCS_SUBST (fromList Xs Qs) (rec y E) = rec y E`
 >- (irule CCS_SUBST_elim >> art []) >> Rewr'
 >> Know `CCS_SUBST (fromList Xs Qs) P' = P'`
 >- (irule CCS_SUBST_elim >> art []) >> Rewr' >> art []
QED

(* THE STAGE THEOREM (Proposition 4.14 of [1, p.103])

   Let the expression Es contain at most Xs, and let Xs be weakly guarded in Es,
   then:
        If Ps ~ E{Ps/Xs} and Qs ~ E{Qs/Xs} then Ps ~ Qs.
 *)
Theorem strong_unique_solution_thm :
    !Xs Es Ps Qs.
        CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
        Ps IN (CCS_solution STRONG_EQUIV Xs Es) /\
        Qs IN (CCS_solution STRONG_EQUIV Xs Es) ==> STRONG_EQUIV Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_equation_def, CCS_solution_def, LIST_REL_EL_EQN]
 >> Q.ABBREV_TAC `P = EL n Ps`
 >> Q.ABBREV_TAC `Q = EL n Qs`
 >> irule (REWRITE_RULE [RSUBSET] STRONG_BISIM_UPTO_THM)
 (*
    `FV G SUBSET (set Xs)` is necessary for the case of `par`;

    `IS_PROC x` is for the same case: they guarantee that
    `CCS_SUBST (Xs |-> Ps) x = x`. (This is not needed
     when "CCS equations" are formalized as another type, e.g. in case
     of STRONG_UNIQUE_SOLUTION where univariate equations are lambda-
     functions of type 'a CCS -> 'a CCS.)
  *)
 >> Q.EXISTS_TAC `\x y. IS_PROC x /\ IS_PROC y /\
                        ((x = y) \/
                         (?G. context Xs G /\ (FV G) SUBSET (set Xs) /\
                              (x = CCS_SUBST (fromList Xs Ps) G) /\
                              (y = CCS_SUBST (fromList Xs Qs) G)))`
 >> BETA_TAC >> reverse CONJ_TAC
 >- (`IS_PROC P /\ IS_PROC Q` by METIS_TAC [IS_PROC_EL] >> simp [] \\
     DISJ2_TAC >> Q.EXISTS_TAC `var (EL n Xs)` \\
     unset [`P`, `Q`] \\
     SRW_TAC [] [CCS_SUBST_def, FV_def, MEM_EL, FDOM_fromList] (* 6 subgoals *)
     >- REWRITE_TAC [context_var]
     >- (Q.EXISTS_TAC `n` >> art [])
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >- METIS_TAC []
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >> METIS_TAC [])
 >> REWRITE_TAC [STRONG_BISIM_UPTO]
 >> fix [`P'`, `Q'`]
 >> BETA_TAC >> STRIP_TAC (* 2 subgoals here *)
 >- (POP_ASSUM MP_TAC >> RW_TAC std_ss [] >| (* 2 subgoals here *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `E1` >> art [O_DEF] \\
       Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
       BETA_TAC >> fs [] \\
       MATCH_MP_TAC TRANS_PROC >> take [`P'`, `u`] >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `E2` >> art [O_DEF] \\
       Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
       BETA_TAC >> fs [] \\
       MATCH_MP_TAC TRANS_PROC >> take [`P'`, `u`] >> art [] ])
 (* move up `P'` and `Q'` *)
 >> Q.PAT_X_ASSUM `IS_PROC Q'` MP_TAC
 >> Q.PAT_X_ASSUM `IS_PROC P'` MP_TAC
 >> NTAC 2 POP_ORW (* P' = ... /\ Q' = ... *)
 (* move up all about G *)
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.ID_SPEC_TAC ‘G’
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Es))
                         UNION BIGUNION (IMAGE FV (set Ps))
                         UNION BIGUNION (IMAGE FV (set Qs))’
 >> rw [] >> fs [FDOM_fromList, FINITE_FV, NIL_NO_TRANS]
 (* 14 subgoals left *)
 >- (rename1 ‘MEM X Xs’ \\
     gs [MEM_EL, fromList_FAPPLY_EL, FDOM_fromList, EL_MAP] \\
     rename1 ‘X = EL i Xs’ \\
    `STRONG_EQUIV (EL i Ps) (CCS_SUBST (fromList Xs Ps) (EL i Es))` by PROVE_TAC [] \\
     IMP_RES_TAC PROPERTY_STAR_LEFT \\
     Q.ABBREV_TAC `E = EL i Es` >> `MEM E Es` by PROVE_TAC [MEM_EL] \\
     Know `weakly_guarded Xs E /\ FV E SUBSET (set Xs)`
     >- (fs [EVERY_MEM, MEM_EL] \\
        `MEM E Es` by PROVE_TAC [MEM_EL] >> METIS_TAC []) >> STRIP_TAC \\
    `?E'. context Xs E' /\
          FV E' SUBSET (set Xs) /\
         (E2 = CCS_SUBST (fromList Xs Ps) E') /\
         !Qs. (LENGTH Qs = LENGTH Xs) ==>
              TRANS (CCS_SUBST (fromList Xs Qs) E) u
                    (CCS_SUBST (fromList Xs Qs) E')`
        by METIS_TAC [Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma] \\
     POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) >> RW_TAC std_ss [] \\
    `STRONG_EQUIV (EL i Qs) (CCS_SUBST (fromList Xs Qs) E)` by PROVE_TAC [] \\
    `?E2. TRANS (EL i Qs) u E2 /\
          STRONG_EQUIV (CCS_SUBST (fromList Xs Qs) E') E2`
        by METIS_TAC [PROPERTY_STAR_RIGHT, STRONG_EQUIV_SYM] \\
     Q.EXISTS_TAC `E2` >> RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E'` >> art [] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) E'` >> art [] \\
     CONJ_TAC (* `IS_PROC ...` #1 *)
     >- (MATCH_MP_TAC CCS_SUBST_IS_PROC >> fs [context_def]) \\
     CONJ_TAC (* `IS_PROC ...` #2 *)
     >- (MATCH_MP_TAC CCS_SUBST_IS_PROC >> fs [context_def]) \\
     DISJ2_TAC >> Q.EXISTS_TAC `E'` >> art [])
 (* 13 subgoals left *)
 >- (rename1 ‘MEM X Xs’ \\
     gs [MEM_EL, fromList_FAPPLY_EL, FDOM_fromList, EL_MAP] \\
     rename1 ‘X = EL i Xs’ \\
    `STRONG_EQUIV (EL i Qs) (CCS_SUBST (fromList Xs Qs) (EL i Es))` by PROVE_TAC [] \\
     Q.ABBREV_TAC `E = EL i Es` >> `MEM E Es` by PROVE_TAC [MEM_EL] \\
     Know `weakly_guarded Xs E /\ FV E SUBSET (set Xs)`
     >- (fs [EVERY_MEM, MEM_EL] \\
        `MEM E Es` by PROVE_TAC [MEM_EL] >> METIS_TAC []) >> STRIP_TAC \\
    `?E2'. TRANS (CCS_SUBST (fromList Xs Qs) E) u E2' /\ STRONG_EQUIV E2' E2`
        by METIS_TAC [PROPERTY_STAR_LEFT, STRONG_EQUIV_SYM] \\
    `?E'. context Xs E' /\
          FV E' SUBSET (set Xs) /\
         (E2' = CCS_SUBST (fromList Xs Qs) E') /\
         !Ps. (LENGTH Ps = LENGTH Xs) ==>
              TRANS (CCS_SUBST (fromList Xs Ps) E) u
                    (CCS_SUBST (fromList Xs Ps) E')`
        by METIS_TAC [Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma] \\
     POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
    `STRONG_EQUIV (EL i Ps) (CCS_SUBST (fromList Xs Ps) E)` by PROVE_TAC [] \\
    `?E1. TRANS (EL i Ps) u E1 /\
          STRONG_EQUIV E1 (CCS_SUBST (fromList Xs Ps) E')`
        by METIS_TAC [PROPERTY_STAR_RIGHT] \\
     Q.EXISTS_TAC `E1` >> RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E'` >> art [] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) E'` >> art [] \\
     CONJ_TAC (* `IS_PROC ...` #1 *)
     >- (MATCH_MP_TAC CCS_SUBST_IS_PROC >> fs [context_def]) \\
     CONJ_TAC (* `IS_PROC ...` #2 *)
     >- (MATCH_MP_TAC CCS_SUBST_IS_PROC >> fs [context_def]) \\
     DISJ2_TAC >> Q.EXISTS_TAC `E'` >> art [])
 (* 12 subgoals left, E = prefix u G (easy) *)
 >- (fs [FV_def, context_prefix_rewrite, ssub_thm, TRANS_PREFIX_EQ, IS_PROC_prefix] \\
     RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G` >> art [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G` >> art [STRONG_EQUIV_REFL] \\
     DISJ2_TAC >> Q.EXISTS_TAC `G` >> rw [])
 (* 11 subgoals left *)
 >- (fs [FV_def, context_prefix_rewrite, ssub_thm, TRANS_PREFIX_EQ, IS_PROC_prefix] \\
     RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G` >> art [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G` >> art [STRONG_EQUIV_REFL] \\
     DISJ2_TAC >> Q.EXISTS_TAC `G` >> rw [])
 (* 10 subgoals left, E = G + G' (not hard) *)
 >- (fs [context_sum_rewrite, TRANS_SUM_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G --u-> E1 ==> _) /\ _’ (MP_TAC o (Q.SPEC ‘u’)) \\
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G' --u-> E1 ==> _) /\ _’ K_TAC \\
       RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM ‘!E1. [Ps/Xs] G --u-> E1 ==> _’ (MP_TAC o (Q.SPEC ‘E1’)) \\
       Q.PAT_X_ASSUM ‘!E2. [Qs/Xs] G --u-> E2 ==> _’ K_TAC \\
       RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E2` >> simp [] \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G`, `u`] >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E2` >> simp [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G --u-> E1 ==> _) /\ _’ K_TAC \\
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G' --u-> E1 ==> _) /\ _’ (MP_TAC o (Q.SPEC ‘u’)) \\
       RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM ‘!E1. [Ps/Xs] G' --u-> E1 ==> _’ (MP_TAC o (Q.SPEC ‘E1’)) \\
       Q.PAT_X_ASSUM ‘!E2. [Qs/Xs] G' --u-> E2 ==> _’ K_TAC \\
       RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `E2` >> simp [] \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G'`, `u`] >> art [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `E2` >> simp [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ] ])
 (* 9 subgoals *)
 >- (fs [context_sum_rewrite, TRANS_SUM_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G --u-> E1 ==> _) /\ _’ (MP_TAC o (Q.SPEC ‘u’)) \\
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G' --u-> E1 ==> _) /\ _’ K_TAC \\
       RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM ‘!E1. [Ps/Xs] G --u-> E1 ==> _’ K_TAC \\
       Q.PAT_X_ASSUM ‘!E2. [Qs/Xs] G --u-> E2 ==> _’ (MP_TAC o (Q.SPEC ‘E2’)) \\
       RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E1` >> simp [] \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G`, `u`] >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E1` >> simp [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G --u-> E1 ==> _) /\ _’ K_TAC \\
       Q.PAT_X_ASSUM ‘!u. (!E1. [Ps/Xs] G' --u-> E1 ==> _) /\ _’ (MP_TAC o (Q.SPEC ‘u’)) \\
       RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM ‘!E1. [Ps/Xs] G' --u-> E1 ==> _’ K_TAC \\
       Q.PAT_X_ASSUM ‘!E2. [Qs/Xs] G' --u-> E2 ==> _’ (MP_TAC o (Q.SPEC ‘E2’)) \\
       RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E1` >> simp [] \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G'`, `u`] >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E1` >> simp [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ] ])
 (* 8 subgoals: E = G || G' (hard) *)
 >- (rename1 ‘context Xs (G1 || G2)’ \\
     fs [context_par_rewrite] \\
     Q.ABBREV_TAC `GP1 = CCS_SUBST (fromList Xs Ps) G1` \\
     Q.ABBREV_TAC `GQ1 = CCS_SUBST (fromList Xs Qs) G1` \\
     Q.ABBREV_TAC `GP2 = CCS_SUBST (fromList Xs Ps) G2` \\
     Q.ABBREV_TAC `GQ2 = CCS_SUBST (fromList Xs Qs) G2` \\
     IMP_RES_TAC TRANS_PAR >| (* 3 subgoals from: GP || G'P --u-> E1 *)
     [ (* goal 1 (of 3):
            GP --u-> E1' /\ (E1 = E1' || G'P),
            GP || G'P --u-> (E1 = E1' || G'P)
        *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP2 u E1 => _) /\ _` K_TAC \\
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP1 u E1 => _) /\ _`
          (MP_TAC o (Q.SPEC `u`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP1 u E1 => _` (MP_TAC o (Q.SPEC `E1'`))\\
       Q.PAT_X_ASSUM `!E2. TRANS GQ1 u E2 => _` K_TAC \\
       RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E2 || GQ2` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR1 >> art []) \\
        `STRONG_EQUIV E1' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         rename1 ‘closed y’ \\
         Q.EXISTS_TAC `y || GQ2` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         Q.EXISTS_TAC `y || GP2` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         ASM_SIMP_TAC std_ss [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `y || G2` \\
         ASM_SIMP_TAC (srw_ss()) [context_par_rewrite,
                                  FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* 2 subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E2 || GQ2` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR1 >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         Q.EXISTS_TAC `y || GQ2` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         Q.EXISTS_TAC `x || GP2` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC ‘G || G2’ \\
         rw [Abbr ‘x’, Abbr ‘y’, Abbr ‘GP2’, Abbr ‘GQ2’, context_par_rewrite] ],
       (* goal 2 (of 3):
            G'P --u-> E1' /\ (E1 = GP || E1')
            GP || G'P --u-> (E1 = GP || E1')
        *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP1 u E1 => _) /\ _` K_TAC \\
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP2 u E1 => _) /\ _`
          (MP_TAC o (Q.SPEC `u`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP2 u E1 => _` (MP_TAC o (Q.SPEC `E1'`)) \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ2 u E2 ==> _` K_TAC \\
       RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `GQ1 || E2` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR2 >> art []) \\
        `STRONG_EQUIV E1' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         rename1 ‘closed y’ \\
         Q.EXISTS_TAC `GQ1 || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         Q.EXISTS_TAC `GP1 || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         ASM_SIMP_TAC std_ss [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G1 || y` \\
         ASM_SIMP_TAC (srw_ss()) [context_par_rewrite,
                                  FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* s subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `GQ1 || E2` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR2 >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         Q.EXISTS_TAC `GQ1 || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `GP1 || x` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G1 || G` \\
         rw [Abbr ‘x’, Abbr ‘y’, Abbr ‘GP1’, Abbr ‘GQ1’, context_par_rewrite] ],
       (* goal 3 (of 3):
            GP --label l-> E1' /\ G'P --label (COMPL l)-> E2
            GP || G'P --tau-> (E1 = E1' || E2)
        *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP1 u E1 => _) /\ _`
         (MP_TAC o (Q.SPEC `label l`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP2 u E1 => _) /\ _`
         (MP_TAC o (Q.SPEC `label (COMPL l)`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ1 (label l) E2 ==> _` K_TAC \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ2 (label (COMPL l)) E2 ==> _` K_TAC \\
       Q.PAT_X_ASSUM `!E1. TRANS GP1 (label l) E1 => _`
          (MP_TAC o (Q.SPEC `E1'`)) >> RW_TAC std_ss [O_DEF] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP2 (label (COMPL l)) E1 => _`
          (MP_TAC o (Q.SPEC `E2`)) >> RW_TAC std_ss [O_DEF] >| (* 4 subgoals *)
       [ (* goal 3.1 (of 4) *)
         Q.EXISTS_TAC `E2' || E2''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         rename1 `STRONG_EQUIV y E2'` \\
         rename1 `STRONG_EQUIV x E2''` \\
         Q.EXISTS_TAC `y || x` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `y || x` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION],
         (* goal 3.2 (of 4) *)
         Q.EXISTS_TAC `E2' || E2''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         rename1 ‘STRONG_EQUIV x1 E2'’ \\
         Q.EXISTS_TAC `x1 || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `x1 || x` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `x1 || G` \\
         fs [context_par_rewrite, FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* s subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 3.3 (of 4) *)
         Q.EXISTS_TAC `E2' || E2''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         rename1 ‘STRONG_EQUIV x1 E2''’ \\
         Q.EXISTS_TAC `y || x1` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `x || x1` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G || x1` \\
         fs [context_par_rewrite, FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* s subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 3.4 (of 4) *)
         Q.EXISTS_TAC `E2' || E2''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         Q.EXISTS_TAC `par (CCS_SUBST (fromList Xs Qs) G)
                           (CCS_SUBST (fromList Xs Qs) G')` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `par (CCS_SUBST (fromList Xs Ps) G)
                           (CCS_SUBST (fromList Xs Ps) G')` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G || G'` \\
         fs [context_par_rewrite, FV_def, CCS_SUBST_def, UNION_SUBSET] ] ])
 (* 7 subgoals left *)
 >- (rename1 ‘context Xs (G1 || G2)’ \\
     fs [context_par_rewrite] \\
     Q.ABBREV_TAC `GP1 = CCS_SUBST (fromList Xs Ps) G1` \\
     Q.ABBREV_TAC `GQ1 = CCS_SUBST (fromList Xs Qs) G1` \\
     Q.ABBREV_TAC `GP2 = CCS_SUBST (fromList Xs Ps) G2` \\
     Q.ABBREV_TAC `GQ2 = CCS_SUBST (fromList Xs Qs) G2` \\
     IMP_RES_TAC TRANS_PAR >| (* 3 subgoals from: GQ || G'Q --u-> E2 *)
     [ (* goal 1 (of 3):
            GQ --u-> E1 /\ (E2 = E1 || G'Q),
            GQ || G'Q --u-> (E2 = E1 || G'Q)
        *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP2 u E1 => _) /\ _` K_TAC \\
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP1 u E1 => _) /\ _`
          (MP_TAC o (Q.SPEC `u`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP1 u E1 => _` K_TAC \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ1 u E2 => _`
          (MP_TAC o (Q.SPEC `E1`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E1' || GP2` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR1 >> art []) \\
        `STRONG_EQUIV E1' E1` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         rename1 ‘closed y’ \\
         Q.EXISTS_TAC `y || GQ2` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         Q.EXISTS_TAC `y || GP2` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         ASM_SIMP_TAC std_ss [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `y || G2` \\
         ASM_SIMP_TAC (srw_ss()) [context_par_rewrite,
                                  FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* 2 subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E1' || GP2` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR1 >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         Q.EXISTS_TAC `y || GQ2` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `x || GP2` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_R >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G || G2` \\
         ASM_SIMP_TAC lset_ss [context_par_rewrite,
                               FV_def, CCS_SUBST_def, UNION_SUBSET] ],
       (* goal 2 (of 3):
            G'Q --u-> E1 /\ (E2 = GQ || E1)
            GQ || G'Q --u-> (E2 = GQ || E1)
        *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP1 u E1 => _) /\ _` K_TAC \\
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP2 u E1 => _) /\ _`
          (MP_TAC o (Q.SPEC `u`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP2 u E1 => _` K_TAC \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ2 u E2 ==> _`
          (MP_TAC o (Q.SPEC `E1`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `GP1 || E1'` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR2 >> art []) \\
         rename1 ‘closed y’ \\
         Q.EXISTS_TAC `GQ1 || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         Q.EXISTS_TAC `GP1 || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         ASM_SIMP_TAC std_ss [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G1 || y` \\
         ASM_SIMP_TAC (srw_ss()) [context_par_rewrite,
                                  FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* s subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `GP1 || E1'` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR2 >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         Q.EXISTS_TAC `GQ1 || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `GP1 || x` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PAR_L >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G1 || G` \\
         ASM_SIMP_TAC lset_ss [context_par_rewrite,
                               FV_def, CCS_SUBST_def, UNION_SUBSET] ],
       (* goal 3 (of 3):
            GQ --label l-> E1 /\ G'Q --label (COMPL l)-> E2'
            GQ || G'Q --tau-> (E2 = E1 || E2')
        *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP1 u E1 => _) /\ _`
          (MP_TAC o (Q.SPEC `label l`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!u. (!E1. TRANS GP2 u E1 => _) /\ _`
          (MP_TAC o (Q.SPEC `label (COMPL l)`)) >> RW_TAC std_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP1 (label l) E1 => _` K_TAC \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ1 (label l) E2 ==> _`
          (MP_TAC o (Q.SPEC `E1`)) >> RW_TAC std_ss [O_DEF] \\
       Q.PAT_X_ASSUM `!E1. TRANS GP2 (label (COMPL l)) E1 => _` K_TAC \\
       Q.PAT_X_ASSUM `!E2. TRANS GQ2 (label (COMPL l)) E2 ==> _`
          (MP_TAC o (Q.SPEC `E2'`)) >> RW_TAC std_ss [O_DEF] >| (* 4 subgoals *)
       [ (* goal 3.1 (of 4) *)
         Q.EXISTS_TAC `E1' || E1''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         rename1 `STRONG_EQUIV y E2'` \\
         rename1 `STRONG_EQUIV E1' x` \\
         Q.EXISTS_TAC `x || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `x || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION],
         (* goal 3.2 (of 4) *)
         Q.EXISTS_TAC `E1' || E1''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         rename1 ‘STRONG_EQUIV x1 E1’ \\
         Q.EXISTS_TAC `x1 || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `x1 || x` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `x1 || G` \\
         fs [context_par_rewrite, FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* s subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 3.3 (of 4) *)
         Q.EXISTS_TAC `E1' || E1''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G’ \\
         rename1 ‘STRONG_EQUIV x1 E2'’ \\
         Q.EXISTS_TAC `y || x1` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         qabbrev_tac ‘x = [Ps/Xs] G’ \\
         Q.EXISTS_TAC `x || x1` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G || x1` \\
         fs [context_par_rewrite, FV_def, CCS_SUBST_def, UNION_SUBSET] \\
         STRONG_CONJ_TAC (* `context Xs y` *)
         >- (MATCH_MP_TAC disjoint_imp_context >> art [] \\
             ASM_SET_TAC [IS_PROC_def]) >> DISCH_TAC \\
         CONJ_TAC >- ASM_SET_TAC [IS_PROC_def] \\
         CONJ_TAC \\ (* s subgoals, same tactics *)
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC CCS_SUBST_elim >> art [] \\
         ASM_SET_TAC [IS_PROC_def],
         (* goal 3.4 (of 4) *)
         Q.EXISTS_TAC `E1' || E1''` \\
         CONJ_TAC >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> art []) \\
         Q.EXISTS_TAC `par (CCS_SUBST (fromList Xs Qs) G)
                           (CCS_SUBST (fromList Xs Qs) G')` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `par (CCS_SUBST (fromList Xs Ps) G)
                           (CCS_SUBST (fromList Xs Ps) G')` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         fs [IS_PROC_par, DISJOINT_UNION] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G || G'` \\
         fs [context_par_rewrite, FV_def, CCS_SUBST_def, UNION_SUBSET] ] ])
 (* 6 subgoals: E = restr f G (not easy) *)
 >- (fs [context_restr_rewrite, TRANS_RESTR_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `tau`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) tau E2 ==> _` K_TAC \\
       Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) tau E1 ==> _`
         (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `restr L E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
         Q.EXISTS_TAC `restr L E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr L E'') (restr L E2)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L E2` >> art [] \\
         fs [IS_PROC_restr] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G`, `tau`] >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `restr L E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G'’ \\
        `STRONG_EQUIV (restr L y) (restr L E2)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L y` >> art [] \\
         qabbrev_tac ‘x = [Ps/Xs] G'’ \\
        `STRONG_EQUIV (restr L E'') (restr L x)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L x` >> art [] \\
         fs [IS_PROC_restr] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr L G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         rw [FV_def, ssub_thm] ],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `label l`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM
         `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) (label l) E2 ==> _` K_TAC \\
       Q.PAT_X_ASSUM
         `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) (label l) E1 ==> _`
         (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `restr L E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
         Q.EXISTS_TAC `restr L E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr L E'') (restr L E2)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L E2` >> art [] \\
         fs [IS_PROC_restr] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G`, `label l`] >> art [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `restr L E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G'’ \\
        `STRONG_EQUIV (restr L y) (restr L E2)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L y` >> art [] \\
         qabbrev_tac ‘x = [Ps/Xs] G'’ \\
        `STRONG_EQUIV (restr L E'') (restr L x)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L x` >> art [] \\
         fs [IS_PROC_restr] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr L G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         rw [FV_def, ssub_thm] ] ])
 (* 5 subgoals: E = restr f G (not easy) *)
 >- (fs [context_restr_rewrite, TRANS_RESTR_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `tau`)) >>  RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) tau E1 ==> _` K_TAC \\
       Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) tau E2 ==> _`
         (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `restr L E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
         Q.EXISTS_TAC `restr L E''` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr L E1) (restr L E'')` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L E''` >> art [] \\
         fs [IS_PROC_restr] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G`, `tau`] >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `restr L E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G'’ \\
        `STRONG_EQUIV (restr L y) (restr L E'')` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L y` >> art [] \\
         qabbrev_tac ‘x = [Ps/Xs] G'’ \\
        `STRONG_EQUIV (restr L E1) (restr L x)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L x` >> art [] \\
         fs [IS_PROC_restr] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr L G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         rw [FV_def, ssub_thm] ],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `label l`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM
          `!E2. TRANS (CCS_SUBST (fromList Xs Ps) G) (label l) E2 ==> _` K_TAC \\
       Q.PAT_X_ASSUM
          `!E1. TRANS (CCS_SUBST (fromList Xs Qs) G) (label l) E1 ==> _`
          (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `restr L E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
         Q.EXISTS_TAC `restr L E''` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr L E1) (restr L E'')` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L E''` >> art [] \\
         fs [IS_PROC_restr] \\
         MATCH_MP_TAC TRANS_PROC \\
         take [`CCS_SUBST (fromList Xs Qs) G`, `label l`] >> art [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `restr L E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
         qabbrev_tac ‘y = [Qs/Xs] G'’ \\
        `STRONG_EQUIV (restr L y) (restr L E'')` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L y` >> art [] \\
         qabbrev_tac ‘x = [Ps/Xs] G'’ \\
        `STRONG_EQUIV (restr L E1) (restr L x)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr L x` >> art [] \\
         fs [IS_PROC_restr] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr L G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         rw [FV_def, ssub_thm, Abbr ‘x’, Abbr ‘y’] ] ])
 (* 4 subgoals left: E = relab f G (not hard) *)
 >- (fs [context_relab_rewrite, TRANS_RELAB_EQ] \\
     Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
       (MP_TAC o (Q.SPEC `u'`)) >> RW_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) u' E2 ==> _` K_TAC \\
     Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u' E2 ==> _`
       (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `relab E2 rf` \\
       CONJ_TAC >- (take [`u'`, `E2`] >> art []) \\
       Q.EXISTS_TAC `relab E2 rf` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      `STRONG_EQUIV E'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `STRONG_EQUIV (relab E'' rf) (relab E2 rf)` by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
       Q.EXISTS_TAC `relab E2 rf` >> art [] \\
       fs [IS_PROC_relab] \\
       MATCH_MP_TAC TRANS_PROC \\
       take [`CCS_SUBST (fromList Xs Qs) G`, `u'`] >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `relab E2 rf` \\
       CONJ_TAC >- (take [`u'`, `E2`] >> art []) \\
       qabbrev_tac ‘y = [Qs/Xs] G'’ \\
      `STRONG_EQUIV (relab y rf) (relab E2 rf)` by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
       Q.EXISTS_TAC `relab y rf` >> art [] \\
       qabbrev_tac ‘x = [Ps/Xs] G'’ \\
      `STRONG_EQUIV (relab E'' rf) (relab x rf)` by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
       Q.EXISTS_TAC `relab x rf` >> art [] \\
       fs [IS_PROC_relab] \\
       DISJ2_TAC >> Q.EXISTS_TAC `relab G' rf` \\
       CONJ_TAC >- (MATCH_MP_TAC context_relab_rule >> art []) \\
       rw [FV_def, ssub_thm, Abbr ‘x’, Abbr ‘y’] ])
 (* 3 subgoals *)
 >- (fs [context_relab_rewrite, TRANS_RELAB_EQ] \\
     Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
       (MP_TAC o (Q.SPEC `u'`)) >> RW_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u' E1 ==> _` K_TAC \\
     Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) u' E2 ==> _`
       (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `relab E1 rf` \\
       CONJ_TAC >- (take [`u'`, `E1`] >> art []) \\
       Q.EXISTS_TAC `relab E'' rf` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      `STRONG_EQUIV E1 E''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `STRONG_EQUIV (relab E1 rf) (relab E'' rf)` by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
       Q.EXISTS_TAC `relab E'' rf` >> art [] \\
       fs [IS_PROC_relab] \\
       MATCH_MP_TAC TRANS_PROC \\
       take [`CCS_SUBST (fromList Xs Qs) G`, `u'`] >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `relab E1 rf` \\
       CONJ_TAC >- (take [`u'`, `E1`] >> art []) \\
       qabbrev_tac ‘y = [Qs/Xs] G'’ \\
      `STRONG_EQUIV (relab y rf) (relab E'' rf)` by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
       Q.EXISTS_TAC `relab y rf` >> art [] \\
       qabbrev_tac ‘x = [Ps/Xs] G'’ \\
      `STRONG_EQUIV (relab E1 rf) (relab x rf)` by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
       Q.EXISTS_TAC `relab x rf` >> art [] \\
       fs [IS_PROC_relab] \\
       DISJ2_TAC >> Q.EXISTS_TAC `relab G' rf` \\
       CONJ_TAC >- (MATCH_MP_TAC context_relab_rule >> art []) \\
       rw [FV_def, ssub_thm, Abbr ‘x’, Abbr ‘y’] ])
 (* 2 subgoals *)
 >- (Q.PAT_X_ASSUM ‘context Xs G ==> _’ K_TAC (* IH is not needed *) \\
     IMP_RES_TAC context_rec \\
    `DISJOINT (FV (rec y G)) (set Xs)` by ASM_SET_TAC [FV_def] \\
    `CCS_SUBST (fromList Xs Ps) (rec y G) = rec y G /\
     CCS_SUBST (fromList Xs Qs) (rec y G) = rec y G` by METIS_TAC [CCS_SUBST_elim] \\
     POP_ORW \\
     POP_ASSUM (fs o wrap) \\
     RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `E1` >> art [] \\
     Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
     MATCH_MP_TAC TRANS_PROC >> take [`rec y G`, `u`] >> art [])
 (* final goal *)
 >> (Q.PAT_X_ASSUM ‘context Xs G ==> _’ K_TAC (* IH is not needed *) \\
     IMP_RES_TAC context_rec \\
    `DISJOINT (FV (rec y G)) (set Xs)` by ASM_SET_TAC [FV_def] \\
    `CCS_SUBST (fromList Xs Qs) (rec y G) = rec y G /\
     CCS_SUBST (fromList Xs Ps) (rec y G) = rec y G` by METIS_TAC [CCS_SUBST_elim] \\
     POP_ORW \\
     POP_ASSUM (fs o wrap) \\
     RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `E2` >> art [] \\
     Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
     MATCH_MP_TAC TRANS_PROC >> take [`rec y G`, `u`] >> art [])
QED

(* ========================================================================== *)
(*  Section V: Unique Solution of (Rooted) Contractions                       *)
(* ========================================================================== *)

(* Transitivity is a property of equivalence but OBS_contracts is PreOrder,
   thus this lemma doesn't derive from LIST_REL_equivalence.
 *)
Theorem OBS_contracts_transitive :
    !(Ps :'a CCS list) Qs Rs.
          LIST_REL OBS_contracts Ps Qs /\ LIST_REL OBS_contracts Qs Rs
      ==> LIST_REL OBS_contracts Ps Rs
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC LIST_REL_trans
 >> Q.EXISTS_TAC `Qs` >> RW_TAC std_ss []
 >> MATCH_MP_TAC OBS_contracts_TRANS
 >> Q.EXISTS_TAC `EL n Qs` >> art []
QED

Theorem OBS_contracts_reflexive :
    !(Ps :'a CCS list). LIST_REL OBS_contracts Ps Ps
Proof
    RW_TAC list_ss [LIST_REL_EL_EQN, OBS_contracts_REFL]
QED

(* USC unfolding lemmas for unique_solution_of_rooted_contractions_lemma
  "USC" := "Unique Solution of (Rooted) Contractions".

   Lemma 1,4 are directly used; Lemma 2,3 are further lemmas of Lemma 4.
*)
Theorem USC_unfolding_lemma1 :
    !Xs Es E C0 Ps.
           CCS_equation Xs Es /\ EVERY (context Xs) Es /\
           CCS_solution OBS_contracts Xs Es Ps /\ context Xs C /\
           (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) /\
           (C0 = \Ys. (CCS_SUBST (fromList Xs Ys)) C)
       ==> !n. OBS_contracts (C0 Ps) ((C0 o (FUNPOW E n)) Ps)
Proof
    rpt GEN_TAC >> STRIP_TAC (* up to `!n` *)
 >> `ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs)`
     by PROVE_TAC [CCS_equation_def]
 >> Q.PAT_X_ASSUM `C0 = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.PAT_X_ASSUM `E  = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 (* re-define C0 and E as abbreviations *)
 >> Q.ABBREV_TAC  `E  = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 >> RW_TAC std_ss [o_DEF]
 >> `ALL_DISTINCT Xs` by PROVE_TAC [CCS_equation_def]
 >> `LENGTH Ps = LENGTH Xs` by PROVE_TAC [CCS_solution_length]
 >> fs [CCS_solution_def]
 >> irule OBS_contracts_subst_context >> art []
 (* applying induction *)
 >> Induct_on `n` >- rw [FUNPOW_0, OBS_contracts_reflexive]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `Qs = FUNPOW E n Ps`
 >> Know `OBS_contracts (E Ps) (E Qs)`
 >- (Q.UNABBREV_TAC `E` >> BETA_TAC \\
     RW_TAC list_ss [LIST_REL_EL_EQN, EL_MAP] \\
     irule OBS_contracts_subst_context >> art [] \\
    `MEM (EL n' Es) Es` by PROVE_TAC [MEM_EL] \\
     fs [EVERY_MEM]) >> DISCH_TAC
 >> MATCH_MP_TAC OBS_contracts_transitive
 >> Q.EXISTS_TAC `E Ps` >> art []
QED

(* `ALL_PROC Ps` is added to handle the last difficulity *)
Theorem USC_unfolding_lemma2 :
  !Xs. ALL_DISTINCT Xs ==>
       !E. weakly_guarded Xs E ==>
           !Ps u P'. (LENGTH Ps = LENGTH Xs) /\ ALL_PROC Ps /\
                     TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
                ?C'. context Xs C' /\
                    (P' = CCS_SUBST (fromList Xs Ps) C') /\
                    !Qs. (LENGTH Qs = LENGTH Xs) ==>
                         TRANS (CCS_SUBST (fromList Xs Qs) E) u
                               (CCS_SUBST (fromList Xs Qs) C')
Proof
    NTAC 2 STRIP_TAC (* up to `!E` *)
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs’ >> rw [NIL_NO_TRANS, ssub_thm]
 >> gs [FDOM_fromList]
 (* 7 subgoals left *)
 >- (IMP_RES_TAC weakly_guarded_var \\
     rename1 ‘~MEM a Xs’ >> fs [VAR_NO_TRANS])
 (* 6 subgoals left *)
 >- (fs [TRANS_PREFIX_EQ] \\
     IMP_RES_TAC weakly_guarded_prefix \\
     Q.EXISTS_TAC `E` >> rw [])
 (* 5 subgoals left *)
 >- (fs [weakly_guarded_sum_rewrite] \\
     IMP_RES_TAC TRANS_SUM >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM
         ‘!Ps u P'. LENGTH Ps = LENGTH Xs /\ ALL_PROC Ps /\ [Ps/Xs] E --u-> P' ==> _’
         (MP_TAC o (Q.SPECL [`Ps`, `u`, `P'`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `C'` >> RW_TAC std_ss [] \\
       MATCH_MP_TAC SUM1 \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM
         ‘!Ps u P'. LENGTH Ps = LENGTH Xs /\ ALL_PROC Ps /\ [Ps/Xs] E' --u-> P' ==> _’
         (MP_TAC o (Q.SPECL [`Ps`, `u`, `P'`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `C'` >> RW_TAC std_ss [] \\
       MATCH_MP_TAC SUM2 \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 (* 4 subgoals left *)
 >- (fs [weakly_guarded_par_rewrite] \\
     IMP_RES_TAC TRANS_PAR >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.PAT_X_ASSUM
         ‘!Ps u P'. LENGTH Ps = LENGTH Xs /\ ALL_PROC Ps /\ [Ps/Xs] E --u-> P' ==> _’
         (MP_TAC o (Q.SPECL [`Ps`, `u`, `E1`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `par C' E'` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art [] \\
                    MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       RW_TAC std_ss [ssub_thm] \\
       MATCH_MP_TAC PAR1 >> FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM
         ‘!Ps u P'. LENGTH Ps = LENGTH Xs /\ ALL_PROC Ps /\ [Ps/Xs] E' --u-> P' ==> _’
         (MP_TAC o (Q.SPECL [`Ps`, `u`, `E1`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `par E C'` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art [] \\
                    MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       RW_TAC std_ss [ssub_thm] \\
       MATCH_MP_TAC PAR2 >> FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM
         ‘!Ps u P'. LENGTH Ps = LENGTH Xs /\ ALL_PROC Ps /\ [Ps/Xs] E --u-> P' ==> _’
          (MP_TAC o (Q.SPECL [`Ps`, `label l`, `E1`])) \\
       Q.PAT_X_ASSUM
         ‘!Ps u P'. LENGTH Ps = LENGTH Xs /\ ALL_PROC Ps /\ [Ps/Xs] E' --u-> P' ==> _’
          (MP_TAC o (Q.SPECL [`Ps`, `label (COMPL l)`, `E2`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `par C'' C'` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art []) \\
       RW_TAC std_ss [ssub_thm] \\
       MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` \\
       CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 (* 3 subgoals left *)
 >- (fs [weakly_guarded_restr_rewrite, TRANS_RESTR_EQ] >| (* 2 subgoals *)
     [ (* goal 3.1 (of 2) *)
       Q.PAT_X_ASSUM ‘!Ps u P'. P’ (MP_TAC o (Q.SPECL [`Ps`, `tau`, `E''`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `restr L C'` \\
       RW_TAC std_ss [ssub_thm]
       >- (MATCH_MP_TAC context_restr_rule >> art []) \\
       Q.EXISTS_TAC ‘[Qs/Xs] C'’ >> rw [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘!Ps u P'. P’ (MP_TAC o (Q.SPECL [`Ps`, `label l`, `E''`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `restr L C'` \\
       RW_TAC std_ss [ssub_thm]
       >- (MATCH_MP_TAC context_restr_rule >> art []) \\
       Q.EXISTS_TAC ‘[Qs/Xs] C'’ >> rw [] ])
 (* 2 subgoals left *)
 >- (fs [weakly_guarded_relab_rewrite, TRANS_RELAB_EQ] \\
     Q.PAT_X_ASSUM ‘!Ps u P'. P’ (MP_TAC o (Q.SPECL [`Ps`, `u'`, `E''`])) \\
     RW_TAC bool_ss [] \\
     Q.EXISTS_TAC `relab C' rf` \\
     RW_TAC std_ss [ssub_thm]
     >- (MATCH_MP_TAC context_relab_rule >> art []) \\
     qexistsl_tac [‘u'’, ‘[Qs/Xs] C'’] >> rw [])
 (* final goal (hard) *)
 >> IMP_RES_TAC weakly_guarded_rec
 >> ‘DISJOINT (FV (rec y E)) (set Xs)’ by rw [FV_thm]
 >> Q.EXISTS_TAC `P'`
 >> Suff `DISJOINT (FV P') (set Xs)`
 >- (RW_TAC std_ss []
     >- (MATCH_MP_TAC disjoint_imp_context >> art [])
     >- (MATCH_MP_TAC EQ_SYM >> irule CCS_SUBST_elim >> art []) \\
     Know `CCS_SUBST (fromList Xs Qs) P' = P'`
     >- (irule CCS_SUBST_elim >> art []) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Ps) (rec y E) = rec y E`
     >- (irule CCS_SUBST_elim >> art [] >> ASM_SET_TAC []) \\
     DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap) \\
     Know `CCS_SUBST (fromList Xs Qs) (rec y E) = rec y E`
     >- (irule CCS_SUBST_elim >> art [] >> ASM_SET_TAC []) \\
     DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap))
 (* cleanups and renames before the final battle *)
 >> Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` K_TAC
 (* hard left goal *)
 >> Q.ABBREV_TAC `P = CCS_SUBST (fromList Xs Ps) (rec y E)`
 >> IMP_RES_TAC TRANS_FV
 >> Know `FV P SUBSET (FV (rec y E)) UNION (BIGUNION (IMAGE FV (set Ps)))`
 >- (Q.UNABBREV_TAC `P` \\
     MATCH_MP_TAC FV_SUBSET_BIGUNION >> art []) >> DISCH_TAC
 >> FULL_SIMP_TAC bool_ss [ALL_PROC_def, EVERY_MEM, IS_PROC_def]
 >> Know `BIGUNION (IMAGE FV (set Ps)) = EMPTY`
 >- rw [NOT_IN_EMPTY, IN_BIGUNION_IMAGE, IMAGE_EQ_SING]
 >> ASM_SET_TAC []
QED

(* It depends on lemma2 and repeated applications of
   the (celebrated) CCS_SUBST_nested.
 *)
Theorem USC_unfolding_lemma3 :
    !Xs Es C E. ALL_DISTINCT Xs /\ context Xs C /\
               (LENGTH Es = LENGTH Xs) /\
                EVERY (weakly_guarded Xs) Es /\
               (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) ==>
       !Ps x P'. (LENGTH Ps = LENGTH Xs) /\ ALL_PROC Ps /\
                 TRANS (CCS_SUBST (fromList Xs (E Ps)) C) x P' ==>
          ?C'. context Xs C' /\
              (P' = CCS_SUBST (fromList Xs Ps) C') /\
              !Qs. (LENGTH Qs = LENGTH Xs) ==>
                    TRANS (CCS_SUBST (fromList Xs (E Qs)) C) x
                          (CCS_SUBST (fromList Xs Qs) C')
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `E  = _` ((FULL_SIMP_TAC std_ss) o wrap)
 >> Know `weakly_guarded Xs (CCS_SUBST (fromList Xs Es) C)`
 >- (MATCH_MP_TAC weakly_guarded_combin >> art []) >> DISCH_TAC
 (* applying CCS_SUBST_nested *)
 >> Know `CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Ps)) Es)) C =
          CCS_SUBST (fromList Xs Ps) (CCS_SUBST (fromList Xs Es) C)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC CCS_SUBST_nested >> art [])
 >> DISCH_THEN (fs o wrap)
 >> Q.ABBREV_TAC `C' = CCS_SUBST (fromList Xs Es) C`
 (* applying USC_unfolding_lemma2 *)
 >> MP_TAC (Q.SPEC `Xs` USC_unfolding_lemma2)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPEC `C'`))
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `x`, `P'`]))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `C''` >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!Qs. LENGTH Qs = LENGTH Xs ==> _` (MP_TAC o (Q.SPEC `Qs`))
 >> RW_TAC std_ss []
 (* applying CCS_SUBST_nested AGAIN *)
 >> Suff `CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Qs)) Es)) C =
          CCS_SUBST (fromList Xs Qs) C'` >- rw []
 >> Q.UNABBREV_TAC `C'`
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC CCS_SUBST_nested >> art []
QED

(* (directly) used in unique_solution_of_rooted_contractions_lemma *)
Theorem USC_unfolding_lemma4 :
    !Xs Es C E C0.
           CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
           context Xs C /\
          (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) /\
          (C0 = \Ys. (CCS_SUBST (fromList Xs Ys)) C) ==>
       !n xs Ps P'.
          (LENGTH Ps = LENGTH Xs) /\ ALL_PROC Ps /\
           TRACE ((C0 o FUNPOW E n) Ps) xs P' /\ LENGTH xs <= n ==>
           ?C''. context Xs C'' /\
                (P' = CCS_SUBST (fromList Xs Ps) C'') /\
                !Qs. (LENGTH Qs = LENGTH Xs) ==>
                      TRACE ((C0 o FUNPOW E n) Qs) xs
                            (CCS_SUBST (fromList Xs Qs) C'')
Proof
    rpt GEN_TAC >> STRIP_TAC (* up to `!n` *)
 >> `ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs)` by PROVE_TAC [CCS_equation_def]
 (* re-define C' and E back to abbreviations *)
 >> Q.PAT_X_ASSUM `C0 = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.PAT_X_ASSUM `E  = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.ABBREV_TAC  `E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 >> Q.ABBREV_TAC  `C0 = \Ys. (CCS_SUBST (fromList Xs Ys)) C`
(* kick-start by induction *)
 >> Induct_on `n`
 >- (RW_TAC std_ss [o_DEF, FUNPOW_0] \\
     Q.EXISTS_TAC `C` >> fs [TRACE_NIL])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `TRACE _ xs P'` MP_TAC
 >> Know `!Ps. (C0 o (FUNPOW E (SUC n))) Ps = (C0 o (FUNPOW E n)) (E Ps)`
 >- (RW_TAC std_ss [o_DEF, FUNPOW]) >> Rewr
 >> DISCH_TAC
 (* stage work *)
 >> Know `!Qs. (LENGTH Qs = LENGTH Xs) ==> (LENGTH (E Qs) = LENGTH Xs)`
 >- (rpt STRIP_TAC \\
     Q.UNABBREV_TAC `E` >> ASM_SIMP_TAC std_ss [LENGTH_MAP]) >> DISCH_TAC
 >> `LENGTH (E Ps) = LENGTH Xs` by PROVE_TAC []
 >> Know `ALL_PROC (E Ps)`
 >- (Q.UNABBREV_TAC `E` \\
     RW_TAC lset_ss [ALL_PROC_def, IS_PROC_def, EVERY_MEM, MEM_MAP, MEM_EL] \\
     rename1 `i < LENGTH Xs` \\
    `i < LENGTH Es` by PROVE_TAC [] \\
     ASM_SIMP_TAC lset_ss [EL_MAP] \\
     Q.ABBREV_TAC `E = EL i Es` \\
  (* FV (CCS_SUBST (Xs |-> Ps) E) = {}, given `ALL_PROC Ps` *)
     REWRITE_TAC [GSYM IS_PROC_def] \\
     MATCH_MP_TAC CCS_SUBST_IS_PROC >> art [] \\
     fs [CCS_equation_def, EVERY_MEM, weakly_guarded_def] \\
    `MEM E Es` by METIS_TAC [MEM_EL] \\
     PROVE_TAC []) >> DISCH_TAC
 (* stage work *)
 >> IMP_RES_TAC TRACE_cases2
 >> Cases_on `xs`
 >- (FULL_SIMP_TAC bool_ss [NULL] \\
    `LENGTH (epsilon :'a Action list) <= n` by FULL_SIMP_TAC arith_ss [LENGTH] \\
     Know `!Ys. (LENGTH Ys = LENGTH Xs) ==> (LENGTH (E Ys) = LENGTH Xs)`
     >- (rpt STRIP_TAC \\
         Q.UNABBREV_TAC `E` >> ASM_SIMP_TAC list_ss [LENGTH_MAP]) \\
     DISCH_TAC \\
     Q.PAT_X_ASSUM `!xs Ps P'. _ ==> _`
        (MP_TAC o (Q.SPECL [`[] :'a Action list`,
                            `(E :'a CCS list -> 'a CCS list) Ps`, `P'`])) \\
     Q.PAT_ASSUM `_ = P'` (ONCE_REWRITE_TAC o wrap) \\
     RW_TAC bool_ss [] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Es) C''`  \\
     CONJ_TAC (* context Xs (CCS_SUBST (Xs |-> Es) C'') *)
     >- (MATCH_MP_TAC context_combin >> fs [EVERY_MEM] \\
         rpt STRIP_TAC >> MATCH_MP_TAC weakly_guarded_imp_context \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     CONJ_TAC (* CCS_SUBST_nested *)
     >- (Q.PAT_X_ASSUM `_ = CCS_SUBST (fromList Xs (E Ps)) C''`
            (ONCE_REWRITE_TAC o wrap) \\
         Q.UNABBREV_TAC `E` >> BETA_TAC \\
         MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC CCS_SUBST_nested \\
         fs [context_def]) \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM `!Qs. (LENGTH Qs = LENGTH Xs) ==> _`
        (MP_TAC o (Q.SPEC `(E :'a CCS list -> 'a CCS list) Qs`)) \\
     RW_TAC bool_ss [] \\
     Suff `CCS_SUBST (fromList Xs Qs) (CCS_SUBST (fromList Xs Es) C'') =
           CCS_SUBST (fromList Xs (E Qs)) C''` >- (Rewr' >> art []) \\
     POP_ASSUM K_TAC \\
     Q.UNABBREV_TAC `E` >> fs [] \\
     MATCH_MP_TAC CCS_SUBST_nested >> fs [context_def])
 (* hard part *)
 >> FULL_SIMP_TAC list_ss []
 >> `LENGTH (FRONT (h::t)) <= n` by PROVE_TAC [LENGTH_FRONT_CONS]
 >> rename1 `TRANS P _ P'`
 >> Q.ABBREV_TAC `us = FRONT (h::t)`
 >> Q.ABBREV_TAC `u = LAST (h::t)`
 >> Q.PAT_X_ASSUM `!xs Ps' P''. _ ==> ?C''. _`
      (MP_TAC o
       (Q.SPECL [`us`, `(E :'a CCS list -> 'a CCS list) Ps`, `P`]))
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`Xs`, `Es`, `C''`, `E`] USC_unfolding_lemma3)
 >> FULL_SIMP_TAC bool_ss [CCS_equation_def]
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u`, `P'`]))
 >> RW_TAC bool_ss []
 >> Q.EXISTS_TAC `C'` >> art []
 >> RW_TAC std_ss [Once TRACE_cases2, NULL]
 >> Q.PAT_X_ASSUM `!Qs. (LENGTH Qs = LENGTH Xs) ==> _` (MP_TAC o (Q.SPEC `Qs`))
 >> RW_TAC bool_ss []
 >> Q.EXISTS_TAC `CCS_SUBST (fromList Xs (E Qs)) C''`
 >> `LENGTH (E Qs) = LENGTH Xs` by PROVE_TAC []
 >> ASM_SIMP_TAC std_ss []
QED

(* Lemma 3.9 of [2], the full (multivariate) version *)
Theorem unique_solution_of_rooted_contractions_lemma :
    !Xs Es Ps Qs. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
                  CCS_solution OBS_contracts Xs Es Ps /\
                  CCS_solution OBS_contracts Xs Es Qs ==>
        !C. context Xs C ==>
            (!l R. WEAK_TRANS (CCS_SUBST (fromList Xs Ps) C) (label l) R ==>
                   ?C'. context Xs C' /\
                        R contracts (CCS_SUBST (fromList Xs Ps) C') /\
                        (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y))
                          (CCS_SUBST (fromList Xs Qs) C)
                          (CCS_SUBST (fromList Xs Qs) C')) /\
            (!R. WEAK_TRANS (CCS_SUBST (fromList Xs Ps) C) tau R ==>
                 ?C'. context Xs C' /\
                      R contracts (CCS_SUBST (fromList Xs Ps) C') /\
                      (WEAK_EQUIV O EPS) (CCS_SUBST (fromList Xs Qs) C)
                                         (CCS_SUBST (fromList Xs Qs) C'))
Proof
    NTAC 7 STRIP_TAC (* up to `context Xs C` *)
 >> Know `EVERY (context Xs) Es`
 >- (fs [EVERY_MEM] >> rpt STRIP_TAC \\
     MATCH_MP_TAC weakly_guarded_imp_context \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 (* this turns Es into a chain-able function: E : Ys -> Ys *)
 >> Q.ABBREV_TAC `E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 (* this turns C into a (toplevel) chain-able function: C0 : Ys -> Y *)
 >> Q.ABBREV_TAC `C0 = \Ys. CCS_SUBST (fromList Xs Ys) C`
 >> Q.ABBREV_TAC `CE = \n. C0 o (FUNPOW E n)`
 >> Know `!n. OBS_contracts (C0 Ps) (CE n Ps)`
 >- (Q.UNABBREV_TAC `CE` >> BETA_TAC \\
     MATCH_MP_TAC USC_unfolding_lemma1 \\
     take [`Xs`, `Es`] >> unset [`E`, `C0`] >> art [])
 >> DISCH_TAC
 >> Know `!n. OBS_contracts (C0 Qs) (CE n Qs)`
 >- (Q.UNABBREV_TAC `CE` >> BETA_TAC \\
     MATCH_MP_TAC USC_unfolding_lemma1 \\
     take [`Xs`, `Es`] >> unset [`E`, `C0`] >> art [])
 >> DISCH_TAC
 (* stage work *)
 >> `(LENGTH Ps = LENGTH Xs) /\ (LENGTH Qs = LENGTH Xs)`
      by PROVE_TAC [CCS_solution_length]
 >> fs [CCS_solution_def]
 >> rpt STRIP_TAC (* 2 subgoals (not symmetric) *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [Action_distinct_label] \\
     `OBS_contracts (C0 Ps) (CE (LENGTH us) Ps)` by PROVE_TAC [] \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`us`, `l`, `R`]) o
                 (MATCH_MP OBS_contracts_AND_TRACE_label)) \\
      RW_TAC std_ss [] \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Know `?C'. context Xs C' /\
                (E2 = CCS_SUBST (fromList Xs Ps) C') /\
                !Qs. (LENGTH Qs = LENGTH Xs) ==>
                      TRACE (CE n Qs) xs' (CCS_SUBST (fromList Xs Qs) C')`
      >- (Q.UNABBREV_TAC `CE` >> FULL_SIMP_TAC bool_ss [] \\
          irule USC_unfolding_lemma4 >> art [] \\
          CONJ_TAC >- (Q.EXISTS_TAC `Es` >> METIS_TAC []) \\
          Q.EXISTS_TAC `C` >> METIS_TAC []) >> STRIP_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) \\
     `LENGTH Qs = LENGTH Xs` by PROVE_TAC [CCS_solution_length] \\
      RW_TAC std_ss [] \\
     `OBS_contracts (C0 Qs) (CE n Qs)` by PROVE_TAC [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `WEAK_TRANS (CE n Qs) (label l) (CCS_SUBST (fromList Xs Qs) C')`
      >- (REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
          Q.EXISTS_TAC `xs'` >> art [] \\
          MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
          Q.EXISTS_TAC `label l` >> art []) >> DISCH_TAC \\
      RW_TAC std_ss [O_DEF] \\
      IMP_RES_TAC OBS_contracts_WEAK_TRANS_label' \\
      Q.EXISTS_TAC `E1` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE >> fs [] \\
     `OBS_contracts (C0 Ps) (CE (LENGTH us) Ps)` by PROVE_TAC [] \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`us`, `R`]) o
                 (MATCH_MP OBS_contracts_AND_TRACE_tau)) \\
      RW_TAC std_ss [] \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Know `?C'. context Xs C' /\
                (E2 = CCS_SUBST (fromList Xs Ps) C') /\
                !Qs. (LENGTH Qs = LENGTH Xs) ==>
                      TRACE (CE n Qs) xs' (CCS_SUBST (fromList Xs Qs) C')`
      >- (Q.UNABBREV_TAC `CE` >> FULL_SIMP_TAC bool_ss [] \\
          irule USC_unfolding_lemma4 >> art [] \\
          CONJ_TAC >- (Q.EXISTS_TAC `Es` >> METIS_TAC []) \\
          Q.EXISTS_TAC `C` >> METIS_TAC []) >> STRIP_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) \\
     `LENGTH Qs = LENGTH Xs` by PROVE_TAC [CCS_solution_length] \\
      RW_TAC std_ss [] \\
     `OBS_contracts (C0 Qs) (CE n Qs)` by PROVE_TAC [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `EPS (CE n Qs) (CCS_SUBST (fromList Xs Qs) C')`
      >- (REWRITE_TAC [EPS_AND_TRACE] \\
          Q.EXISTS_TAC `xs'` >> art []) >> DISCH_TAC \\
      RW_TAC std_ss [O_DEF] \\
      IMP_RES_TAC OBS_contracts_EPS' \\
      Q.EXISTS_TAC `E1` >> art [] ]
QED

(* This is a shared lemma for unique_solution_of_obs_contractions and
   unique_solution_of_rooted_contractions.
 *)
Theorem shared_lemma[local] :
   CCS_equation Xs Es /\
   EVERY (weakly_guarded Xs) Es /\
   CCS_solution OBS_contracts Xs Es Ps /\
   CCS_solution OBS_contracts Xs Es Qs
  ==>
   WEAK_BISIM (\R S. ?C. context Xs C /\
                         WEAK_EQUIV R (CCS_SUBST (fromList Xs Ps) C) /\
                         WEAK_EQUIV S (CCS_SUBST (fromList Xs Qs) C))
Proof
    rpt STRIP_TAC >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 (* compatible with symbols in UniqueSolutionsTheory.shared_lemma *)
 >> rename1 `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
 >> rename1 `WEAK_EQUIV E'  (CCS_SUBST (fromList Xs Ps) C)`
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (fromList Xs Ps) C)`
        (MP_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RW_TAC std_ss [] \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Ps`, `Qs`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      POP_ASSUM K_TAC (* !R. EPS _ R ==> _ *) \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`l`, `E2`])) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
        (MP_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      reverse CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
        (MP_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RW_TAC std_ss [] \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Qs`, `Ps`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      POP_ASSUM K_TAC (* !R. EPS _ R ==> _ *) \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`l`, `E2'`])) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (fromList Xs Ps) C)`
        (MP_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (from Xs Ps) C)`
        (MP_TAC o (Q.SPEC `E1`) o (MATCH_MP WEAK_EQUIV_TRANS_tau)) \\
      RW_TAC std_ss [] \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- (Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
          Q.EXISTS_TAC `C` >> art []) \\
      Q.PAT_X_ASSUM `EPS _ E2` K_TAC \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Ps`, `Qs`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS _ (label l) R => _` K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `E2`)) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
        (MP_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      reverse CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (from Xs Qs) C)`
        (MP_TAC o (Q.SPEC `E2`) o (MATCH_MP WEAK_EQUIV_TRANS_tau)) \\
      RW_TAC std_ss [] \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- (Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
          Q.EXISTS_TAC `C` >> art []) \\
      Q.PAT_X_ASSUM `EPS _ E2'` K_TAC \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Qs`, `Ps`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS _ (label l) R => _` K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `E2'`)) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (fromList Xs Ps) C)`
        (MP_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]
QED

(* Theorem 3.10 of [2], full version *)
Theorem unique_solution_of_obs_contractions :
    !Xs Es Ps Qs.
        CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
        Ps IN (CCS_solution OBS_contracts Xs Es) /\
        Qs IN (CCS_solution OBS_contracts Xs Es) ==> WEAK_EQUIV Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. context Xs C /\
                            WEAK_EQUIV R (CCS_SUBST (fromList Xs Ps) C) /\
                            WEAK_EQUIV S (CCS_SUBST (fromList Xs Qs) C)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.EXISTS_TAC `EL n Es` \\
     CONJ_TAC (* context Xs (EL n Es) *)
     >- (MATCH_MP_TAC weakly_guarded_imp_context \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         REWRITE_TAC [MEM_EL] \\
         Q.EXISTS_TAC `n` >> art []) \\
     CONJ_TAC \\ (* 2 subgoals, same initial tactic *)
     MATCH_MP_TAC OBS_contracts_IMP_WEAK_EQUIV >|
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!n. n < LENGTH Ps ==> X` (MP_TAC o (Q.SPEC `n`)) \\
       RW_TAC std_ss [] >> POP_ASSUM MP_TAC \\
       Know `EL n (MAP (CCS_SUBST (fromList Xs Ps)) Es) =
             CCS_SUBST (fromList Xs Ps) (EL n Es)`
       >- (MATCH_MP_TAC EL_MAP >> fs []) >> Rewr,
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!n. n < LENGTH Qs ==> X` (MP_TAC o (Q.SPEC `n`)) \\
       RW_TAC std_ss [] >> POP_ASSUM MP_TAC \\
       Know `EL n (MAP (CCS_SUBST (fromList Xs Qs)) Es) =
             CCS_SUBST (fromList Xs Qs) (EL n Es)`
       >- (MATCH_MP_TAC EL_MAP >> fs []) >> Rewr ])
 >> POP_ASSUM K_TAC (* `n` is useless *)
 >> MATCH_MP_TAC shared_lemma
 >> fs [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
QED

(* THE FINAL THEOREM (Theorem 3.16 of [3]) *)
Theorem unique_solution_of_rooted_contractions :
    !Xs Es Ps Qs.
        CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
        Ps IN (CCS_solution OBS_contracts Xs Es) /\
        Qs IN (CCS_solution OBS_contracts Xs Es) ==> OBS_CONGR Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss (* `std_ss` is not enough here *)
           [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
 (* here is the difference from unique_solution_of_obs_contractions *)
 >> irule OBS_CONGR_BY_WEAK_BISIM
 >> Q.EXISTS_TAC `\R S. ?C. context Xs C /\
                            WEAK_EQUIV R (CCS_SUBST (fromList Xs Ps) C) /\
                            WEAK_EQUIV S (CCS_SUBST (fromList Xs Qs) C)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.ABBREV_TAC `P = EL n Ps` \\
     Q.ABBREV_TAC `Q = EL n Qs` \\
     Q.ABBREV_TAC `E = EL n Es` \\
     Know `weakly_guarded Xs E`
     >- (Q.UNABBREV_TAC `E` >> FIRST_X_ASSUM MATCH_MP_TAC \\
         REWRITE_TAC [MEM_EL] >> Q.EXISTS_TAC `n` >> art []) \\
     rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `OBS_contracts P (CCS_SUBST (fromList Xs Ps) E)` by METIS_TAC [EL_MAP] \\
       IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
       MP_TAC (Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma) \\
      `MEM E Es` by PROVE_TAC [MEM_EL] \\
      `FV E SUBSET (set Xs)` by PROVE_TAC [] \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E2`])) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) >> RW_TAC std_ss [] \\
      `OBS_contracts Q (CCS_SUBST (fromList Xs Qs) E)` by METIS_TAC [EL_MAP] \\
       Q.PAT_X_ASSUM `OBS_contracts P (CCS_SUBST (fromList Xs Ps) E)` K_TAC \\
       IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
       Q.EXISTS_TAC `E1'` >> art [] \\
       Q.EXISTS_TAC `E'` >> art [] \\
       MATCH_MP_TAC contracts_IMP_WEAK_EQUIV >> art [],
       (* goal 2 (of 2) *)
      `OBS_contracts Q (CCS_SUBST (fromList Xs Qs) E)` by METIS_TAC [EL_MAP] \\
       IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
       MP_TAC (Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma) \\
      `MEM E Es` by PROVE_TAC [MEM_EL] \\
      `FV E SUBSET (set Xs)` by PROVE_TAC [] \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E2'`])) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
      `OBS_contracts P (CCS_SUBST (fromList Xs Ps) E)` by METIS_TAC [EL_MAP] \\
       Q.PAT_X_ASSUM `OBS_contracts Q (CCS_SUBST (fromList Xs Qs) E)` K_TAC \\
       IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
       rename1 `WEAK_TRANS P u E1'` \\
       Q.EXISTS_TAC `E1'` >> art [] \\
       Q.EXISTS_TAC `E'` >> art [] \\
       MATCH_MP_TAC contracts_IMP_WEAK_EQUIV >> art [] ])
 >> POP_ASSUM K_TAC (* `n` is useless *)
 >> MATCH_MP_TAC shared_lemma
 >> fs [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
QED

val _ = export_theory ();
val _ = html_theory "Multivariate";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.

 [2] Sangiorgi, Davide. "Equations, contractions, and unique
     solutions." ACM Transactions on Computational Logic (TOCL) 18.1
     (2017): 4. (DOI: 10.1145/2971339)

 [3] C. Tian and D. Sangiorgi, “Unique solutions of contractions, CCS, and
     their HOL formalisation,” Inf. Comput., vol. 275, p. 104606, Dec. 2020.

 [4] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory.
     Springer, Cham (2015).

 *)
