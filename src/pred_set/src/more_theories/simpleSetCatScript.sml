open HolKernel Parse boolLib bossLib;
open relationTheory combinTheory pred_setTheory cardinalTheory

val _ = new_theory "simpleSetCat";

val _ = app (ignore o hide) ["S", "W"]


Definition restr_def:
  restr f s = \x. if x IN s then f x else ARB
End

Theorem restr_applies:
  x IN A ==> (restr f A x = f x)
Proof
  simp[restr_def]
QED

Theorem IN_UNCURRY[simp]:
  (a,b) IN UNCURRY R <=> R a b
Proof
  simp[IN_DEF]
QED
Definition Delta_def[simp]:
  Delta V a b <=>  a = b /\ a IN V
End
Overload "Δ" = “Delta”                                                 (* UOK *)

Theorem Delta_INTER:
  Delta (s INTER t) = Delta s RINTER Delta t
Proof
  simp[FUN_EQ_THM, RINTER] >> metis_tac[]
QED


Definition Gr_def[simp]:
  Gr h A a b <=> a IN A /\ b = h a
End

Theorem Gr_Id[simp]:
  Gr (\x. x) A = Delta A
Proof
  csimp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem Gr_restr[simp]:
  Gr (restr f A) A = Gr f A
Proof
  csimp[FUN_EQ_THM, restr_def]
QED


Definition span_def[simp]:
  span A f g b d <=> ?a. a IN A /\ b = f a /\ d = g a
End

Definition kernel_def[simp]:
  kernel A f x y <=> x IN A /\ y IN A /\ f x = f y
End

Theorem kernel_graph:
  kernel A f = inv (Gr f A) O Gr f A
Proof
  simp[FUN_EQ_THM, O_DEF]
QED


Definition RIMAGE_def:
  RIMAGE f A R x y <=>
  ?x0 y0. x = f x0 /\ y = f y0 /\ R x0 y0 /\ x0 IN A /\ y0 IN A
End

Definition RINV_IMAGE_def:
  RINV_IMAGE f A R x y <=> x IN A /\ y IN A /\ R (f x) (f y)
End

Theorem RIMAGE_Gr:
  RIMAGE f A R = Gr f A O R O inv (Gr f A)
Proof
  dsimp[FUN_EQ_THM, O_DEF, IN_DEF, PULL_EXISTS, RIMAGE_def] >>
  metis_tac[]
QED

Theorem Delta_IMAGE:
  Delta (IMAGE f A) = RIMAGE f A (Delta A)
Proof
  simp[FUN_EQ_THM, PULL_EXISTS, RIMAGE_def] >> metis_tac[]
QED

Theorem RINV_IMAGE_Gr:
  RINV_IMAGE f A R = inv (Gr f A) O R O Gr f A
Proof
  dsimp[FUN_EQ_THM, O_DEF, RINV_IMAGE_def] >> metis_tac[]
QED

Theorem restr_restr_o[simp]:
  restr (f o restr g A) A = restr (f o g) A
Proof
  simp[restr_def, FUN_EQ_THM]
QED

Theorem restr_cases:
  restr f A x = g x <=> x IN A /\ f x = g x \/  x NOTIN A /\ g x = ARB
Proof
  simp[restr_def] >> metis_tac[]
QED


Theorem oID[simp]:
  f o (\x.x) = f /\ (\x.x) o f = f
Proof
  simp[FUN_EQ_THM]
QED

Definition shom_def:
  shom f A B <=> (!a. a IN A ==> f a IN B) /\ !a. a NOTIN A ==> f a = ARB
End

(* pushouts in Set *)

Definition Spushout_def:
  Spushout (A:'a set) (B:'b set) (C:'c set) f g (P:'p set,i1,i2) (:'d) <=>
  shom f A B /\ shom g A C /\ shom i1 B P /\ shom i2 C P /\
  restr (i1 o f) A = restr (i2 o g) A /\
  !(Q:'d set) j1 j2.
    shom j1 B Q /\ shom j2 C Q /\ restr (j1 o f) A = restr (j2 o g) A ==>
    ?!u. shom u P Q /\ restr (u o i1) B = j1 /\ restr (u o i2) C = j2
End

Definition SPO_pimg_def[simp]:
  SPO_pimg A f g (INL x) = PREIMAGE f {x} INTER A /\
  SPO_pimg A f g (INR y) = PREIMAGE g {y} INTER A
End

Definition SPOr_def:
  SPOr A f g = EQC (\x y. (?a. a IN A /\ x = INL (f a) /\ y = INR (g a)) \/
                          x = y)
End

Definition SPO_def:
  SPO A B C f g =
    (partition (SPOr A f g) (B <+> C),
     restr (\b. { a | a IN B <+> C /\ SPOr A f g (INL b) a }) B,
     restr (\c. { a | a IN B <+> C /\ SPOr A f g (INR c) a }) C)
End

Theorem symmetric_SPOr[simp]:
  symmetric (SPOr A f g)
Proof
  rw[SPOr_def, symmetric_EQC]
QED

Theorem transitive_SPOr[simp]:
  transitive (SPOr A f g)
Proof
  simp[SPOr_def, transitive_EQC]
QED

Theorem SPOr_lemma0[local]:
  restr (j1 o f) A = restr (j2 o g) A ==>
  !s1 s2. SPOr A f g s1 s2 ==>
          (!b1 b2. s1 = INL b1 /\ s2 = INL b2 ==> j1 b1 = j1 b2) /\
          (!b c. s1 = INL b /\ s2 = INR c ==> j1 b = j2 c) /\
          (!b c. s1 = INR c /\ s2 = INL b ==> j1 b = j2 c) /\
          (!c1 c2. s1 = INR c1 /\ s2 = INR c2 ==> j2 c1 = j2 c2)
Proof
  strip_tac >> simp[SPOr_def] >> Induct_on ‘EQC’ >> rw[]
  >- (fs[restr_def, FUN_EQ_THM] >> metis_tac[])
  >- (rename [‘EQC _ (INL b1) s’, ‘EQC _ s (INL b2)’] >>
      Cases_on ‘s’ >> fs[])
  >- (rename [‘EQC _ (INL b) s’, ‘EQC _ s (INR c)’] >>
      Cases_on ‘s’ >> fs[])
  >- (rename [‘EQC _ (INR c) s’, ‘EQC _ s (INL b)’] >>
      Cases_on ‘s’ >> fs[])
  >- (rename [‘EQC _ (INR c1) s’, ‘EQC _ s (INR c2)’] >>
      Cases_on ‘s’ >> fs[])
QED

Theorem SPOr_lemma =
  SPOr_lemma0 |> UNDISCH
              |> SIMP_RULE (srw_ss()) [IMP_CONJ_THM, PULL_FORALL]
              |> SIMP_RULE (srw_ss()) [FORALL_AND_THM]
              |> DISCH_ALL

Theorem SPOr_REFL[simp]:
  SPOr A f g x x
Proof
  simp[SPOr_def]
QED

Theorem Spushout_quotient:
  shom f A B /\ shom g A C ==>
  Spushout (A:'a set) (B:'b set) (C:'c set) f g (SPO A B C f g) (:'d)
Proof
  simp[Spushout_def, SPO_def] >> rw[]
  >- (simp[shom_def] >> reverse conj_tac >- simp[restr_def] >>
      dsimp[restr_applies, partition_def] >> csimp[] >>
      qx_gen_tac ‘b’ >> strip_tac >> qexists_tac ‘INL b’ >> simp[] >>
      simp[EXTENSION] >>
      ‘symmetric (SPOr A f g)’ suffices_by metis_tac[symmetric_def] >>
      simp[])
  >- (simp[shom_def] >> reverse conj_tac >- simp[restr_def] >>
      dsimp[restr_applies, partition_def] >> csimp[] >>
      qx_gen_tac ‘c’ >> strip_tac >>
      qexists_tac ‘INR c’ >> simp[EXTENSION] >>
      ‘symmetric (SPOr A f g)’ suffices_by metis_tac[symmetric_def] >>
      simp[])
  >- (simp[Once FUN_EQ_THM, restr_def] >> qx_gen_tac ‘a’ >> rw[]
      >- (simp[Once EXTENSION] >> qx_gen_tac ‘s’ >>
          ‘SPOr A f g (INL (f a)) (INR (g a)) /\ symmetric (SPOr A f g) /\
           transitive (SPOr A f g)’
            suffices_by metis_tac[symmetric_def, transitive_def] >>
          simp[] >> simp[SPOr_def] >> irule EQC_R >> simp[] >> metis_tac[]) >>
      metis_tac[shom_def]) >>
  ONCE_REWRITE_TAC[FUN_EQ_THM] >>
  simp[o_ABS_R] >> simp[EXISTS_UNIQUE_ALT] >>
  qexists_tac ‘restr (\p. case some a. INL a IN p of
                            SOME a => j1 a
                          | NONE => j2 (CHOICE {b | INR b IN p}))
               (partition (SPOr A f g) (B <+> C))’ >>
  qx_gen_tac ‘u’ >>
  reverse (Cases_on ‘shom u (partition (SPOr A f g) (B <+> C)) Q’)
  >- (simp[] >> pop_assum mp_tac >> simp[shom_def] >> strip_tac
      >- (ONCE_REWRITE_TAC [FUN_EQ_THM] >> simp[] >>
          rename [‘a IN partition _ _’, ‘u a NOTIN Q’] >>
          qexists_tac ‘a’ >> simp[restr_applies] >>
          disch_then (assume_tac o SYM) >> fs[] >>
          qpat_x_assum ‘_ NOTIN Q’ mp_tac >> simp[] >>
          DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
          qpat_x_assum ‘_ IN partition _ _’ mp_tac >>
          simp[partition_def, sumTheory.EXISTS_SUM] >> strip_tac >> rw[]
          >- metis_tac[shom_def]
          >- metis_tac[SPOr_REFL]
          >- metis_tac[shom_def] >>
          DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >> conj_tac
          >- metis_tac[SPOr_REFL] >>
          metis_tac[shom_def]) >>
      ONCE_REWRITE_TAC [FUN_EQ_THM] >> simp[]>> rename [‘u a <> ARB’] >>
      qexists_tac ‘a’ >> simp[restr_def]) >>
  ONCE_REWRITE_TAC [FUN_EQ_THM] >> simp[restr_cases] >>
  ‘(!b. b NOTIN B ==> j1 b = ARB) /\ (!c. c NOTIN C ==> j2 c = ARB) /\
   (!p. p NOTIN partition (SPOr A f g) (B <+> C) ==> u p = ARB)’
    by metis_tac[shom_def] >> csimp[] >>
  simp[DECIDE “p /\ q \/ ~p <=> q \/ ~p”] >>
  simp[DECIDE “p \/ ~q <=> q ==> p”] >> eq_tac
  >- (simp[partition_def, PULL_EXISTS, sumTheory.FORALL_SUM] >>
      strip_tac >> qx_gen_tac ‘p’ >> conj_tac
      >- (qx_gen_tac ‘b’>> rw[] >>
          DEEP_INTRO_TAC optionTheory.some_intro >> reverse (rw[])
          >- metis_tac[SPOr_REFL] >>
          rename [‘SPOr _ _ _ (INL b1) (INL b2)’] >> Cases_on ‘b1 = b2’ >>
          simp[] >> metis_tac[SPOr_lemma]) >>
      qx_gen_tac ‘c’ >> rw[] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[]
      >- metis_tac[SPOr_lemma] >>
      DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >>
      metis_tac[SPOr_REFL, SPOr_lemma]) >>
  simp[partition_def, PULL_EXISTS, sumTheory.FORALL_SUM, FORALL_AND_THM] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) >> simp[] >>
  disch_then (K ALL_TAC) >> rw[]
  >- (DEEP_INTRO_TAC optionTheory.some_intro >> reverse (rw[])
      >- metis_tac[SPOr_REFL] >> metis_tac[SPOr_lemma]) >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >> conj_tac
  >- metis_tac[SPOr_lemma] >> strip_tac >>
  DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >> metis_tac[SPOr_REFL, SPOr_lemma]
QED

(* pushouts in Set into universe delta are pushouts into universe epsilon if
   epsilon is no bigger than delta *)
Theorem Spushout_transfer:
  Spushout A B C f g (P,i1,i2) (:'d) /\ INJ h univ(:'e) univ(:'d) ==>
  Spushout A B C f g (P,i1,i2) (:'e)
Proof
  rw[Spushout_def] >>
  first_x_assum $ qspecl_then [‘IMAGE h Q’, ‘restr (h o j1) B’,
                               ‘restr (h o j2) C’] mp_tac >>
  impl_tac
  >- (fs[shom_def, restr_def, FUN_EQ_THM] >> metis_tac[INJ_IFF, IN_UNIV]) >>
  simp[EXISTS_UNIQUE_THM] >> rw[]
  >- (drule_then assume_tac LINV_DEF >> fs[] >>
      qexists_tac ‘restr (LINV h univ(:'e) o u) P’>>
      first_x_assum $ qspecl_then [‘ARB’, ‘ARB’] (K ALL_TAC) >>
      fs[shom_def, FUN_EQ_THM, restr_def] >> rw[] >> metis_tac[]) >>
  Q.MATCH_RENAME_TAC ‘u1 = u2’ >>
  first_x_assum $ qspecl_then [‘restr (h o u1) P’, ‘restr (h o u2) P’] mp_tac >>
  impl_tac
  >- (fs[shom_def, FUN_EQ_THM, restr_def] >> rw[] >> metis_tac[]) >>
  rw[FUN_EQ_THM, restr_def] >> metis_tac[shom_def, INJ_IFF, IN_UNIV]
QED

Theorem shoms_exist:
  !(A:'a set) (B:'b set). B <> {} ==> ?h. shom h A B
Proof
  rw[shom_def] >> qexists_tac ‘restr (K (CHOICE B)) A’ >>
  rw[restr_def, CHOICE_DEF]
QED

Theorem unit_pushout:
  shom f A B /\ shom g A C /\ A <> {} ==>
  Spushout A B C f g ({()}, restr (K ()) B, restr (K ()) C) (:unit)
Proof
  simp[shom_def, Spushout_def, FUN_EQ_THM] >> rw[] >>
  simp[EXISTS_UNIQUE_DEF, FUN_EQ_THM]>> fs[IN_DEF] >> metis_tac[]
QED

Theorem Spushout_sym:
  Spushout A B C f g (P,p1,p2) (:'d) ==>
  Spushout A C B g f (P,p2,p1) (:'d)
Proof
  simp[Spushout_def] >> metis_tac[]
QED

Theorem shom_into_EMPTY[simp]:
 shom f A {} <=> A = {} /\ f = K ARB
Proof
  csimp[shom_def] >> simp[FUN_EQ_THM, IN_DEF]
QED

Theorem shom_outof_EMPTY[simp]:
  shom f {} A <=> f = K ARB
Proof
  simp[shom_def, FUN_EQ_THM]
QED

Theorem restr_EMPTY[simp]:
  restr f {} = K ARB
Proof
  simp[FUN_EQ_THM, restr_def]
QED

Definition cardgt_def:
  cardgt (:'a) n <=> FINITE univ(:'a) ==> n < CARD univ(:'a)
End

Theorem cardgt0[simp]:
  cardgt (:'a) 0
Proof
  simp[cardgt_def] >> CCONTR_TAC >> fs[] >> rfs[]
QED

Theorem cardgt1_INJ_bool:
  cardgt (:'a) 1 <=> ?bf. INJ bf {T;F} univ(:'a)
Proof
  simp[cardgt_def] >> eq_tac >> strip_tac >> fs[INJ_IFF]
  >- (‘?x. x IN univ(:'a)’ by simp[] >>
      ‘?y. y IN univ(:'a) /\ x <> y’
        by (CCONTR_TAC >> fs[] >>
            ‘univ(:'a) = {x}’ by simp[EXTENSION] >>
            pop_assum SUBST_ALL_TAC >>
            fs[]) >>
      qexists_tac ‘\b. if b then x else y’ >> rw[]) >>
  rw[] >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac ‘CARD {bf T; bf F}’ >> conj_tac >- simp[] >>
  irule CARD_SUBSET >> simp[]
QED

Theorem Spushouts_iso:
  Spushout (A:'a set) (B:'b set) (C:'c set) f g (P : 'd set,i1,i2) (:'e) /\
  Spushout A B C f g (Q : 'e set,j1,j2) (:'d) /\
  cardgt (:'d) 1 /\ cardgt (:'e) 1 ==>
  ?H. BIJ H P Q /\ restr (H o i1) B = j1 /\ restr (H o i2) C = j2
Proof
  rw[Spushout_def] >>
  first_assum $ drule_all >>
  last_assum $ drule_all >>
  REWRITE_TAC[EXISTS_UNIQUE_DEF] >> simp[] >>
  disch_then $ CONJUNCTS_THEN2 (qx_choose_then ‘pq’ strip_assume_tac)
             strip_assume_tac >>
  disch_then $ CONJUNCTS_THEN2 (qx_choose_then ‘qp’ strip_assume_tac)
             strip_assume_tac >>
  Cases_on ‘P = {}’ >> fs[] >> Cases_on ‘Q = {}’ >> fs[] >>
  ‘SURJ pq P Q’
    by (CCONTR_TAC >>
        ‘?q. q IN Q /\ !p. p IN P ==> pq p <> q’
          by (fs[SURJ_DEF, shom_def] >> metis_tac[]) >>
        ‘(!b. b IN B ==> j1 b <> q) /\ (!c. c IN C ==> j2 c <> q)’
          by (qpat_x_assum ‘_ = j1’ (SUBST_ALL_TAC o SYM) >>
              qpat_x_assum ‘_ = j2’ (SUBST_ALL_TAC o SYM) >>
              simp[restr_applies] >> metis_tac[shom_def]) >>
        ‘qp q IN P’ by metis_tac[shom_def] >>
        Cases_on ‘?p. p IN P /\ p <> qp q’
        >- (fs[] >>
            qabbrev_tac ‘qp' = \q0. if q0 = q then p else qp q0’ >>
            ‘shom qp' Q P’ by (fs[shom_def, Abbr‘qp'’] >> metis_tac[]) >>
            ‘restr (qp' o j1) B = i1 /\ restr (qp' o j2) C = i2’
              by (simp[FUN_EQ_THM, restr_def, Abbr‘qp'’] >>
                  qpat_x_assum ‘_ = i1’ (SUBST_ALL_TAC o SYM) >>
                  qpat_x_assum ‘_ = i2’ (SUBST_ALL_TAC o SYM) >>
                  simp[restr_def]) >>
            ‘qp' = qp’ by metis_tac[] >>
            pop_assum mp_tac >>
            simp_tac (srw_ss()) [Abbr‘qp'’, FUN_EQ_THM] >> metis_tac[]) >>
        fs[] >>
        ‘P = {qp q}’ by (simp[EXTENSION] >> metis_tac[]) >>
        ‘?p. p NOTIN P’
          by (‘?bf. INJ bf {T;F} univ(:'d)’ by metis_tac[cardgt1_INJ_bool] >>
              Cases_on ‘bf T = qp q’
              >- (qexists_tac‘bf F’ >> simp[] >> fs[INJ_IFF] >>
                  disch_then (assume_tac o SYM) >> fs[] >> rfs[]) >>
              qexists_tac ‘bf T’ >> simp[]) >>
        first_x_assum $ qspecl_then [‘{qp q; p}’, ‘i1’, ‘i2’] mp_tac >>
        impl_tac >- (simp[] >> fs[shom_def]) >>
        strip_tac >> fs[EXISTS_UNIQUE_DEF] >>
        ‘?v. shom v Q {qp q; p} /\ restr (v o j1) B = i1 /\
             restr (v o j2) C = i2 /\ v <> u’ suffices_by metis_tac[] >>
        qexists_tac
          ‘\q0. if q0 = q then if u q = p then qp q else p else u q0’ >>
        simp[FUN_EQ_THM, restr_def] >> rpt strip_tac
        >- (fs[shom_def, AllCaseEqs()] >> metis_tac[])
        >- (qpat_x_assum ‘_ = i1’ (SUBST_ALL_TAC o SYM) >> simp[restr_def])
        >- (qpat_x_assum ‘_ = i2’ (SUBST_ALL_TAC o SYM) >> simp[restr_def])
        >- (qexists_tac ‘q’ >> rw[] >> fs[])) >>
  ‘!p. p IN P ==> (?b. b IN B /\ i1 b = p) \/ (?c. c IN C /\ i2 c = p)’
    by (CCONTR_TAC >> fs[] >>
        Cases_on ‘?q. q IN Q /\ pq p <> q’ >> fs[]
        >- (qabbrev_tac ‘v = \p0. if p0 = p then q else pq p0’ >>
            ‘shom v P Q’ by (fs[shom_def, Abbr‘v’] >> metis_tac[]) >>
            ‘v <> pq’ by (simp[Abbr‘v’, FUN_EQ_THM] >> metis_tac[]) >>
            ‘restr (v o i1) B = j1 /\ restr (v o i2) C = j2’
              suffices_by metis_tac[] >>
            qpat_x_assum ‘_ = j1’ (SUBST_ALL_TAC o SYM) >>
            qpat_x_assum ‘_ = j2’ (SUBST_ALL_TAC o SYM) >>
            simp[FUN_EQ_THM, Abbr‘v’, restr_def] >> metis_tac[]) >>
        ‘Q = {pq p}’ by (simp[EXTENSION] >> metis_tac[SURJ_DEF]) >>
        ‘?q. q NOTIN Q’
          by (‘?bf. INJ bf {T;F} univ(:'e)’ by metis_tac[cardgt1_INJ_bool] >>
              Cases_on ‘bf T = pq p’
              >- (qexists_tac‘bf F’ >> simp[] >> fs[INJ_IFF] >>
                  disch_then (assume_tac o SYM) >> fs[] >> rfs[]) >>
              qexists_tac ‘bf T’ >> simp[]) >>
        first_x_assum $ qspecl_then [‘{pq p; q}’, ‘j1’, ‘j2’] mp_tac >>
        impl_tac >- (simp[] >> fs[shom_def]) >>
        strip_tac >> fs[EXISTS_UNIQUE_DEF] >>
        ‘?v. shom v P {pq p; q} /\ restr (v o i1) B = j1 /\
             restr (v o i2) C = j2 /\ v <> u’ suffices_by metis_tac[] >>
        qexists_tac
        ‘\p0. if p0 = p then if u p = q then pq p else q else u p0’ >>
        simp[FUN_EQ_THM, restr_def] >> rpt strip_tac
        >- (fs[shom_def, AllCaseEqs()] >> metis_tac[])
        >- (qpat_x_assum ‘_ = j1’ (SUBST_ALL_TAC o SYM) >> simp[restr_def] >>
            metis_tac[])
        >- (qpat_x_assum ‘_ = j2’ (SUBST_ALL_TAC o SYM) >> simp[restr_def] >>
            metis_tac[])
        >- (qexists_tac ‘p’ >> rw[] >> fs[])) >>
  qexists_tac ‘pq’ >> simp[BIJ_DEF] >>
  simp[INJ_IFF] >> conj_tac >- metis_tac[shom_def] >>
  ‘!p. p IN P ==> qp (pq p) = p’ suffices_by metis_tac[] >>
  qx_gen_tac ‘p’ >> strip_tac >> first_x_assum drule >> strip_tac
  >- (pop_assum (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum ‘_ = i1’ (fn th => simp[SYM th, SimpRHS]) >>
      qpat_x_assum ‘_ = j1’ (SUBST_ALL_TAC o SYM)>>
      simp[restr_applies]) >>
  pop_assum (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘_ = i2’ (fn th => simp[SYM th, SimpRHS]) >>
  qpat_x_assum ‘_ = j2’ (SUBST_ALL_TAC o SYM)>>
  simp[restr_applies]
QED

(* eps R A a, injects a (from set A) into a's equivalence class with
   respect to relation R
*)
Definition eps_def:
  eps R A a = if a IN A then {b | R a b /\ b IN A} else ARB
End

Theorem eps_partition:
  a IN A ==> eps R A a IN partition R A
Proof
  simp[eps_def, partition_def] >> strip_tac >>
  qexists_tac ‘a’ >> simp[EXTENSION] >> metis_tac[]
QED



val _ = export_theory();
