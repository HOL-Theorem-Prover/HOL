Theory bnfMutual
Ancestors
  bnfFixBNF pred_set
Libs
  HolKernel Parse boolLib bossLib

(* ----------------------------------------------------------------------
    Mutual recursion, from nested recursion.

    A mutually recursive pair arrives from the specification as one
    functor per type with the sibling as an extra argument:

        T1 = F1(T1, T2)        T2 = F2(T2, T1)

    Nothing new has to be constructed for it.  Take T2's fixed point with
    the *sibling's* slot left as a parameter — an ordinary datatype,
    T2' α — and then define

        T1 = μβ. F1(β, T2' β)        T2 = T2' T1

    which is a recursion nested through T2', and that already works.  What
    is left is to turn the nested recursion principle for T1, and T2''s
    own, into the principle for the pair, and that is what is proved here
    — once, over parameters, so no datatype replays it.

    Throughout, 'n1 and 'n2 are the two types and 'c1 and 'c2 the answer
    types a pair of functions maps them to; 'm2 is T2' 'c1, the sibling's
    type over the answers rather than over T1.  smap is T2''s map in that
    argument, which is where the two recursions meet.
   ---------------------------------------------------------------------- *)

(* the equations a pair of functions defined by mutual recursion
   satisfies: each type's constructor takes a value of that type's functor,
   whose occurrences of *either* type have been mapped by the
   corresponding function *)
Definition MUTREC_def:
  MUTREC (cn1 : 'fn1 -> 'n1) (cn2 : 'fn2 -> 'n2) mpK mpQ t1 t2 h1 h2 ⇔
    (∀af. h1 (cn1 af) = t1 (mpK h1 h2 af)) ∧
    (∀af. h2 (cn2 af) = t2 (mpQ h1 h2 af))
End

(* the recursion principle a type's own construction produced, as a
   predicate: the map is the one over that type's functor, so the
   hypotheses below can name it *)
Definition SREC_def:
  SREC (cn : 'f -> 'n) (mp : ('n -> 'c) -> 'f -> 'g) ⇔
    ∀t. ∃!h. ∀af. h (cn af) = t (mp h af)
End

(* and the sibling's map, at every function it might be given: not
   FIXMAP, because the map operator here is the sibling's map itself
   rather than a parameter to be solved for *)
Definition SMAP_def:
  SMAP (cn2 : 'fn2 -> 'n2) cm2 mpBg smap ⇔
    ∀g af. smap g (cn2 af) = cm2 (mpBg g af)
End

(* the principle a pair of types has once the reduction is done: for any
   pair of target functions there is exactly one pair of functions
   satisfying the two equations *)
Definition MUTITER_def:
  MUTITER (cn1 : 'fn1 -> 'n1) (cn2 : 'fn2 -> 'n2) mpK mpQ ⇔
    ∀t1 t2.
      (∃h1 h2. MUTREC cn1 cn2 mpK mpQ t1 t2 h1 h2) ∧
      ∀h1 h2 k1 k2.
        MUTREC cn1 cn2 mpK mpQ t1 t2 h1 h2 ∧
        MUTREC cn1 cn2 mpK mpQ t1 t2 k1 k2 ⇒ h1 = k1 ∧ h2 = k2
End

(* Mapping a functor's own argument and then the sibling's answers is
   mapping both at once, with the sibling's map composed in.  Both
   functors need this, in the same shape: for F1 the first map is its own
   recursion, and for F2 it is the sibling's map at the same time. *)
Definition MUTMAP_def:
  MUTMAP (mpG : ('n1 -> 'c1) -> 'fn1 -> 'fg1) mpH mpK smap ⇔
    ∀g k af. mpH k (mpG g af) = mpK g (k o smap g) af
End

(* the two functors' composition laws, as rewrites in either direction:
   the map through the sibling is what has to be introduced on one side
   and eliminated on the other *)
val f1fwd = qpat_assum ‘MUTMAP mpG mpH mpK smap’
              (fn th => REWRITE_TAC[SRULE [MUTMAP_def] th])
val f1bwd = qpat_assum ‘MUTMAP mpG mpH mpK smap’
              (fn th => REWRITE_TAC[GSYM (SRULE [MUTMAP_def] th)])
val f2bwd = qpat_assum ‘MUTMAP mpBg mp2c mpQ smap’
              (fn th => REWRITE_TAC[GSYM (SRULE [MUTMAP_def] th)])

(* mapping a functor's own argument and the sibling's separately is
   mapping both at once *)
Definition MUTSPLIT_def:
  MUTSPLIT (mpQ : ('n1 -> 'c1) -> ('n2 -> 'c2) -> 'fn2 -> 'fc2) mp1a mp2n ⇔
    ∀g k af. mpQ g k af = mp1a g (mp2n k af)
End

Theorem MUTUAL_RECURSION:
  (* T1's recursion, nested through the sibling *)
  SREC cn1 mpG ∧
  (* the sibling's own recursion, over the answers and over T1 *)
  SREC cm2 mp2c ∧ SREC cn2 mp2n ∧
  (* the sibling's map, and the functors' composition laws *)
  SMAP cn2 cm2 mpBg smap ∧
  MUTMAP mpG mpH mpK smap ∧ MUTMAP mpBg mp2c mpQ smap ∧
  MUTSPLIT mpQ mp1a mp2n ⇒
  MUTITER cn1 cn2 mpK mpQ
Proof
  simp[MUTITER_def] >> strip_tac >>
  (* the predicates are there so that a driver's facts can be matched
     against them; the proof wants what they say *)
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [SREC_def, SMAP_def, MUTSPLIT_def]) >>
  rpt gen_tac >>
  (* the fold over the sibling's structure that the answers call for *)
  qpat_assum ‘∀s. ∃!k. ∀af. k (cm2 af) = s (mp2c k af)’
    (qspec_then ‘t2’ (strip_assume_tac o SRULE[EXISTS_UNIQUE_THM])) >>
  rename [‘∀af. fold (cm2 af) = t2 (mp2c fold af)’] >>
  (* whatever T1's function is, the sibling's is that fold after it *)
  ‘∀g af. (fold o smap g) (cn2 af) = t2 (mpQ g (fold o smap g) af)’
    by (rpt gen_tac >> f2bwd >> simp[]) >>
  ‘∀h1 h2. (∀af. h2 (cn2 af) = t2 (mpQ h1 h2 af)) ⇒ h2 = fold o smap h1’
    by (rpt strip_tac >>
        qpat_assum ‘∀s. ∃!k. ∀af. k (cn2 af) = s (mp2n k af)’
          (qspec_then ‘t2 o mp1a h1’
             (strip_assume_tac o SRULE[EXISTS_UNIQUE_THM])) >>
        first_x_assum irule >> simp[]) >>
  (* and T1's is the solution of its own recursion at that fold *)
  qpat_assum ‘∀t. ∃!h. ∀af. h (cn1 af) = t (mpG h af)’
    (qspec_then ‘t1 o mpH fold’
       (strip_assume_tac o SRULE[EXISTS_UNIQUE_THM])) >>
  rename [‘∀af. hh (cn1 af) = t1 (mpH fold (mpG hh af))’] >>
  (* so there is only one solution, and this is it *)
  ‘∀h1 h2. MUTREC cn1 cn2 mpK mpQ t1 t2 h1 h2 ⇒
           h1 = hh ∧ h2 = fold o smap hh’
    by (simp[MUTREC_def] >> rpt gen_tac >> strip_tac >>
        ‘h2 = fold o smap h1’
          by (qpat_assum ‘∀h1 h2. (∀af. h2 (cn2 af) = _) ⇒ _’ irule >>
              simp[]) >>
        ‘h1 = hh’
          by (qpat_assum ‘∀h h'. (∀af. h (cn1 af) = t1 (mpH fold _)) ∧ _ ⇒ _’
                irule >> simp[] >> qx_gen_tac ‘af’ >> f1fwd >> simp[]) >>
        simp[]) >>
  conj_tac
  >- (qexistsl_tac [‘hh’, ‘fold o smap hh’] >> simp[MUTREC_def] >>
      qx_gen_tac ‘af’ >> f1bwd >> simp[]) >>
  rpt gen_tac >> strip_tac >> res_tac >> simp[]
QED

(* ----------------------------------------------------------------------
    Mutual induction.

    Each type's own principle covers *its* sub-terms, and the two are
    tied together by the second type's set function for the first type's
    slot: the values of one type inside a value of the other.  What the
    pair's principle needs beyond the two is that this set decomposes the
    way the nesting says — the first type's own sub-terms are its direct
    occurrences together with those the sibling holds.
   ---------------------------------------------------------------------- *)

Definition NESTSET_def:
  NESTSET (stn1 : 'fn1 -> 'n1 set) sb1 sa1 S21 ⇔
    ∀af. stn1 af = sb1 af ∪ BIGUNION (IMAGE S21 (sa1 af))
End

Theorem MUTUAL_INDUCTION:
  FIXIND cn1 stn1 ∧ FIXIND cn2 st2 ∧
  NESTSET stn1 sb1 sa1 S21 ∧ FIXSET cn2 st2 sb2 S21 ⇒
  ∀P1 P2.
    (∀af. (∀y. y ∈ sb1 af ⇒ P1 y) ∧ (∀z. z ∈ sa1 af ⇒ P2 z) ⇒ P1 (cn1 af)) ∧
    (∀af. (∀y. y ∈ sb2 af ⇒ P1 y) ∧ (∀z. z ∈ st2 af ⇒ P2 z) ⇒ P2 (cn2 af)) ⇒
    (∀n. P1 n) ∧ ∀m. P2 m
Proof
  strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [FIXIND_def, FIXSET_def, NESTSET_def]) >>
  rpt gen_tac >> strip_tac >>
  (* a value of the second type satisfies P2 once the first type's values
     inside it satisfy P1 — which is its own induction *)
  ‘∀m. (∀y. y ∈ S21 m ⇒ P1 y) ⇒ P2 m’
    by (qpat_assum ‘∀P. (∀af. (∀z. z ∈ st2 af ⇒ P z) ⇒ P (cn2 af)) ⇒ ∀m. P m’
          ho_match_mp_tac >>
        rpt strip_tac >>
        qpat_assum ‘∀af. (∀y. y ∈ sb2 af ⇒ P1 y) ∧ _ ⇒ _’ irule >> conj_tac
        >- (rpt strip_tac >>
            qpat_assum ‘∀y. y ∈ S21 (cn2 af) ⇒ P1 y’ irule >> simp[]) >>
        rpt strip_tac >>
        qpat_assum ‘∀m. m ∈ st2 af ⇒ _ ⇒ P2 m’ (drule_then irule) >>
        rpt strip_tac >>
        qpat_assum ‘∀y. y ∈ S21 (cn2 af) ⇒ P1 y’ irule >> simp[] >>
        disj2_tac >> qexists_tac ‘S21 z’ >> simp[] >> qexists_tac ‘z’ >>
        simp[]) >>
  (* and then the first type's own induction covers both *)
  ‘∀n. P1 n’
    by (qpat_assum ‘∀P. (∀af. (∀y. y ∈ stn1 af ⇒ P y) ⇒ P (cn1 af)) ⇒ ∀n. P n’
          ho_match_mp_tac >>
        rpt strip_tac >>
        qpat_assum ‘∀af. (∀y. y ∈ sb1 af ⇒ P1 y) ∧ _ ⇒ _’ irule >> conj_tac
        >- (rpt strip_tac >>
            qpat_assum ‘∀y. y ∈ stn1 af ⇒ P1 y’ irule >> simp[]) >>
        rpt strip_tac >>
        qpat_assum ‘∀m. (∀y. y ∈ S21 m ⇒ P1 y) ⇒ P2 m’ irule >>
        rpt strip_tac >>
        qpat_assum ‘∀y. y ∈ stn1 af ⇒ P1 y’ irule >> simp[] >>
        disj2_tac >> qexists_tac ‘S21 z’ >> simp[] >> qexists_tac ‘z’ >>
        simp[]) >>
  simp[]
QED

(* ----------------------------------------------------------------------
    Primitive recursion for the pair.

    The principle above is an iterator: each function only ever sees the
    results of the recursive calls.  HOL's datatype axioms hand the
    function the constructor's arguments as well, and the two are bridged
    by the standard pairing trick — iterate into 'n1 # 'c1 and 'n2 # 'c2,
    rebuilding the arguments alongside the answers, and observe that
    rebuilding is the identity because it and the constructors solve the
    same iteration.  Both types go through it at once, so the maps here
    take a function per type rather than one.
   ---------------------------------------------------------------------- *)

Definition MapId2_def:
  MapId2 (mp : ('a -> 'a) -> ('b -> 'b) -> 'f -> 'f) ⇔ ∀x. mp I I x = x
End

Definition MapComp2_def:
  MapComp2 (mp_ab : ('a1 -> 'b1) -> ('a2 -> 'b2) -> 'f -> 'g)
           (mp_bc : ('b1 -> 'c1) -> ('b2 -> 'c2) -> 'g -> 'h)
           (mp_ac : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'f -> 'h) ⇔
    ∀f1 f2 g1 g2 x. mp_bc g1 g2 (mp_ab f1 f2 x) = mp_ac (g1 o f1) (g2 o f2) x
End

Theorem MUTUAL_PRIM_REC:
  MUTITER cn1 cn2
          (mpq1 : ('n1 -> 'n1 # 'c1) -> ('n2 -> 'n2 # 'c2) -> 'fn1 -> 'fq1)
          mpq2 ∧
  MUTITER cn1 cn2 mpn1 mpn2 ∧
  MapComp2 mpq1 mpqn1 mpn1 ∧ MapComp2 mpq1 mpqc1 mpc1 ∧ MapId2 mpn1 ∧
  MapComp2 mpq2 mpqn2 mpn2 ∧ MapComp2 mpq2 mpqc2 mpc2 ∧ MapId2 mpn2 ⇒
  ∀t1 t2.
    (∃(h1 : 'n1 -> 'c1) (h2 : 'n2 -> 'c2).
       (∀af. h1 (cn1 af) = t1 af (mpc1 h1 h2 af)) ∧
       (∀af. h2 (cn2 af) = t2 af (mpc2 h1 h2 af))) ∧
    ∀h1 h2 k1 k2.
      ((∀af. h1 (cn1 af) = t1 af (mpc1 h1 h2 af)) ∧
       (∀af. h2 (cn2 af) = t2 af (mpc2 h1 h2 af))) ∧
      ((∀af. k1 (cn1 af) = t1 af (mpc1 k1 k2 af)) ∧
       (∀af. k2 (cn2 af) = t2 af (mpc2 k1 k2 af))) ⇒ h1 = k1 ∧ h2 = k2
Proof
  strip_tac >> rpt gen_tac >>
  (* the paired iterator: alongside the answer it rebuilds its argument *)
  qpat_assum ‘MUTITER cn1 cn2 mpq1 mpq2’
    (fn th =>
        qspecl_then
          [‘λv. (cn1 (mpqn1 FST FST v),
                 t1 (mpqn1 FST FST v) (mpqc1 SND SND v))’,
           ‘λv. (cn2 (mpqn2 FST FST v),
                 t2 (mpqn2 FST FST v) (mpqc2 SND SND v))’]
          (strip_assume_tac o SRULE [])
          (SRULE [MUTITER_def, MUTREC_def] th)) >>
  (* and rebuilding is the identity: it and the constructors solve the
     iteration at the types themselves, which has one solution *)
  qpat_assum ‘MUTITER cn1 cn2 mpn1 mpn2’
    (fn th =>
        qspecl_then [‘cn1’, ‘cn2’] (strip_assume_tac o SRULE [])
                    (SRULE [MUTITER_def, MUTREC_def] th)) >>
  ‘FST o h1 = I ∧ FST o h2 = I’
    by (qpat_x_assum ‘∀h1 h2 k1 k2. _ ∧ _ ⇒ h1 = k1 ∧ h2 = k2’
          (qspecl_then [‘FST o h1’, ‘FST o h2’, ‘I’, ‘I’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> gen_tac >> simp[] >>
                     gs[MapId2_def, MapComp2_def]) >>
        simp[]) >>
  conj_tac
  >- (qexistsl_tac [‘SND o h1’, ‘SND o h2’] >> rpt conj_tac >> gen_tac >>
      simp[] >> gs[MapComp2_def] >> gs[MapId2_def]) >>
  (* uniqueness: a solution paired with the identity solves the paired
     iteration, and those solutions are unique *)
  ‘∀g1 g2. (∀af. g1 (cn1 af) = t1 af (mpc1 g1 g2 af)) ∧
           (∀af. g2 (cn2 af) = t2 af (mpc2 g1 g2 af)) ⇒
           h1 = (λx. (x, g1 x)) ∧ h2 = (λx. (x, g2 x))’
    by (rpt gen_tac >> strip_tac >>
        qpat_assum ‘∀h1 h2 k1 k2. _ ∧ _ ⇒ h1 = k1 ∧ h2 = k2’
          (qspecl_then [‘h1’, ‘h2’, ‘λx. (x, g1 x)’, ‘λx. (x, g2 x)’]
                       mp_tac) >>
        impl_tac
        >- (simp[] >> gs[MapComp2_def] >>
            simp[combinTheory.o_DEF, GSYM combinTheory.I_EQ_IDABS, ETA_AX] >>
            gs[MapId2_def]) >>
        simp[]) >>
  qx_genl_tac [‘g1’, ‘g2’, ‘j1’, ‘j2’] >> strip_tac >>
  ‘(λx. (x, g1 x)) = (λx. (x, j1 x)) ∧ (λx. (x, g2 x)) = (λx. (x, j2 x))’
    by metis_tac[] >>
  gs[FUN_EQ_THM]
QED
