Theory bnfMutual
Ancestors
  bnfFixBNF
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
  ∀t1 t2.
    (∃h1 h2. MUTREC cn1 cn2 mpK mpQ t1 t2 h1 h2) ∧
    ∀h1 h2 k1 k2.
      MUTREC cn1 cn2 mpK mpQ t1 t2 h1 h2 ∧
      MUTREC cn1 cn2 mpK mpQ t1 t2 k1 k2 ⇒ h1 = k1 ∧ h2 = k2
Proof
  strip_tac >>
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
