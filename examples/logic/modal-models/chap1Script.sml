open HolKernel Parse boolLib bossLib;
open nlistTheory listTheory;
open pred_setTheory;
open modalBasicsTheory;

val _ = new_theory "chap1";

(* Def 1.9 *)
(* definition of formula; define the box as the dual of diamond *)

val BOX_def =
  Define
    `BOX form = NOT (DIAM (NOT form))`;

val IMP_def = Define`
  IMP f1 f2 = DISJ (NOT f1) f2
  `;


val _ = set_mapped_fixity{fixity = Infixr 200, term_name = "IMP", tok = "->"}



val AND_def =
  Define
    `AND f1 f2 = NOT (DISJ (NOT f1) (NOT f2))
   `;

val DOUBLE_IMP_def =
  Define
    `DOUBLE_IMP f1 f2 = AND (IMP f1 f2) (IMP f2 f1)
   `;

val TRUE_def =
  Define
    `TRUE = NOT FALSE`;


val _ = overload_on ("□", ``BOX``);
val _ = overload_on ("◇", ``DIAM``);
val _ = overload_on ("⊥", ``FALSE``);
val _ = overload_on ("~", ``NOT``);
Overload "¬" = ``NOT``


(* Def 1.18 *)
(* define the substitution function induced by a function from a set of propositional letters to a set of forms*)
val subst_def =
  Define
    `subst f FALSE = FALSE /\
     subst f (VAR p) = f p /\
     subst f (DISJ form1 form2) = DISJ (subst f form1) (subst f form2) /\
     subst f (NOT form) = NOT (subst f form) /\
     subst f (DIAM form) = DIAM (subst f form)`;

val _ = export_rewrites ["subst_def"]

val subst_box = store_thm(
    "subst_box[simp]",
    ``subst f (BOX form) = BOX (subst f form)``,
    rw[BOX_def]);


Theorem satis_in_world = satis_only_in_worlds
Theorem satis_def = satis_def
val _ = temp_delsimps ["satis_def"]

Theorem frame_component_equality = frame_component_equality

val satis_AND = store_thm(
"satis_AND",
``!M w f1 f2. satis M w (AND f1 f2) <=> (satis M w f1 /\ satis M w f2)``,
rpt strip_tac >> eq_tac >- (rpt strip_tac >> fs[satis_def,AND_def] >> metis_tac[])
                        >- (rpt strip_tac >> fs[satis_def,AND_def] >> metis_tac[satis_in_world]));



val satis_set_def =
  Define
  `satis_set M w (Σ:form set) = !a. a IN Σ ==> satis M w a`;



(* Def 1.21 *)
(* definition of universally true/ satisfiable/ falsiable *)
val universal_true_def = Define`
    universal_true M form <=> (!w. w IN M.frame.world ==> satis M w form)`;

val satisfiable_def = Define`
    stfable M form = (?w. satis M w form)`;

val refutable_def = Define`
    refutable M form = (?w. satis M w (NOT form))`;


(* Def 1.28 *)
(* definitions involves validness *)


val valid_frame_state_def = Define`
    valid_frame_state f w form = !M. M.frame = f ==> satis M w form`;

val valid_frame_def =Define`
    valid_frame f form = !w. valid_frame_state f w form`;

val valid_class_frame_def = Define`
    valid_class C form = !f. f IN C ==> valid_frame f form`;

val valid_def = Define`
    valid (form:form)  =
      !f:num frame. valid_frame f form`;

val logic_def = Define`
    LOGIC C = {form | valid_class C form}`



(* Def 1.35 *)
val local_semantic_conseq = Define`
    LSC Σ S form <=>
    !(M:'b model) w.
       M IN S /\ satis_set M w Σ ==>
       satis M w form`;



(* Def 1.39 *)
val demodalize_def = Define`
demodalize FALSE = FALSE /\
demodalize (VAR p) = VAR p /\
demodalize (DISJ form1 form2) = DISJ (demodalize form1) (demodalize form2) /\
demodalize (NOT form) = NOT (demodalize form) /\
demodalize (DIAM form) = demodalize form`;

val propform_def = Define`
    propform (VAR p) = T /\
    (propform (DISJ form1 form2) <=> propform form1 /\ propform form2) /\
    (propform (NOT f) <=> propform f) /\
    propform FALSE = T /\
    propform (DIAM f) = F`;

val _ = export_rewrites["propform_def"]

val propform_IMP = store_thm(
    "propform_IMP[simp]",
    ``!f1 f2. propform (f1 -> f2) <=> propform f1 /\ propform f2``,
    simp[IMP_def]);


val peval_def = Define`
    peval σ (VAR p) = σ p /\
    (peval σ (DISJ f1 f2) <=> peval σ f1 \/ peval σ f2) /\
    peval σ FALSE = F /\
    peval σ (NOT f) = ¬peval σ f /\
    peval σ (DIAM f) = F`;

val _ = export_rewrites["peval_def"]

val ptaut_def = Define`
    ptaut f <=> propform f /\ !σ. peval σ f = T`;





val (Kproof_rules, Kproof_ind, Kproof_cases) = Hol_reln`
  Kproof [] /\
  (!p form1 form2.
    Kproof p /\ MEM (IMP form1 form2) p /\ MEM form1 p ==>
    Kproof (p ++ [form2])) /\
  (!p form f.
    Kproof p /\ MEM form p ==> Kproof (p ++ [subst f form])) /\
  (!p form. Kproof p /\ MEM form p ==> Kproof (p ++ [BOX form])) /\
  (!p form1 form2. Kproof p ==> Kproof (p ++ [IMP (BOX (IMP form1 form2)) (IMP (BOX form1) (BOX form2))])) /\
  (!p form. Kproof p ==> Kproof (p ++ [IMP (DIAM form) (NOT (BOX (NOT form)))])) /\
  (!p form. Kproof p ==> Kproof (p ++ [IMP (NOT (BOX (NOT form))) (DIAM form)])) /\
  (!p f. Kproof p /\ ptaut f ==> Kproof (p ++ [f]))
`;

val K_provable_def = Define`
K_provable form <=> ?p. Kproof p /\ Kproof (p ++ [form])`;





(* Def 1.42 *)
val normal_modal_logic = Define`
NML (S: form set) <=> !A B p q f form.
                  (ptaut form ==> form IN S) /\
                  (IMP (BOX (IMP p q)) (IMP (BOX p) (BOX q))) IN S /\
                  (IMP (DIAM p) (NOT (BOX (NOT p)))) IN S /\
                  (IMP (NOT (BOX (NOT p))) (DIAM p)) IN S /\
                  (A IN S ==> (subst f A) IN S) /\
                  (A IN S ==> (BOX A) IN S) /\
                  ((IMP A B) IN S /\ A IN S ==> B IN S)`;



val propform_demodalize = store_thm(
    "propform_demodalize",
    ``!f. propform (demodalize f)``,
    Induct_on `f` >> simp[propform_def, demodalize_def]);



val peval_IMP = store_thm(
    "peval_IMP[simp]",
    ``peval σ (f1 -> f2) <=> peval σ f1 ==> peval σ f2``,
    simp[IMP_def] >> DECIDE_TAC);



val peval_AND = store_thm(
    "peval_AND[simp]",
    ``peval σ (AND f1 f2) <=> peval σ f1 /\ peval σ f2``,
    simp[AND_def] >> DECIDE_TAC);





val K_provable_EM = store_thm(
    "K_provable_EM",
    ``K_provable (DISJ (VAR p) (NOT (VAR p)))``,
    rw[K_provable_def] >>
    `ptaut (DISJ (VAR p) (NOT (VAR p)))` suffices_by metis_tac[Kproof_cases] >>
    rw[ptaut_def]);



val ptaut_MP = store_thm(
    "ptaut_MP",
    ``!f1 f2. ptaut (f1 -> f2) /\ ptaut f1 ==> ptaut f2``,
    rpt strip_tac >> fs[ptaut_def,peval_def]);



val demodalize_IMP = store_thm(
    "demodalize_IMP",
    ``!f1 f2. demodalize (f1 -> f2) = (demodalize f1 -> demodalize f2)``,
    rw[demodalize_def, IMP_def]);








val peval_demodalize_subst_eq = store_thm(
    "peval_demodalize_subst_eq",
    ``!f σ form. propform form ==> (peval σ (demodalize (subst f form)) <=> peval (peval σ o demodalize o f) form)``,
    Induct_on `form` >> simp[demodalize_def]);



val demodalize_subst = store_thm(
    "demodalize_subst",
    ``!form f. demodalize (subst f form) = demodalize (subst f (demodalize form))``,
    Induct_on `form` >>
    fs[demodalize_def,subst_def]);



val ptaut_not_not = store_thm(
    "ptaut_not_not",
    ``!f. ptaut f ==> ptaut (NOT (NOT f))``,
    fs[ptaut_def]);



val peval_not_not = store_thm(
    "peval_not_not",
    ``!f. peval σ f = peval σ (NOT (NOT f))``,
    rw[peval_def]);



val ptaut_EM = store_thm(
    "ptaut_EM",
    ``!f. propform f ==> ptaut (DISJ f (NOT f))``,
    rw[ptaut_def]);



val peval_DISJ_COMM = store_thm(
    "peval_DISJ_COMM",
    ``!f1 f2. (propform f1 /\ propform f2) ==> (peval σ (DISJ f1 f2) = peval σ (DISJ f2 f1))``,
    rw[peval_def] >> metis_tac[]);



val ptaut_propform_K = store_thm(
    "ptaut_propform_K",
    ``!f1 f2. propform f1 /\ propform f2 ==>
     ptaut (DISJ (¬ ¬ ¬DISJ (¬f1) (f2))
    (DISJ (¬ ¬ ¬f1) (¬ ¬f2)))``,
    rpt strip_tac >>
    `propform (DISJ (¬ ¬ ¬DISJ (¬f1) (f2))
    (DISJ (¬ ¬ ¬f1) (¬ ¬f2)))` by rw[propform_def] >>
    `!σ. peval σ (DISJ (¬ ¬ ¬DISJ (¬f1) (f2))
    (DISJ (¬ ¬ ¬f1) (¬ ¬f2))) = peval σ (DISJ (¬DISJ (¬f1) (f2))
    (DISJ (¬f1) (f2)))` by metis_tac[peval_def,peval_not_not] >>
    `!σ. peval σ (DISJ (¬DISJ (¬f1) f2) (DISJ (¬f1) f2)) = T` by metis_tac[peval_def] >>
    `!σ. peval σ (DISJ (¬ ¬ ¬DISJ (¬f1) f2) (DISJ (¬ ¬ ¬f1) (¬ ¬f2))) = T` by metis_tac[] >>
    metis_tac[ptaut_def]);



val ptaut_propform_dual1 = store_thm(
    "ptaut_propform_dual1",
    ``!f. propform f ==>
     ptaut (DISJ (¬f) (¬ ¬ ¬ ¬f))``,
    rpt strip_tac >>
    `propform (DISJ (¬f) (¬ ¬ ¬ ¬f))` by rw[propform_def] >>
    `!σ. peval σ (DISJ (¬f) (¬ ¬ ¬ ¬f)) = peval σ (DISJ (¬f) f)` by metis_tac[peval_def,peval_not_not] >>
    `!σ. peval σ (DISJ (¬f) f) = T` by metis_tac[peval_def] >>
    `!σ. peval σ  (DISJ (¬f) (¬ ¬ ¬ ¬f)) = T` by metis_tac[] >>
    metis_tac[ptaut_def]);



val ptaut_propform_dual2 = store_thm(
    "ptaut_propform_dual2",
    ``!f. propform f ==>
     ptaut (DISJ (¬ ¬ ¬ ¬ ¬f) f)``,
    rpt strip_tac >>
    `propform (DISJ (¬ ¬ ¬ ¬ ¬f) f)` by rw[propform_def] >>
    `!σ. peval σ (DISJ (¬ ¬ ¬ ¬ ¬f) f) = peval σ (DISJ (¬f) f)` by metis_tac[peval_def,peval_not_not] >>
    `!σ. peval σ (DISJ (¬f) f) = T` by metis_tac[peval_def] >>
    `!σ. peval σ (DISJ (¬ ¬ ¬ ¬ ¬f) f) = T` by metis_tac[] >>
    metis_tac[ptaut_def]);



val demodalize_propform = store_thm(
    "demodalize_propform",
    ``!f. propform f ==> demodalize f = f``,
   Induct_on `f` >> rw[propform_def,demodalize_def]);



val ptaut_demodalize = store_thm(
    "ptaut_demodalize",
    ``!f. ptaut f ==> ptaut (demodalize f)``,
    rw[ptaut_def,demodalize_propform]);


val exercise_1_6_2 = store_thm(
    "exercise_1_6_2",
    ``!p. Kproof p ==> !f. MEM f p ==> ptaut (demodalize f)``,
    Induct_on `Kproof` >> rpt strip_tac
    >- (* empty proof *) fs[]
    >- (* modus ponens *)
       (`MEM f p ==> ptaut (demodalize f)` by rw[] >>
        `MEM (form1 -> form2) p ==> ptaut (demodalize (form1 -> form2))` by metis_tac[] >>
        `ptaut (demodalize (form1 -> form2))` by metis_tac[] >>
        `ptaut (demodalize form1 -> demodalize form2)` by metis_tac[demodalize_IMP] >>
        `MEM form1 p ==> ptaut (demodalize form1)` by metis_tac[] >>
        `ptaut (demodalize form1)` by metis_tac[] >>
        `ptaut (demodalize form2)` by metis_tac[ptaut_MP] >>
        `MEM f p \/ MEM f [form2]` by metis_tac[MEM_APPEND]
        >- metis_tac[]
        >- (`f = form2` by metis_tac[MEM] >> rw[]))
    >- (* instantiation *)
       (fs[MEM_APPEND] >>
        simp[ptaut_def,propform_demodalize,Once demodalize_subst,
             peval_demodalize_subst_eq] >>
        fs[ptaut_def])
    >- (`MEM f p \/ MEM f [BOX form]` by metis_tac[MEM_APPEND] >-
    metis_tac[] >>
    `f = BOX form` by metis_tac[MEM] >>
    `demodalize (BOX form) = NOT (NOT (demodalize form))` by rw[demodalize_def, BOX_def] >>
    `ptaut (demodalize form)` by metis_tac[] >>
    `ptaut (NOT (NOT (demodalize form)))` by metis_tac[ptaut_not_not] >>
    metis_tac[])

    >- (* box K axiom 1 *)
       (`MEM f p \/ MEM f [□ (form1 -> form2) -> □ form1 -> □ form2]` by metis_tac[MEM_APPEND] >-
    metis_tac[] >>
    `f = (□ (form1 -> form2) -> □ form1 -> □ form2)` by metis_tac[MEM] >>
    `propform (demodalize form1)` by metis_tac[propform_demodalize] >>
    `propform (demodalize form2)` by metis_tac[propform_demodalize] >>
    `ptaut (DISJ (¬ ¬ ¬DISJ (¬demodalize form1) (demodalize form2))
    (DISJ (¬ ¬ ¬demodalize form1) (¬ ¬demodalize form2)))` by simp[propform_demodalize,ptaut_propform_K] >>
    `demodalize (□ (form1 -> form2) -> □ form1 -> □ form2) =
  DISJ (¬ ¬ ¬DISJ (¬demodalize form1) (demodalize form2))
    (DISJ (¬ ¬ ¬demodalize form1) (¬ ¬demodalize form2))` by simp[demodalize_def, BOX_def,IMP_def] >>
    `ptaut (demodalize (□ (form1 -> form2) -> □ form1 -> □ form2))` by rw_tac std_ss[demodalize_def] >> metis_tac[])

    >- (`MEM f p \/ MEM f [◇ form -> ¬□ (¬form)]` by metis_tac[MEM_APPEND] >-
    metis_tac[] >>
    `f = (◇ form -> ¬□ (¬form))` by metis_tac[MEM] >>
    `propform (demodalize form)` by metis_tac[propform_demodalize] >>
    `ptaut (DISJ (¬demodalize form) (¬ ¬ ¬ ¬demodalize form))` by simp[propform_demodalize,ptaut_propform_dual1] >>
    `demodalize (◇ form -> ¬□ (¬form)) =
  DISJ (¬demodalize form) (¬ ¬ ¬ ¬demodalize form)` by simp[demodalize_def, BOX_def,IMP_def] >>
    `ptaut (demodalize (◇ form -> ¬□ (¬form)))` by fs[demodalize_def,IMP_def,BOX_def] >> metis_tac[])

     >- (`MEM f p \/ MEM f [¬□ (¬form) -> ◇ form]` by metis_tac[MEM_APPEND] >-
    metis_tac[] >>
    `f = (¬□ (¬form) -> ◇ form)` by metis_tac[MEM] >>
    `propform (demodalize form)` by metis_tac[propform_demodalize] >>
    `ptaut (DISJ (¬ ¬ ¬ ¬ ¬demodalize form) (demodalize form))` by simp[propform_demodalize,ptaut_propform_dual2] >>
    `demodalize (¬□ (¬form) -> ◇ form) =
  DISJ (¬ ¬ ¬ ¬ ¬demodalize form) (demodalize form)` by simp[demodalize_def, BOX_def,IMP_def] >>
    `ptaut (demodalize (¬□ (¬form) -> ◇ form))` by fs[demodalize_def,IMP_def,BOX_def] >> metis_tac[])

     >- (fs[MEM_APPEND] >> metis_tac[ptaut_demodalize]));









(* THE FOLLOWING IS FOR 1.6.6! *)





val (KGproof_rules, KGproof_ind, KGproof_cases) = Hol_reln`
  KGproof (Γ:form set) [] /\
  (!p form1 form2.
    KGproof Γ p /\ MEM (IMP form1 form2) p /\ MEM form1 p ==>
    KGproof Γ (p ++ [form2])) /\
  (!p form f.
    KGproof Γ p /\ MEM form p ==> KGproof Γ (p ++ [subst f form])) /\
  (!p form. KGproof Γ p /\ MEM form p ==> KGproof Γ (p ++ [BOX form])) /\
  (!p form1 form2. KGproof Γ p ==> KGproof Γ (p ++ [IMP (BOX (IMP form1 form2)) (IMP (BOX form1) (BOX form2))])) /\
  (!p form. KGproof Γ p ==> KGproof Γ (p ++ [IMP (DIAM form) (NOT (BOX (NOT form)))])) /\
  (!p form. KGproof Γ p ==> KGproof Γ (p ++ [IMP (NOT (BOX (NOT form))) (DIAM form)])) /\
  (!p form. KGproof Γ p /\ ptaut form ==> KGproof Γ (p ++ [form])) /\
  (!p form. KGproof Γ p /\ form IN Γ ==> KGproof Γ (p ++ [form]))
`;



val KG_provable_def = Define`
KG_provable Γ form <=> ?p. KGproof Γ p /\ KGproof Γ (p ++ [form])`;



val NMLG_def = Define`
NMLG (Γ:form set) = BIGINTER {A | (NML A) /\ (Γ SUBSET A)}`;


val NMLG_ind = save_thm(
  "NMLG_ind",
  ``phi ∈ NMLG G``
    |> SIMP_CONV (srw_ss()) [NMLG_def, normal_modal_logic]
    |> EQ_IMP_RULE |> #1
    |> UNDISCH |> SPEC_ALL |> UNDISCH
    |> DISCH ``(phi : form) ∈ NMLG G``
    |> Q.GEN `phi`
    |> DISCH_ALL |> Q.GEN `P`)



val KGproof_APPEND = store_thm(
    "KGproof_APPEND",
    ``!p2. KGproof Γ p2 ==> !p1. KGproof Γ p1 ==> KGproof Γ (p1 ++ p2)``,
    Induct_on `KGproof` >> simp[] >>
    metis_tac[KGproof_rules, MEM_APPEND, APPEND_ASSOC]);




Theorem exercise_1_6_6_d2:
  !f. f ∈ NMLG Γ ⇒ f ∈ { phi | KG_provable Γ phi }
Proof
  ho_match_mp_tac NMLG_ind >> simp[] >> rpt strip_tac >>
  simp[KG_provable_def] >~
  [‘KG_provable Γ (A -> B)’, ‘KG_provable Γ A’]
  >- (fs[KG_provable_def] >>
      rename [‘KGproof Γ (p1 ++ [A -> B])’, ‘KGproof Γ (p2 ++ [A])’] >>
      qexists_tac `p1 ++ [A -> B] ++ p2 ++ [A]` >>
      conj_asm1_tac >- metis_tac[APPEND_ASSOC,KGproof_APPEND]
      >- metis_tac[MEM,MEM_APPEND,KGproof_rules]) >~
  [‘Γ ⊆ _’]
  >- (rw[SUBSET_DEF] >> qexists_tac `[]` >> metis_tac[KGproof_rules]) >>
  metis_tac[MEM,MEM_APPEND,KGproof_rules,KG_provable_def]
QED

val NML_NMLG = store_thm(
    "NML_NMLG",
    ``!G. NML (NMLG G)``,
    rw[NMLG_def,BIGINTER,normal_modal_logic] >> metis_tac[]);



val exercise_1_6_6_d1 = store_thm(
    "exercise_1_6_6_d1",
    ``!p. KGproof Γ p ==> !form. MEM form p  ==> form IN NMLG Γ``,
    Induct_on `KGproof` >>
    rpt strip_tac >- (metis_tac[MEM])
                  >- (`MEM form p \/ MEM form [form2]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form = form2` by metis_tac[MEM] >>
     `form1 IN NMLG Γ` by metis_tac[] >>
     `(form1 -> form2) IN NMLG Γ` by metis_tac[] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form' p \/ MEM form' [subst f form]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form' = subst f form` by metis_tac[MEM] >>
     `form IN NMLG Γ` by metis_tac[] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form' p \/ MEM form' [BOX form]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form' = BOX form` by metis_tac[MEM] >>
     `form IN NMLG Γ` by metis_tac[] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form p \/ MEM form [□ (form1 -> form2) -> □ form1 -> □ form2]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form = (□ (form1 -> form2) -> □ form1 -> □ form2)` by metis_tac[MEM] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form' p \/ MEM form' [◇ form -> ¬□ (¬form)]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form' = (◇ form -> ¬□ (¬form))` by metis_tac[MEM] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form' p \/ MEM form' [¬□ (¬form) -> ◇ form]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form' = (¬□ (¬form) -> ◇ form)` by metis_tac[MEM] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form' p \/ MEM form' [form]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form' = form` by metis_tac[MEM] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[normal_modal_logic] >> metis_tac[])
                  >- (`MEM form' p \/ MEM form' [form]` by metis_tac[MEM_APPEND] >-
     metis_tac[] >>
     `form' = form` by metis_tac[MEM] >>
     `NML (NMLG Γ)` by metis_tac[NML_NMLG] >>
     fs[NMLG_def] >> rpt strip_tac >> metis_tac[SUBSET_DEF]));


val KG_provable_G = store_thm(
    "KG_provable_G",
    ``Γ SUBSET {form | KG_provable Γ form}``,
    fs[KG_provable_def] >> rw[SUBSET_DEF] >>
    qexists_tac `[]` >> metis_tac[KGproof_rules]);



(*prop symbols*)

val prop_letters_def = Define`
  (prop_letters (VAR p) = {p}) /\
  (prop_letters FALSE = {}) /\
  (prop_letters (DISJ f1 f2) = (prop_letters f1) ∪ (prop_letters f2)) /\
  (prop_letters (NOT f) = prop_letters f) /\
  (prop_letters (DIAM f) = prop_letters f)`


Theorem exercise_1_3_1:
!phi M1 M2.
   M1.frame = M2.frame ==>
   (!p. p IN (prop_letters phi) ==> M1.valt p = M2.valt p) ==>
   (!w. w IN M1.frame.world ==> (satis M1 w phi <=> satis M2 w phi))
Proof
Induct_on `phi` >> rw[satis_def] (* 4 *) >>
fs[prop_letters_def] >> metis_tac[]
QED


Theorem subst_comp:
 subst g (subst f x) = subst ((subst g) o f) x
Proof
Induct_on `x` >> rw[subst_def]
QED

val _ = export_theory();
