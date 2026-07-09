Theory pushout
Ancestors
  category

Definition is_span_in_def:
  is_span_in c S A B f g <=>
    f :- S → A -:c /\
    g :- S → B -:c
End

Definition is_cospan_in_def:
  is_cospan_in c A B S f g <=>
    f :- A → S -:c /\
    g :- B → S -:c
End

Definition pushout_square_def:
  pushout_square c S A B P f g i j <=>
    f :- S → A -:c /\
    g :- S → B -:c /\
    i :- A → P -:c /\
    j :- B → P -:c /\
    (i o f -:c = j o g -:c)
End

Definition is_pushout_def:
  is_pushout c S A B P f g i j <=>
    pushout_square c S A B P f g i j /\
    (!P' i' j'.
      i' :- A → P' -:c /\
      j' :- B → P' -:c /\
      (i' o f -:c = j' o g -:c)
      ==>
      ?!u. u :- P → P' -:c /\
           (u o i -:c = i') /\
           (u o j -:c = j'))
End

Definition pullback_square_def:
  pullback_square c A B S P f g p q <=>
    f :- A → S -:c /\
    g :- B → S -:c /\
    p :- P → A -:c /\
    q :- P → B -:c /\
    (f o p -:c = g o q -:c)
End

Definition is_pullback_def:
  is_pullback c A B S P f g p q <=>
    pullback_square c A B S P f g p q /\
    (!P' p' q'.
      p' :- P' → A -:c /\
      q' :- P' → B -:c /\
      (f o p' -:c = g o q' -:c)
      ==>
      ?!u. u :- P' → P -:c /\
           (p o u -:c = p') /\
           (q o u -:c = q'))
End

Theorem pushout_pullback_dual:
  !c S A B P f g i j.
    is_category c ==>
    (is_pushout c S A B P f g i j <=>
     is_pullback (op_cat c) A B S P (op_mor f) (op_mor g) (op_mor i) (op_mor j))
Proof
  rw[is_pushout_def, is_pullback_def, pushout_square_def, pullback_square_def] >>
  simp[op_cat_maps_to_in, op_mor_idem] >>
  EQ_TAC
  >- (
    strip_tac >> rpt conj_tac >> TRY (simp[])
    >- (
      `f ≈> i -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      `g ≈> j -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      qspec_then `f°` (qspec_then `i°` mp_tac) op_cat_compose_in >>
      simp[op_mor_idem] >>
      disch_then (qspec_then `c` mp_tac) >> simp[] >>
      strip_tac >>
      irule EQ_SYM >>
      qspec_then `g°` (qspec_then `j°` (qspec_then `c` mp_tac)) op_cat_compose_in >>
      simp[op_mor_idem])
    >- (
      rpt strip_tac \\
      `p' ≈> f° -:c°` by (fs[maps_to_in_def, composable_in_def, op_cat_maps_to_in] >>
        metis_tac[op_mor_idem]) \\
      `q' ≈> g° -:c°` by (fs[maps_to_in_def, composable_in_def, op_cat_maps_to_in] >>
        metis_tac[op_mor_idem]) \\
      `f ≈> p'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `g ≈> q'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `f° o p' -:c° = (p'° o f -:c)°` by
        (qspecl_then [`f°`, `p'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `g° o q' -:c° = (q'° o g -:c)°` by
        (qspecl_then [`g°`, `q'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `p'° o f -:c = q'° o g -:c` by metis_tac[op_mor_idem] \\
      `?!u'. u' :- P → P' -:c /\ u' o i -:c = p'° /\ u' o j -:c = q'°` by
        (first_x_assum (qspecl_then [`P'`, `p'°`, `q'°`] mp_tac) >> simp[]) \\
      simp[EXISTS_UNIQUE_THM] \\
      conj_tac
      >- (
        `?u'. u' :- P → P' -:c /\ u' o i -:c = p'° /\ u' o j -:c = q'°` by
          fs[EXISTS_UNIQUE_THM] \\
        qexists_tac `u'°` >> simp[op_mor_idem] \\
        `i ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `i° o u'° -:c° = (u' o i -:c)°` by
          (qspecl_then [`i°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `j° o u'° -:c° = (u' o j -:c)°` by
          (qspecl_then [`j°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        metis_tac[op_mor_idem])
      >- (
        rpt strip_tac \\
        `i ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `j ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `i° o u -:c° = (u° o i -:c)°` by
          (qspecl_then [`i°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `u° o i -:c = p'°` by metis_tac[op_mor_idem] \\
        `j° o u -:c° = (u° o j -:c)°` by
          (qspecl_then [`j°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `u° o j -:c = q'°` by metis_tac[op_mor_idem] \\
        `i ≈> u'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) >>
        `j ≈> u'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `i° o u' -:c° = (u'° o i -:c)°` by
          (qspecl_then [`i°`, `u'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) >>
        `u'° o i -:c = p'°` by metis_tac[op_mor_idem] >>
        `j° o u' -:c° = (u'° o j -:c)°` by
          (qspecl_then [`j°`, `u'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) >>
        `u'° o j -:c = q'°` by metis_tac[op_mor_idem] \\
        `u° = u'°` by metis_tac[EXISTS_UNIQUE_THM] \\
        metis_tac[op_mor_idem])))
  >- (
    strip_tac >> rpt conj_tac >> TRY (simp[])
    >- (
      `f ≈> i -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      `g ≈> j -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `f° o i° -:c° = (i o f -:c)°` by
        (qspecl_then [`f°`, `i°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `g° o j° -:c° = (j o g -:c)°` by
        (qspecl_then [`g°`, `j°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      metis_tac[op_mor_idem])
    >- (
      rpt strip_tac \\
      `(i'°)° :- A → P' -:c` by simp[op_mor_idem] >>
      `(j'°)° :- B → P' -:c` by simp[op_mor_idem] \\
      `f ≈> i' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      `g ≈> j' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `f° o i'° -:c° = (i' o f -:c)°` by
        (qspecl_then [`f°`, `i'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) >>
      `g° o j'° -:c° = (j' o g -:c)°` by
        (qspecl_then [`g°`, `j'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `f° o i'° -:c° = g° o j'° -:c°` by metis_tac[] \\
      `?!u. u° :- P → P' -:c /\ i° o u -:c° = i'° /\ j° o u -:c° = j'°` by
        (first_x_assum (qspecl_then [`P'`, `i'°`, `j'°`] mp_tac) >> simp[op_mor_idem]) \\
      simp[EXISTS_UNIQUE_THM] >> conj_tac
      >- (
        `?u. u° :- P → P' -:c /\ i° o u -:c° = i'° /\ j° o u -:c° = j'°` by
          fs[EXISTS_UNIQUE_THM] \\
        qexists_tac `u°` >> simp[op_mor_idem] \\
        `i ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `j ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `i° o u -:c° = (u° o i -:c)°` by
          (qspecl_then [`i°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j° o u -:c° = (u° o j -:c)°` by
          (qspecl_then [`j°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        metis_tac[op_mor_idem])
      >- (
        rpt strip_tac \\
        `i ≈> u -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `j ≈> u -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `i ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `j ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `i° o u° -:c° = (u o i -:c)°` by
          (qspecl_then [`i°`, `u°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j° o u° -:c° = (u o j -:c)°` by
          (qspecl_then [`j°`, `u°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `i° o u'° -:c° = (u' o i -:c)°` by
          (qspecl_then [`i°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j° o u'° -:c° = (u' o j -:c)°` by
          (qspecl_then [`j°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        metis_tac[EXISTS_UNIQUE_THM, op_mor_idem])))
QED

Theorem pushout_unique_iso:
  !c S A B P1 P2 f g i1 j1 i2 j2.
    is_category c /\
    is_pushout c S A B P1 f g i1 j1 /\
    is_pushout c S A B P2 f g i2 j2
    ==>
    iso_objs c P1 P2
Proof
  rw[is_pushout_def, pushout_square_def, iso_objs_thm] >>
  `?!u. u :- P1 → P2 -:c /\ u o i1 -:c = i2 /\ u o j1 -:c = j2` by
    (first_x_assum (qspecl_then [`P2`, `i2`, `j2`] mp_tac) >> simp[]) >>
  `?!u. u :- P2 → P1 -:c /\ u o i2 -:c = i1 /\ u o j2 -:c = j1` by
    (first_x_assum (qspecl_then [`P1`, `i1`, `j1`] mp_tac) >> simp[]) >>
  `?!u. u :- P2 → P2 -:c /\ u o i2 -:c = i2 /\ u o j2 -:c = j2` by
    (last_x_assum (qspecl_then [`P2`, `i2`, `j2`] mp_tac) >> simp[]) >>
  `?!u. u :- P1 → P1 -:c /\ u o i1 -:c = i1 /\ u o j1 -:c = j1` by
    (last_x_assum (qspecl_then [`P1`, `i1`, `j1`] mp_tac) >> simp[]) >>
  qabbrev_tac `u = @u. u :- P1 → P2 -:c /\ u o i1 -:c = i2 /\ u o j1 -:c = j2` >>
  qabbrev_tac `v = @u. u :- P2 → P1 -:c /\ u o i2 -:c = i1 /\ u o j2 -:c = j1` >>
  `u :- P1 → P2 -:c /\ u o i1 -:c = i2 /\ u o j1 -:c = j2` by
    (markerLib.UNABBREV_ALL_TAC >> SELECT_ELIM_TAC >> rpt strip_tac >>
     metis_tac[EXISTS_UNIQUE_THM]) >>
  `v :- P2 → P1 -:c /\ v o i2 -:c = i1 /\ v o j2 -:c = j1` by
    (markerLib.UNABBREV_ALL_TAC >> SELECT_ELIM_TAC >> rpt strip_tac >>
     metis_tac[EXISTS_UNIQUE_THM]) >>
  `v o u -:c :- P1 → P1 -:c` by metis_tac[maps_to_comp] >>
  `(v o u -:c) o i1 -:c = i1` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `(v o u -:c) o j1 -:c = j1` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `id P1 -:c :- P1 → P1 -:c` by
    (irule id_maps_to >> simp[] >> fs[maps_to_in_def, maps_to_def] >>
     metis_tac[is_category_def, category_axioms_def]) >>
  `(id P1 -:c) o i1 -:c = i1` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `(id P1 -:c) o j1 -:c = j1` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `v o u -:c = id P1 -:c` by
    (qpat_x_assum `?!u. u :- P1 → P1 -:c /\ _` mp_tac >>
     simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  `u o v -:c :- P2 → P2 -:c` by metis_tac[maps_to_comp] >>
  `(u o v -:c) o i2 -:c = i2` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `(u o v -:c) o j2 -:c = j2` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `id P2 -:c :- P2 → P2 -:c` by
    (irule id_maps_to >> simp[] >> fs[maps_to_in_def, maps_to_def] >>
     metis_tac[is_category_def, category_axioms_def]) >>
  `(id P2 -:c) o i2 -:c = i2` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `(id P2 -:c) o j2 -:c = j2` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `u o v -:c = id P2 -:c` by
    (qpat_x_assum `?!u. u :- P2 → P2 -:c /\ _` mp_tac >>
     simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  qexists_tac `u` >> simp[iso_def] >> qexists_tac `v` >>
  simp[iso_pair_def, composable_in_def, composable_def] >>
  fs[maps_to_in_def, maps_to_def]
QED

Theorem pushout_iso_stability:
  !c S A B P f g i j.
    is_category c /\
    is_pushout c S A B P f g i j /\
    iso c f
    ==>
    iso c j
Proof
  rw[is_pushout_def, iso_def] >>
  fs[pushout_square_def, iso_pair_def] >>
  `g'.dom = f.cod` by fs[composable_in_def, composable_def] >>
  `g'.dom = A` by fs[maps_to_in_def, maps_to_def] >>
  `f.dom ∈ c.obj /\ f.cod ∈ c.obj /\ g'.dom ∈ c.obj /\ g'.cod ∈ c.obj`
    by metis_tac[composable_obj] >>
  `(g' o f -:c).cod = g'.cod` by (irule (cj 5 comp_mor_dom_cod) >> metis_tac[]) >>
  `(id f.dom -:c).cod = f.dom` by metis_tac[id_dom_cod] >>
  `g'.cod = f.dom` by metis_tac[] >>
  `f.dom = S'` by fs[maps_to_in_def, maps_to_def] >>
  `g'.cod = S'` by metis_tac[] >>
  `g'.cod = g.dom` by fs[maps_to_in_def, maps_to_def] >>
  `g' ∈ c.mor` by fs[composable_in_def] >>
  `g ∈ c.mor` by fs[maps_to_in_def] >>
  `g' ≈> g -:c` by simp[composable_in_def, composable_def] >>
  `g' :- A → S' -:c` by fs[maps_to_in_def, maps_to_def] >>
  `g o g' -:c :- A → B -:c` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def, maps_to_def] >>
  `B ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `id B -:c :- B → B -:c` by (irule id_maps_to >> simp[]) >>
  `f ≈> g' -:c /\ g' ≈> g -:c` by simp[] >>
  `(g o g' -:c) o f -:c = g o g' o f -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `g' o f -:c = id S' -:c` by metis_tac[] >>
  `g o id g.dom -:c -:c = g` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def] >>
  `g.dom = S'` by fs[maps_to_in_def, maps_to_def] >>
  `g o id S' -:c -:c = g` by metis_tac[] >>
  `S' ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `g o g' o f -:c -:c = g` by metis_tac[] >>
  `(g o g' -:c) o f -:c = g` by metis_tac[] >>
  `(id g.cod -:c) o g -:c = g` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def] >>
  `g.cod = B` by fs[maps_to_in_def, maps_to_def] >>
  `(id B -:c) o g -:c = g` by metis_tac[] >>
  `(g o g' -:c) o f -:c = (id B -:c) o g -:c` by metis_tac[] >>
  `?!k. k :- P → B -:c /\ k o i -:c = g o g' -:c /\ k o j -:c = id B -:c` by
    (first_x_assum irule >> simp[]) >>
  qabbrev_tac `k = @u. u :- P → B -:c /\ u o i -:c = g o g' -:c /\
                        u o j -:c = id B -:c` >>
  `k :- P → B -:c /\ k o i -:c = g o g' -:c /\ k o j -:c = id B -:c` by
    (markerLib.UNABBREV_ALL_TAC >> SELECT_ELIM_TAC >> rpt strip_tac >>
     metis_tac[EXISTS_UNIQUE_THM]) >>
  `f o g' -:c = id A -:c` by metis_tac[] >>
  `A ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `i.dom = A` by fs[maps_to_in_def, maps_to_def] >>
  `i ∈ c.mor` by fs[maps_to_in_def] >>
  `i o id i.dom -:c -:c = i` by metis_tac[is_category_def, category_axioms_def] >>
  `i o id A -:c -:c = i` by metis_tac[] >>
  `g' ≈> f -:c` by
    (simp[composable_in_def, composable_def] >> fs[maps_to_in_def, maps_to_def]) >>
  `f ≈> i -:c` by
    (simp[composable_in_def, composable_def] >> fs[maps_to_in_def, maps_to_def]) >>
  `(i o f -:c) o g' -:c = i o f o g' -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `(j o g -:c) o g' -:c = (i o f -:c) o g' -:c` by metis_tac[] >>
  `g ≈> j -:c` by
    (simp[composable_in_def, composable_def] >> fs[maps_to_in_def, maps_to_def]) >>
  `(j o g -:c) o g' -:c = j o g o g' -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `i o f o g' -:c -:c = i` by metis_tac[] >>
  `(i o f -:c) o g' -:c = i` by metis_tac[] >>
  `(j o g -:c) o g' -:c = i` by metis_tac[] >>
  `j o g o g' -:c -:c = i` by metis_tac[] >>
  `k.dom = P /\ k.cod = B` by fs[maps_to_in_def, maps_to_def] >>
  `j.dom = B /\ j.cod = P` by fs[maps_to_in_def, maps_to_def] >>
  `k ∈ c.mor` by fs[maps_to_in_def] >>
  `j ∈ c.mor` by fs[maps_to_in_def] >>
  `k ≈> j -:c` by simp[composable_in_def, composable_def] >>
  `j ≈> k -:c` by simp[composable_in_def, composable_def] >>
  `i.cod = P` by fs[maps_to_in_def, maps_to_def] >>
  `i ≈> k -:c` by simp[composable_in_def, composable_def] >>
  `(j o k -:c) o i -:c = j o k o i -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `j o k o i -:c -:c = i` by metis_tac[] >>
  `(j o k -:c) o i -:c = i` by metis_tac[] >>
  `(j o k -:c) o j -:c = j o k o j -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `j o k o j -:c -:c = j o id B -:c -:c` by metis_tac[] >>
  `j o id j.dom -:c -:c = j` by metis_tac[is_category_def, category_axioms_def] >>
  `j o id B -:c -:c = j` by metis_tac[] >>
  `(j o k -:c) o j -:c = j` by metis_tac[] >>
  `P ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `id P -:c :- P → P -:c` by (irule id_maps_to >> simp[]) >>
  `(id P -:c) o i -:c = i` by (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `(id P -:c) o j -:c = j` by (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `j o k -:c :- P → P -:c` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def, maps_to_def] >>
  `?!u. u :- P → P -:c /\ u o i -:c = i /\ u o j -:c = j` by
    (first_x_assum irule >> simp[]) >>
  `j o k -:c = id P -:c` by
    (qpat_x_assum `?!u. u :- P → P -:c /\ _` mp_tac >>
     simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  qexists_tac `k` >> simp[]
QED

Theorem pushout_transport_iso:
  !c S A B P P' f g i j e.
    is_category c /\
    is_pushout c S A B P f g i j /\
    e :- P → P' -:c /\ iso c e
    ==>
    is_pushout c S A B P' f g (e o i -:c) (e o j -:c)
Proof
  rpt strip_tac >>
  `e ∈ c.mor ∧ e.dom = P ∧ e.cod = P'` by fs[maps_to_in_def, maps_to_def] >>
  qabbrev_tac `d = inv_in c e` >>
  `d :- P' → P -:c` by (simp[Abbr`d`] >> irule inv_maps_to >> simp[]) >>
  `d ∈ c.mor ∧ d.dom = P' ∧ d.cod = P` by fs[maps_to_in_def, maps_to_def] >>
  `(e o d -:c = id P' -:c) ∧ (d o e -:c = id P -:c)` by
     (simp[Abbr`d`] >> metis_tac[comp_inv_id]) >>
  qpat_x_assum `is_pushout c _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [is_pushout_def, pushout_square_def]) >>
  `e o i -:c :- A → P' -:c` by metis_tac[maps_to_comp] >>
  `e o j -:c :- B → P' -:c` by metis_tac[maps_to_comp] >>
  simp[is_pushout_def, pushout_square_def] >>
  conj_tac
  >- (
      `f ≈> i -:c ∧ i ≈> e -:c ∧ g ≈> j -:c ∧ j ≈> e -:c`
        by metis_tac[maps_to_composable] >>
      metis_tac[comp_assoc]) >>
  rpt strip_tac >>
  `e ≈> d -:c ∧ d ≈> e -:c ∧ i ≈> e -:c ∧ j ≈> e -:c ∧
   (e o i -:c) ≈> d -:c ∧ (e o j -:c) ≈> d -:c` by metis_tac[maps_to_composable] >>
  `d o (e o i -:c) -:c = i` by
     metis_tac[comp_assoc, id_comp2, maps_to_in_def, maps_to_def] >>
  `d o (e o j -:c) -:c = j` by
     metis_tac[comp_assoc, id_comp2, maps_to_in_def, maps_to_def] >>
  `∃!u. u :- P → P'' -:c ∧ (u o i -:c = i') ∧ (u o j -:c = j')` by metis_tac[] >>
  `!w1 w2. (w1 :- P → P'' -:c ∧ w1 o i -:c = i' ∧ w1 o j -:c = j') ∧
           (w2 :- P → P'' -:c ∧ w2 o i -:c = i' ∧ w2 o j -:c = j') ==> (w1 = w2)`
     by metis_tac[EXISTS_UNIQUE_THM] >>
  `?w. w :- P → P'' -:c ∧ w o i -:c = i' ∧ w o j -:c = j'` by metis_tac[EXISTS_UNIQUE_THM] >>
  pop_assum strip_assume_tac >>
  `d ≈> w -:c` by metis_tac[maps_to_composable] >>
  simp[EXISTS_UNIQUE_THM] >>
  conj_tac
  >- (
      qexists_tac `w o d -:c` >>
      `w o d -:c :- P' → P'' -:c` by metis_tac[maps_to_comp] >>
      `(w o d -:c) o (e o i -:c) -:c = w o i -:c` by metis_tac[comp_assoc] >>
      `(w o d -:c) o (e o j -:c) -:c = w o j -:c` by metis_tac[comp_assoc] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `!v. v :- P' → P'' -:c ∧ (v o (e o i -:c) -:c = i') ∧ (v o (e o j -:c) -:c = j')
       ==> (v = w o d -:c)` by
     (rpt strip_tac >>
      `e ≈> v -:c` by metis_tac[maps_to_composable] >>
      `v o e -:c :- P → P'' -:c` by metis_tac[maps_to_comp] >>
      `(v o e -:c) o i -:c = i'` by metis_tac[comp_assoc] >>
      `(v o e -:c) o j -:c = j'` by metis_tac[comp_assoc] >>
      `v o e -:c = w` by metis_tac[] >>
      `v = (v o e -:c) o d -:c` by
         metis_tac[comp_assoc, id_comp1, maps_to_in_def, maps_to_def] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem pushout_transport_dom_iso:
  !c X A A' B P f g i j e.
    is_category c ∧
    is_pushout c X A B P f g i j ∧
    e :- A' → A -:c ∧ iso c e
    ==>
    is_pushout c X A' B P (inv_in c e o f -:c) g (i o e -:c) j
Proof
  rpt strip_tac >>
  `e ∈ c.mor ∧ e.dom = A' ∧ e.cod = A` by fs[maps_to_in_def, maps_to_def] >>
  qabbrev_tac `d = inv_in c e` >>
  `d :- A → A' -:c` by (simp[Abbr`d`] >> irule inv_maps_to >> simp[]) >>
  `d ∈ c.mor ∧ d.dom = A ∧ d.cod = A'` by fs[maps_to_in_def, maps_to_def] >>
  `(e o d -:c = id A -:c) ∧ (d o e -:c = id A' -:c)` by
     (simp[Abbr`d`] >> metis_tac[comp_inv_id]) >>
  qpat_x_assum `is_pushout c _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [is_pushout_def, pushout_square_def]) >>
  `d o f -:c :- X → A' -:c` by metis_tac[maps_to_comp] >>
  `i o e -:c :- A' → P -:c` by metis_tac[maps_to_comp] >>
  `f ≈> d -:c ∧ e ≈> i -:c ∧ d ≈> e -:c` by metis_tac[maps_to_composable] >>
  simp[is_pushout_def, pushout_square_def] >>
  conj_tac
  >- (
      `(i o e -:c) o (d o f -:c) -:c = i o f -:c` by
         metis_tac[comp_assoc, id_comp1, maps_to_composable, maps_to_in_def, maps_to_def] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `i' o d -:c :- A → P' -:c` by metis_tac[maps_to_comp] >>
  `(i' o d -:c) o f -:c = j' o g -:c` by
     metis_tac[comp_assoc, maps_to_composable] >>
  `∃!u. u :- P → P' -:c ∧ (u o i -:c = i' o d -:c) ∧ (u o j -:c = j')` by metis_tac[] >>
  `!w1 w2. (w1 :- P → P' -:c ∧ w1 o i -:c = i' o d -:c ∧ w1 o j -:c = j') ∧
           (w2 :- P → P' -:c ∧ w2 o i -:c = i' o d -:c ∧ w2 o j -:c = j') ==> (w1 = w2)`
     by metis_tac[EXISTS_UNIQUE_THM] >>
  `?w. w :- P → P' -:c ∧ w o i -:c = i' o d -:c ∧ w o j -:c = j'`
     by metis_tac[EXISTS_UNIQUE_THM] >>
  pop_assum strip_assume_tac >>
  simp[EXISTS_UNIQUE_THM] >>
  conj_tac
  >- (
      qexists_tac `w` >>
      `w o (i o e -:c) -:c = i'` by
         metis_tac[comp_assoc, id_comp1, maps_to_composable, maps_to_in_def, maps_to_def] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `!v. v :- P → P' -:c ∧ (v o (i o e -:c) -:c = i') ∧ (v o j -:c = j') ==> (v = w)` by
     (rpt strip_tac >>
      `v o i -:c = i' o d -:c` by
         metis_tac[comp_assoc, id_comp1, maps_to_composable, maps_to_in_def, maps_to_def] >>
      metis_tac[]) >>
  metis_tac[]
QED

Triviality pushout_sym:
  !c X A B P f g i j.
    is_pushout c X A B P f g i j ==> is_pushout c X B A P g f j i
Proof
  rw[is_pushout_def, pushout_square_def] >> metis_tac[]
QED

Theorem pushout_transport_cod_iso:
  !c X A B B' P f g i j e.
    is_category c ∧
    is_pushout c X A B P f g i j ∧
    e :- B' → B -:c ∧ iso c e
    ==>
    is_pushout c X A B' P f (inv_in c e o g -:c) i (j o e -:c)
Proof
  rpt strip_tac >>
  `is_pushout c X B A P g f j i` by (irule pushout_sym >> simp[]) >>
  `is_pushout c X B' A P (inv_in c e o g -:c) f (j o e -:c) i`
     by (qspecl_then [`c`,`X`,`B`,`B'`,`A`,`P`,`g`,`f`,`j`,`i`,`e`]
           mp_tac pushout_transport_dom_iso >> simp[]) >>
  irule pushout_sym >> simp[]
QED

Theorem pushout_relabel_span:
  !c X A A' B B' P f g i j eA eB.
    is_category c ∧
    is_pushout c X A B P f g i j ∧
    eA :- A' → A -:c ∧ iso c eA ∧
    eB :- B' → B -:c ∧ iso c eB
    ==>
    is_pushout c X A' B' P
      (inv_in c eA o f -:c) (inv_in c eB o g -:c) (i o eA -:c) (j o eB -:c)
Proof
  rpt strip_tac >>
  `is_pushout c X A' B P (inv_in c eA o f -:c) g (i o eA -:c) j`
     by (qspecl_then [`c`,`X`,`A`,`A'`,`B`,`P`,`f`,`g`,`i`,`j`,`eA`]
           mp_tac pushout_transport_dom_iso >> simp[]) >>
  qspecl_then [`c`,`X`,`A'`,`B`,`B'`,`P`,`inv_in c eA o f -:c`,`g`,`i o eA -:c`,`j`,`eB`]
    mp_tac pushout_transport_cod_iso >> simp[]
QED

Theorem iso_cancel_left:
  is_category c /\ iso c e /\ x ≈> e -:c ==>
  inv_in c e o (e o x -:c) -:c = x
Proof
  rpt strip_tac >>
  `e IN c.mor /\ x IN c.mor /\ x.cod = e.dom` by fs[composable_in_def] >>
  `e ≈> inv_in c e -:c` by simp[inv_composable] >>
  `inv_in c e o (e o x -:c) -:c = (inv_in c e o e -:c) o x -:c` by
    metis_tac[comp_assoc] >>
  pop_assum SUBST1_TAC >>
  `inv_in c e o e -:c = id e.dom -:c` by simp[comp_inv_id] >>
  pop_assum SUBST1_TAC >>
  `e.dom = x.cod` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule id_comp2 >> simp[]
QED
