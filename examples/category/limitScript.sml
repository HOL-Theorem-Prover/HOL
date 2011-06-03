open HolKernel Parse bossLib boolLib boolSimps categoryTheory functorTheory nat_transTheory pairTheory lcsymtacs SatisfySimps;

val _ = new_theory "limit";

val is_terminal_def = Define`
  is_terminal c y = y ∈ c.obj ∧ ∀x. x ∈ c.obj ⇒ ∃!f. f :- x → y-:c`;

val is_initial_def = Define`
  is_initial c x = is_terminal (op_cat c) x`;

val is_initial_thm = Q.store_thm(
"is_initial_thm",
`∀c x. is_category c ⇒ (is_initial c x = x ∈ c.obj ∧ ∀y. y ∈ c.obj ⇒ ∃!f. f :- x → y-:c)`,
metis_tac [is_initial_def,is_terminal_def,op_cat_maps_to_in,op_cat_idem,op_cat_obj,op_mor_idem])

val terminal_unique = Q.store_thm(
"terminal_unique",
`∀c x y. is_category c ∧ is_terminal c x ∧ is_terminal c y ⇒ uiso_objs c x y`,
srw_tac [][uiso_objs_thm] >>
simp_tac (srw_ss()) [EXISTS_UNIQUE_THM] >>
reverse conj_tac >- metis_tac [is_terminal_def] >>
`∃f. f :- x → y-:c` by metis_tac [is_terminal_def] >>
qexists_tac `f` >> srw_tac [][iso_def] >>
`∃g. g :- y → x-:c` by metis_tac [is_terminal_def] >>
qexists_tac `g` >> srw_tac [][iso_pair_def]
>- metis_tac [maps_to_composable,FST,SND]
>> PROVE_TAC [is_terminal_def,id_maps_to,maps_to_comp,maps_to_def,maps_to_in_def,mor_obj]);

val initial_unique = Q.store_thm(
"initial_unique",
`∀c x y. is_category c ∧ is_initial c x ∧ is_initial c y ⇒ uiso_objs c x y`,
metis_tac [terminal_unique,is_initial_def,is_category_op_cat,op_cat_uiso_objs]);

val is_terminal_cat_iso = Q.store_thm(
"is_terminal_cat_iso", (* actually should work for just an equivalence *)
`∀f c d x. cat_iso f ∧ (f :- c → d) ∧ is_terminal c x ⇒ is_terminal d (f@@x)`,
srw_tac [][cat_iso_def] >>
imp_res_tac cat_iso_pair_sym >>
`is_functor f ∧ is_functor g` by fsrw_tac [][cat_iso_pair_def] >>
`(f ≈> g) ∧ (g ≈> f)` by fsrw_tac [][cat_iso_pair_def] >>
`faithful g` by metis_tac [cat_iso_embedding,embedding_def,cat_iso_def] >>
fsrw_tac [][is_terminal_def,objf_in_obj] >>
qx_gen_tac `y` >> strip_tac >>
`g@@y ∈ f.dom.obj` by metis_tac [objf_in_obj,composable_def] >>
first_x_assum (qspec_then `g@@y` mp_tac) >>
srw_tac [][] >>
imp_res_tac is_functor_is_category >>
fsrw_tac [][EXISTS_UNIQUE_THM] >>
qmatch_assum_rename_tac `h :- g@@y → x -:f.dom` [] >>
`f##h :- f@@(g@@y) → f@@x -:f.cod` by metis_tac [morf_maps_to,maps_to_def] >>
conj_tac >- metis_tac [functor_comp_objf,cat_iso_pair_def,id_functor_objf,composable_def] >>
qx_gen_tac `h1` >> qx_gen_tac `h2` >> strip_tac >>
fsrw_tac [][faithful_def,cat_iso_pair_def] >>
metis_tac [morf_maps_to,functor_comp_objf,id_functor_objf,composable_def,maps_to_def]);

val cone_cat_def = Define`
  cone_cat f = comma_cat (diagonal_functor f.dom f.cod) (itself_functor f)`;

val is_category_cone_cat = Q.store_thm(
"is_category_cone_cat",
`∀f. is_functor f ⇒ is_category (cone_cat f)`,
srw_tac [][cone_cat_def] >>
imp_res_tac is_functor_is_category >>
match_mp_tac is_category_comma_cat >>
srw_tac [][] >- (
  match_mp_tac is_functor_diagonal_functor >>
  srw_tac [][] ) >>
match_mp_tac is_functor_itself_functor >>
srw_tac [][]);
val _ = export_rewrites["is_category_cone_cat"];

val _ = type_abbrev("cone",``:(γ,unit,(α,β,γ,δ) nat_trans) morphism``);
val _ = type_abbrev("cone_mor",``:((α,β,γ,δ) cone, (γ,δ) mor # (unit, unit) mor) mor``);
val _ = overload_on("vertex",``λ(c:(α,β,γ,δ)cone). c.dom``);
val _ = overload_on("proj",``λ(c:(α,β,γ,δ)cone) x. c.map@+x``);
val _ = overload_on("is_cone",``λd c. c ∈ (cone_cat d).obj``);
val _ = overload_on("is_cone_mor",``λd f. f ∈ (cone_cat d).mor``);

val vertex_obj = Q.store_thm(
"vertex_obj",
`∀d l c. is_cone d l ∧ (c = d.cod) ⇒ vertex l ∈ c.obj`,
srw_tac [][cone_cat_def,is_comma_cat_obj_def]);
val _ = export_rewrites["vertex_obj"];

val proj_maps_to = Q.store_thm(
"proj_maps_to",
`∀d l x a b c. is_functor d ∧ l ∈ (cone_cat d).obj ∧ x ∈ d.dom.obj ∧
               (a = vertex l) ∧ (b = d@@x) ∧ (c = d.cod)
  ⇒ proj l x :- a → b -:c`,
srw_tac [][cone_cat_def] >>
fsrw_tac [][is_comma_cat_obj_def] >>
match_mp_tac nt_at_maps_to >>
imp_res_tac is_functor_is_category >>
fsrw_tac [][]);

val is_cone_thm = Q.store_thm(
"is_cone_thm",
`∀d c. is_functor d ⇒
(is_cone d c =
    vertex c ∈ d.cod.obj ∧ extensional (proj c) d.dom.obj ∧
    (c.map :- (K_functor d.dom d.cod (vertex c)) → d) ∧
    (∀x. x ∈ d.dom.obj ⇒ proj c x :- vertex c → d@@x -:d.cod) ∧
    (∀f. f ∈ d.dom.mor ⇒ ((d##f) o proj c f.dom -:d.cod = proj c f.cod)))`,
srw_tac [][cone_cat_def] >>
fsrw_tac [][is_comma_cat_obj_def] >>
imp_res_tac is_functor_is_category >>
EQ_TAC >> strip_tac >- (
  fsrw_tac [][] >>
  imp_res_tac is_nat_trans_def >>
  fsrw_tac [][extensional_def,extensional_nat_trans_def] >>
  qpat_assum `c.map.dom = X` mp_tac >>
  fsrw_tac [][nat_trans_axioms_def] >>
  strip_tac >>
  conj_tac >- (
    srw_tac [][] >>
    first_x_assum (qspec_then `x` mp_tac) >>
    fsrw_tac [][] ) >>
  srw_tac [][] >>
  first_x_assum (qspecl_then [`f`,`f.dom`,`f.cod`] mp_tac) >>
  fsrw_tac [][] >>
  first_x_assum (qspec_then `f.cod` mp_tac) >>
  srw_tac [][maps_to_in_def]) >>
fsrw_tac [][] >>
srw_tac [][is_nat_trans_def] >- (
  srw_tac [][extensional_nat_trans_def] >>
  fsrw_tac [][extensional_def] ) >>
srw_tac [][nat_trans_axioms_def] >>
`x ∈ c.map.cod.dom.obj ∧ y ∈ c.map.cod.dom.obj` by metis_tac[maps_to_obj] >>
res_tac >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >>
metis_tac []);

val mk_cone_def = Define`
  (mk_cone d v ps : (α,β,γ,δ) cone) =
  <| dom := v; cod := ();
     map := mk_nt <| dom := K_functor d.dom d.cod v;
                     cod := d;
                     map := ps |> |>`;

val mk_cone_dom_cod = Q.store_thm(
"mk_cone_dom_cod",
`∀d v ps. ((mk_cone d v ps).dom = v) ∧
          ((mk_cone d v ps).cod = ())`,
srw_tac [][mk_cone_def]);
val _ = export_rewrites["mk_cone_dom_cod"];

val mk_cone_proj = Q.store_thm(
"mk_cone_proj",
`∀d v ps. (proj (mk_cone d v ps) = restrict ps d.dom.obj)`,
srw_tac [][mk_cone_def,FUN_EQ_THM,mk_nt_def]);

val mk_cone_proj_ext = save_thm(
"mk_cone_proj_ext",
GEN_ALL(SIMP_RULE std_ss [FUN_EQ_THM] (SPEC_ALL mk_cone_proj)));

val is_cone_mk_cone = Q.store_thm(
"is_cone_mk_cone",
`∀d v ps. is_functor d ⇒
(is_cone d (mk_cone d v ps) = v ∈ d.cod.obj ∧
  (∀x. x ∈ d.dom.obj ⇒ ps x :- v → d@@x -:d.cod) ∧
  (∀f. f ∈ d.dom.mor ⇒ (ps f.cod = (d##f) o ps f.dom -:d.cod)))`,
srw_tac [][is_cone_thm,mk_cone_proj,EQ_IMP_THM] >>
fsrw_tac [][mk_cone_def,mk_nt_def,restrict_def] >>
imp_res_tac is_functor_is_category >>
imp_res_tac mor_obj >>
srw_tac [][] >>
first_x_assum (qspec_then `f` mp_tac) >>
srw_tac [][]);

val is_cone_mor_thm = Q.store_thm(
"is_cone_mor_thm",
`∀d f. is_functor d ⇒
(is_cone_mor d f =
  is_cone d f.dom ∧ is_cone d f.cod ∧
  (FST f.map) :- (vertex f.dom) → (vertex f.cod) -:d.cod ∧
  ∀x. x ∈ d.dom.obj ⇒ (proj f.dom x = proj f.cod x o (FST f.map) -:d.cod))`,
srw_tac [][] >>
EQ_TAC >> strip_tac >- (
  Q.ISPECL_THEN [`cone_cat d`,`f`] mp_tac mor_obj >>
  fsrw_tac [][cone_cat_def] >>
  fsrw_tac [][is_comma_cat_mor_def] >>
  qpat_assum `nt1 = nt2` mp_tac >>
  qpat_assum `X ≈≈> f.cod.map` mp_tac >>
  `(d = f.dom.map.cod) ∧ (is_nat_trans f.dom.map)` by (
    fsrw_tac [][composable_nts_def] ) >>
  fsrw_tac [][maps_to_in_def] >>
  srw_tac [][] >>
  qmatch_assum_abbrev_tac `kk ≈≈> f.cod.map` >>
  `kk ≈> f.cod.map` by fsrw_tac [][composable_nts_def] >>
  qmatch_assum_abbrev_tac `f.dom.map = nt2` >>
  `f.dom.map@+x = nt2@+x` by srw_tac [][] >>
  srw_tac [][Abbr`nt2`,Abbr`kk`]) >>
imp_res_tac is_cone_thm >>
imp_res_tac is_functor_is_category >>
fsrw_tac [][cone_cat_def] >>
fsrw_tac [][is_comma_cat_mor_def,maps_to_in_def] >>
fsrw_tac [][oneTheory.one] >>
conj_asm1_tac >- (
  fsrw_tac [][composable_nts_def] >>
  fsrw_tac [][is_comma_cat_obj_def] ) >>
conj_asm1_tac >- (
  fsrw_tac [][composable_nts_def] >>
  fsrw_tac [][is_comma_cat_obj_def] ) >>
fsrw_tac [][] >>
qpat_assum `f.dom.map.cod = d` (assume_tac o SYM) >>
`(is_nat_trans f.dom.map)` by (
  full_simp_tac std_ss [composable_nts_def] ) >>
fsrw_tac [][] >>
match_mp_tac nt_eq_thm >>
fsrw_tac [][]);

val mk_cone_mor_def = Define`
  (mk_cone_mor c1 c2 m : (α,β,γ,δ) cone_mor) =
    <| dom := c1; cod := c2; map := (m,ARB) |>`;

val mk_cone_mor_dom_cod = Q.store_thm(
"mk_cone_mor_dom_cod",
`∀c1 c2 m. ((mk_cone_mor c1 c2 m).dom = c1) ∧
           ((mk_cone_mor c1 c2 m).cod = c2)`,
srw_tac [][mk_cone_mor_def]);
val _ = export_rewrites["mk_cone_mor_dom_cod"];

val FST_mk_cone_mor_map = Q.store_thm(
"FST_mk_cone_mor_map",
`∀c1 c2 m. (FST (mk_cone_mor c1 c2 m).map = m)`,
srw_tac [][mk_cone_mor_def]);
val _ = export_rewrites["FST_mk_cone_mor_map"];

val is_cone_mor_mk_cone_mor = Q.store_thm(
"is_cone_mor_mk_cone_mor",
`∀d c1 c2 f. is_functor d ⇒ (
  is_cone_mor d (mk_cone_mor c1 c2 f) =
  is_cone d c1 ∧ is_cone d c2 ∧
  f :- c1.dom → c2.dom -:d.cod ∧
  (∀x. x ∈ d.dom.obj ⇒ (proj c1 x = proj c2 x o f -:d.cod)))`,
srw_tac [][is_cone_mor_thm] >>
srw_tac [][mk_cone_mor_def]);

val is_limit_def = Define`
  is_limit d l = is_functor d ∧ is_terminal (cone_cat d) l`;

val is_limit_is_cone = Q.store_thm(
"is_limit_is_cone",
`∀d l. is_limit d l ⇒ is_cone d l`,
srw_tac [][is_limit_def,is_terminal_def]);
val _ = export_rewrites["is_limit_is_cone"];

val limit_universal = Q.store_thm(
"limit_universal",
`∀d l c. is_limit d l ∧ c ∈ (cone_cat d).obj ⇒
  ∃!m. m :- c → l -:(cone_cat d)`,
srw_tac [][is_limit_def,is_terminal_def]);

val cone_cat_maps_to = Q.store_thm(
"cone_cat_maps_to",
`∀m c1 c2 d. is_functor d ⇒
(m :- c1 → c2 -:cone_cat d =
   (m :- c1 → c2) ∧ (is_cone d c1) ∧ (is_cone d c2) ∧
   (FST m.map) :- vertex c1 → vertex c2 -:d.cod ∧
   (∀x. x ∈ d.dom.obj ⇒ (proj m.dom x = proj m.cod x o (FST m.map) -:d.cod)) ∧
   (∀f. f ∈ d.dom.mor ⇒
     (((d##f) o proj c2 f.dom -:d.cod) o (FST m.map) -:d.cod =
      proj c2 f.cod o (FST m.map) -:d.cod)))`,
rpt strip_tac >> EQ_TAC >- (
  strip_tac >>
  imp_res_tac maps_to_in_def >>
  imp_res_tac is_cone_mor_thm >>
  fsrw_tac [][] >> srw_tac [][] >>
  qabbrev_tac `co = m.cod` >>
  qabbrev_tac `n = co.map` >>
  qabbrev_tac `h = FST m.map` >>
  AP_TERM_TAC >>
  Q.ISPECL_THEN [`n`,`n.dom`,`n.cod`,`d.cod`,`f`,`f.dom`,`f.cod`]
    mp_tac (GSYM naturality) >>
  fsrw_tac [][cone_cat_def] >>
  fsrw_tac [][maps_to_in_def,is_comma_cat_obj_def] >>
  srw_tac [][] >>
  imp_res_tac is_functor_is_category >>
  srw_tac [][] >>
  match_mp_tac id_comp1 >>
  `n @+ f.cod :- n.dom@@f.cod → d@@f.cod -:d.cod` by (
    match_mp_tac nt_at_maps_to >>
    map_every qexists_tac [`n.dom`,`d`] >>
    srw_tac [][] ) >>
  fsrw_tac [][maps_to_in_def]) >>
strip_tac >>
srw_tac [][maps_to_in_def] >>
fsrw_tac [][is_cone_mor_thm]);

(* stylistic decision to be made: should predicates be defined to include all
of their assumptions, e.g. is_category of the appropriate fields of a record?
composability of functors/nat_trans would be an exception, unless you overload
notation on those types...
is_functor_is_category (etc.) should probably be made a rewrite.

alternatively: remove all these assumptions from definitions, possibly renaming
the definitions with a "pre_", and add separate stronger predicates (without the "pre_")
that add the extra assumptions.
*)

val has_limits_def = Define`
  has_limits s c = ∀d. is_functor d ∧ (d :- s → c) ⇒ ∃l. is_limit d l`;

(*
val functor_cat_pointwise_limits = Q.store_thm(
"functor_cat_pointwise_limits", (* Mac Lane p 111*)
`∀D J P X τ. is_functor D ∧ (D :- J → [P→X]) ∧
  (∀p. p ∈ P.obj ⇒ is_limit ((eval_functor P X p) ◎ D) (τ p)) ⇒
    (∃L. is_functor L ∧ (L :- P → X) ∧
         (∀p. p ∈ P.obj ⇒ (L@@p = vertex (τ p))) ∧
         let t = λL. (mk_nt <|dom := (diagonal_functor J [P→X])@@L; cod := D;
                              map := λj. mk_nt <|dom := ((diagonal_functor J [P→X])@@L)@@j; cod := D@@j;
                                                 map := λp. proj (τ p) j|> |>) in
         (is_nat_trans (t L)) ∧
         (∀L'. is_functor L' ∧ (L' :- P → X) ∧ (∀p. p ∈ P.obj ⇒ (L'@@p = vertex (τ p))) ∧ is_nat_trans (t L') ⇒ (L' = L)) ∧
         (is_limit D (mk_cone D L ((t L).map))))`,
srw_tac [][] >>
limit_universal
qexists_tac `mk_functor <|dom:=P; cod:=X; map:= use the unique maps |>`
);

val functor_cat_has_limits = Q.store_thm(
"functor_cat_has_limits",
`∀c j v. is_category c ∧ is_category j ∧ is_category v ∧
  has_limits j v ⇒ has_limits j [c→v]`,
srw_tac [][has_limits_def] >>
fsrw_tac [][GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
qabbrev_tac `j = d.dom` >>
qabbrev_tac `τ = λp. f (eval_functor c v p ◎ d)` >>
`∀p. p ∈ c.obj ⇒ is_limit (eval_functor c v p ◎ d) (τ p)` by
  srw_tac [][Abbr`τ`] >>
Q.ISPECL_THEN [`d`,`j`,`c`,`v`,`τ`] mp_tac functor_cat_pointwise_limits >>
srw_tac [][LET_THM] >>
metis_tac []);
*)

(*
val _ = overload_on("empty_diagram",``λc. discrete_functor {} c ARB``);

val is_functor_empty_diagram = Q.store_thm(
"is_functor_empty_diagram",
`∀c. is_category c ⇒ is_functor (empty_diagram c)`,
srw_tac [][is_functor_discrete_functor]);
val _ = export_rewrites["is_functor_empty_diagram"];

val limit_empty_diagram_terminal = Q.store_thm(
"limit_empty_diagram_terminal",
`∀c. is_category c ⇒ (is_limit (empty_diagram c) = is_terminal c o vertex)`,
srw_tac [][FUN_EQ_THM,is_limit_def] >>
srw_tac [][is_terminal_def,is_cone_thm,EQ_IMP_THM] >- (
  fsrw_tac [][is_cone_thm]
why bother proving this?
*)

val _ = overload_on("product_diagram",``λc a b. discrete_functor {1;2} c (λn. if n = 1 then a else b)``);

val is_functor_product_diagram = Q.store_thm(
"is_functor_product_diagram",
`∀c a b. is_category c ∧ a ∈ c.obj ∧ b ∈ c.obj ⇒ is_functor (product_diagram c a b)`,
srw_tac [][] >>
match_mp_tac is_functor_discrete_functor >>
srw_tac [][]);

val is_binary_product_thm = Q.store_thm(
"is_binary_product_thm",
`∀c a b l. is_category c ∧ a ∈ c.obj ∧ b ∈ c.obj ⇒
  (is_limit (product_diagram c a b) l =
   ∃ab π1 π2.
     (l = mk_cone (product_diagram c a b) ab (λn. if n = 1 then π1 else π2)) ∧
     π1 :- ab → a -:c ∧
     π2 :- ab → b -:c ∧
     ∀p p1 p2.
       p1 :- p → a -:c ∧
       p2 :- p → b -:c ⇒
         ∃!m. m :- p → ab -:c ∧
           (π1 o m -:c = p1) ∧
           (π2 o m -:c = p2))`,
rpt strip_tac >>
qabbrev_tac `d = product_diagram c a b` >>
`is_functor d` by (srw_tac [][is_functor_product_diagram,Abbr`d`]) >>
EQ_TAC >- (
  strip_tac >>
  map_every qexists_tac [`vertex l`,`proj l 1`,`proj l 2`] >>
  conj_tac >- (
    fsrw_tac [][is_limit_def,mk_cone_def,is_terminal_def] >>
    pop_assum (K ALL_TAC) >>
    pop_assum mp_tac >>
    srw_tac [][is_cone_thm] >>
    fsrw_tac [][morphism_component_equality,oneTheory.one] >>
    srw_tac [][mk_nt_def,restrict_def,FUN_EQ_THM] >>
    fsrw_tac [][extensional_def] >>
    unabbrev_all_tac >>
    srw_tac [][] ) >>
  ntac 2 (conj_asm1_tac >- (
    match_mp_tac proj_maps_to >>
    qexists_tac `d` >>
    srw_tac [][Abbr`d`] )) >>
  srw_tac [][] >>
  qabbrev_tac `co = mk_cone d p (λn. if n = 1 then p1 else p2)` >>
  `co ∈ (cone_cat d).obj` by (
    qunabbrev_tac `co` >>
    fsrw_tac [][is_cone_mk_cone] >>
    imp_res_tac maps_to_obj >>
    qunabbrev_tac `d` >>
    fsrw_tac [][maps_to_in_def] >>
    srw_tac [][] >> fsrw_tac [][] ) >>
  Q.ISPECL_THEN [`d`,`l`,`co`] mp_tac limit_universal >>
  srw_tac [][EXISTS_UNIQUE_THM] >- (
    pop_assum (K ALL_TAC) >>
    pop_assum mp_tac >>
    srw_tac [][cone_cat_maps_to] >>
    qexists_tac `FST m.map` >>
    pop_assum (K ALL_TAC) >>
    pop_assum mp_tac >>
    unabbrev_all_tac >>
    fsrw_tac [][mk_cone_proj_ext] >>
    srw_tac [][restrict_def] >|[
      pop_assum (qspec_then `1` mp_tac),
      pop_assum (qspec_then `2` mp_tac)] >>
    srw_tac [][] ) >>
  qmatch_rename_tac `ma = mb` [] >>
  qabbrev_tac `mma = mk_cone_mor co l ma` >>
  qabbrev_tac `mmb = mk_cone_mor co l mb` >>
  `mma :- co → l -:cone_cat d` by (
    srw_tac [][maps_to_in_def,Abbr`mma`] >>
    srw_tac [][is_cone_mor_mk_cone_mor] >- (
      srw_tac [][Abbr`co`,Abbr`d`] ) >>
    pop_assum mp_tac >>
    srw_tac [][Abbr`d`,Abbr`co`,mk_cone_proj_ext,restrict_def] ) >>
  `mmb :- co → l -:cone_cat d` by (
    srw_tac [][maps_to_in_def,Abbr`mmb`] >>
    srw_tac [][is_cone_mor_mk_cone_mor] >- (
      srw_tac [][Abbr`co`,Abbr`d`] ) >>
    pop_assum mp_tac >>
    srw_tac [][Abbr`d`,Abbr`co`,mk_cone_proj_ext,restrict_def] ) >>
  `mma = mmb` by res_tac >>
  fsrw_tac [][Abbr`mma`,Abbr`mmb`,mk_cone_mor_def]) >>
srw_tac [][is_limit_def] >>
fsrw_tac [][is_terminal_def] >>
conj_asm1_tac >- (
  imp_res_tac maps_to_obj >>
  srw_tac [][is_cone_mk_cone,Abbr`d`] >> srw_tac [][] >>
  fsrw_tac [][maps_to_in_def] ) >>
qmatch_assum_abbrev_tac `is_cone d co` >>
qx_gen_tac `c2` >> strip_tac >>
Q.ISPECL_THEN [`d`,`c2`] mp_tac is_cone_thm >>
srw_tac [DNF_ss][Abbr`d`] >>
first_x_assum (qspecl_then [`c2.dom`,`proj c2 1`,`proj c2 2`] mp_tac) >>
srw_tac [][EXISTS_UNIQUE_THM] >- (
  pop_assum (K ALL_TAC) >>
  qexists_tac `mk_cone_mor c2 co m` >>
  srw_tac [][cone_cat_maps_to,Abbr`co`,mk_cone_proj_ext,restrict_def] >>
  srw_tac [][] >> fsrw_tac [][maps_to_in_def] ) >>
qmatch_rename_tac `f1 = f2` [] >>
first_x_assum (qspecl_then [`FST f1.map`,`FST f2.map`] assume_tac) >>
qsuff_tac `FST f1.map = FST f2.map` >- (
  simp_tac std_ss [morphism_component_equality] >>
  fsrw_tac [][maps_to_in_def] >>
  Cases_on `f1.map` >> Cases_on `f2.map` >> srw_tac [][] >>
  srw_tac [][morphism_component_equality] ) >>
first_x_assum match_mp_tac >>
unabbrev_all_tac >>
ntac 2 (pop_assum mp_tac) >>
fsrw_tac [][maps_to_in_def,is_cone_mor_thm] >>
strip_tac >> strip_tac >>
first_assum (qspec_then `1` mp_tac) >>
first_x_assum (qspec_then `2` mp_tac) >>
first_assum (qspec_then `1` mp_tac) >>
first_x_assum (qspec_then `2` mp_tac) >>
fsrw_tac [][mk_cone_proj_ext,restrict_def]);

val has_binary_products_def = Define`
  has_binary_products c = has_limits (discrete_cat {1;2}) c`;

val has_binary_products_thm = Q.store_thm(
"has_binary_products_thm",
`∀c. is_category c ⇒
(has_binary_products c =
  ∀a b. a ∈ c.obj ∧ b ∈ c.obj ⇒
  ∃l. is_limit (product_diagram c a b) l)`,
srw_tac [][has_binary_products_def,has_limits_def,EQ_IMP_THM] >- (
  first_x_assum match_mp_tac >>
  srw_tac [][is_functor_product_diagram] ) >>
first_x_assum (qspecl_then [`d@@1`,`d@@2`] mp_tac) >>
`d@@1 ∈ d.cod.obj ∧ d@@2 ∈ d.cod.obj` by srw_tac [][objf_in_obj] >>
srw_tac [][] >>
qmatch_assum_abbrev_tac `is_limit d' l` >>
qsuff_tac `d' = d` >- metis_tac [] >>
match_mp_tac functor_eq_thm >>
srw_tac [][Abbr`d'`,is_functor_product_diagram] >>
fsrw_tac [][] >>
match_mp_tac (GSYM morf_discrete_mor) >>
qexists_tac `{1;2}` >> srw_tac [][]);

val binary_product_projections_exist_thm = Q.store_thm(
"binary_product_projections_exist_thm",
`∃f1 f2 f3. ∀c a b. is_category c ∧ a ∈ c.obj ∧ b ∈ c.obj ∧ (∃l. is_limit (product_diagram c a b) l) ⇒
  f2 c a b :- f1 c a b → a -:c ∧
  f3 c a b :- f1 c a b → b -:c ∧
  ∀p p1 p2.
    p1 :- p → a -:c ∧ p2 :- p → b -:c ⇒
    ∃!m. m :- p → f1 c a b -:c ∧ (f2 c a b o m -:c = p1) ∧ (f3 c a b o m -:c = p2)`,
srw_tac [][GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
pop_assum mp_tac >> srw_tac [][is_binary_product_thm] >>
map_every qexists_tac [`ab`,`π1`,`π2`] >>
srw_tac [][]);

val binary_product_projections_def = new_specification(
"binary_product_projections_def",
["binary_product","binary_product_proj1","binary_product_proj2"],
binary_product_projections_exist_thm);

val pair_morphism_def = new_specification(
"pair_morphism_def",
["pair_morphism"],
binary_product_projections_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT2
|> SIMP_RULE std_ss [EXISTS_UNIQUE_THM,GSYM LEFT_EXISTS_AND_THM] |> DISCH_ALL
|> Q.GEN `b` |> Q.GEN `a` |> Q.GEN `c`
|> SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM,GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val HS = HardSpace 1

val _ = add_rule {
  term_name = "binary_product_syntax",
  fixity = Infixr 800,
  pp_elements = [HS, TOK "\195\151", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundSameName, (PP.INCONSISTENT, 0))
};

val _ = add_rule {
  term_name = "binary_product_proj1_syntax",
  fixity = TruePrefix 625,
  pp_elements = [TOK "\207\1281", HS, TM, TOK"\195\151", TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundSameName, (PP.INCONSISTENT, 0))
};

val _ = add_rule {
  term_name = "binary_product_proj2_syntax",
  fixity = TruePrefix 625,
  pp_elements = [TOK "\207\1282", HS, TM, TOK"\195\151", TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundSameName, (PP.INCONSISTENT, 0))
};

val _ = add_rule {
  term_name = "pair_morphism_syntax",
  fixity = TruePrefix 625,
  pp_elements = [TOK "\226\159\168", TM, TOK ",", TM, TOK "\226\159\169-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundSameName, (PP.INCONSISTENT, 0))
};

val _ = overload_on("binary_product_syntax",``λa b c. binary_product c a b``);
val _ = overload_on("binary_product_proj1_syntax",``λa b c. binary_product_proj1 c a b``);
val _ = overload_on("binary_product_proj2_syntax",``λa b c. binary_product_proj2 c a b``);
val _ = overload_on("pair_morphism_syntax",``λf g c. pair_morphism c f.cod g.cod f.dom f g``);
val _ = overload_on("binary_product_syntax", ``λf g c. pair_morphism_syntax (f o (π1 f.dom × g.dom -:c) -:c) (g o (π2 f.dom × g.dom -:c) -:c) c``);

val binary_product_obj = Q.store_thm(
"binary_product_obj",
`∀c x y. is_category c ∧ (∃l. is_limit (product_diagram c x y) l) ∧ x ∈ c.obj ∧ y ∈ c.obj ⇒ x × y -:c ∈ c.obj`,
metis_tac [binary_product_projections_def,maps_to_obj]);
val _ = export_rewrites["binary_product_obj"];

val pi_maps_to = Q.store_thm(
"pi_maps_to",
`∀c a b. is_category c ∧ (∃l. is_limit (product_diagram c a b) l) ∧ a ∈ c.obj ∧ b ∈ c.obj ⇒
  π1 a×b -:c :- a × b -:c → a -:c ∧
  π2 a×b -:c :- a × b -:c → b -:c`,
metis_tac [binary_product_projections_def]);

val pair_morphism_unique = Q.store_thm(
"pair_morphism_unique",
`∀c a b p p1 p2 m. is_category c ∧ (∃l. is_limit (product_diagram c a b) l) ∧ a ∈ c.obj ∧ b ∈ c.obj ∧
  p1 :- p → a -:c ∧ p2 :- p → b -:c ∧
  m :- p → a × b -:c -:c ∧
  ((π1 a×b -:c) o m -:c = p1) ∧
  ((π2 a×b -:c) o m -:c = p2) ⇒
  (m = pair_morphism c a b p p1 p2)`,
metis_tac [pair_morphism_def]);

val binary_product_id = Q.store_thm(
"binary_product_id",
`∀c a b. is_category c ∧ (∃l. is_limit (product_diagram c a b) l) ∧ a ∈ c.obj ∧ b ∈ c.obj ⇒
  (id a × b -:c -:c = (id a -:c) × id b -:c -:c)`,
srw_tac [][] >>
qspecl_then [`c`,`a`,`b`] mp_tac pi_maps_to >> srw_tac [SATISFY_ss][] >>
imp_res_tac maps_to_in_def >>
imp_res_tac maps_to_obj >>
match_mp_tac pair_morphism_unique >>
fsrw_tac [SATISFY_ss][]);

val pair_morphism_maps_to = Q.store_thm(
"pair_morphism_maps_to",
`∀c a b p p1 p2 x y. is_category c ∧ (∃l. is_limit (product_diagram c a b) l) ∧ a ∈ c.obj ∧ b ∈ c.obj ∧
  p1 :- p → a -:c ∧ p2 :- p → b -:c ∧ (x = p) ∧ (y = a × b -:c) ⇒
  pair_morphism c a b p p1 p2 :- x → y -:c`,
metis_tac [pair_morphism_def]);

val pair_pi_id = Q.store_thm(
"pair_pi_id",
`∀c a b. is_category c ∧ (∃l. is_limit (product_diagram c a b) l) ∧ a ∈ c.obj ∧ b ∈ c.obj
  ⇒ (pair_morphism c a b (a × b -:c) (π1 a×b -:c) (π2 a×b -:c) = id a × b -:c -:c)`,
srw_tac [][] >>
match_mp_tac EQ_SYM >>
match_mp_tac pair_morphism_unique >>
fsrw_tac [SATISFY_ss][] >>
conj_asm1_tac >- srw_tac [SATISFY_ss][pi_maps_to] >>
conj_asm1_tac >- srw_tac [SATISFY_ss][pi_maps_to] >>
fsrw_tac [][maps_to_in_def]);

val pi1_comp_pair = Q.store_thm(
"pi1_comp_pair",
`∀c f g p a b. is_category c ∧ a ∈ c.obj ∧ b ∈ c.obj ∧
   (∃l. is_limit (product_diagram c a b) l) ∧
    f :- p → a -:c ∧ g :- p → b -:c
  ⇒ ((π1 a×b -:c) o ⟨f,g⟩-:c -:c = f)`,
metis_tac [pair_morphism_def,maps_to_in_def,maps_to_def])

val pi2_comp_pair = Q.store_thm(
"pi2_comp_pair",
`∀c f g p a b. is_category c ∧ a ∈ c.obj ∧ b ∈ c.obj ∧
   (∃l. is_limit (product_diagram c a b) l) ∧
    f :- p → a -:c ∧ g :- p → b -:c
  ⇒ ((π2 a×b -:c) o ⟨f,g⟩-:c -:c = g)`,
metis_tac [pair_morphism_def,maps_to_in_def,maps_to_def])

val pair_morphism_comp = Q.store_thm(
"pair_morphism_comp",
`∀c f g h. is_category c ∧ h ≈> f -:c ∧ h ≈> g -:c ∧ (∃l. is_limit (product_diagram c f.cod g.cod) l)
 ⇒ ((⟨f,g⟩-:c) o h -:c = ⟨f o h -:c,g o h -:c⟩-:c)`,
srw_tac [][] >>
match_mp_tac pair_morphism_unique >>
qspecl_then [`c`,`h`,`f`,`h.dom`,`f.cod`] mp_tac composable_maps_to >>
qspecl_then [`c`,`h`,`g`,`h.dom`,`g.cod`] mp_tac composable_maps_to >>
fsrw_tac [][] >> ntac 2 strip_tac >>
imp_res_tac maps_to_in_def >>
fsrw_tac [SATISFY_ss][] >>
`⟨f,g⟩-:c :- f.dom → f.cod × g.cod -:c -:c` by (
  match_mp_tac pair_morphism_maps_to >>
  fsrw_tac [SATISFY_ss][] >>
  imp_res_tac maps_to_obj >>
  fsrw_tac [][maps_to_in_def,composable_in_def] ) >>
`h ≈> ⟨f,g⟩-:c -:c` by fsrw_tac [][composable_in_def,maps_to_in_def] >>
qspecl_then [`c`,`f.cod`,`g.cod`] mp_tac pi_maps_to >>
fsrw_tac [SATISFY_ss][maps_to_obj] >> strip_tac >>
`⟨f,g⟩-:c ≈> π2 f.cod×g.cod -:c -:c` by fsrw_tac [][composable_in_def,maps_to_in_def] >>
`⟨f,g⟩-:c ≈> π1 f.cod×g.cod -:c -:c` by fsrw_tac [][composable_in_def,maps_to_in_def] >>
conj_tac >- ( match_mp_tac composable_maps_to >> fsrw_tac [][maps_to_in_def,composable_in_def] ) >>
qspecl_then [`c`,`h`,`⟨f,g⟩-:c`,`π1 f.cod×g.cod -:c`] mp_tac (GSYM comp_assoc) >>
qspecl_then [`c`,`h`,`⟨f,g⟩-:c`,`π2 f.cod×g.cod -:c`] mp_tac (GSYM comp_assoc) >>
srw_tac [][] >>
AP_TERM_TAC >|[
  match_mp_tac pi1_comp_pair,
  match_mp_tac pi2_comp_pair
] >> qexists_tac `f.dom` >>
fsrw_tac [SATISFY_ss][maps_to_in_def,maps_to_obj,composable_in_def]);

val pre_product_functor_def = Define`
  pre_product_functor c y = <|
    dom := c; cod := c; map := λf. f × id y -:c -:c |>`;

val pre_product_functor_components = Q.store_thm(
"pre_product_functor_components",
`∀c x. ((pre_product_functor c x).dom = c) ∧
       ((pre_product_functor c x).cod = c) ∧
       (∀f. (pre_product_functor c x)##f = f × id x-:c -:c)`,
srw_tac [][pre_product_functor_def,morf_def])
val _ = export_rewrites["pre_product_functor_components"];

val pre_product_functor_objf = Q.store_thm(
"pre_product_functor_objf",
`∀c x y. is_category c ∧ (∃l. is_limit (product_diagram c x y) l) ∧ x ∈ c.obj ∧ y ∈ c.obj
⇒ ((pre_product_functor c y)@@x = x × y -:c)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  qexists_tac `x × y -:c` >>
  srw_tac [SATISFY_ss][binary_product_obj,binary_product_id] ) >>
qmatch_assum_abbrev_tac `pair_morphism c a b p p1 p2 = id z -:c` >>
qspecl_then [`c`,`a`,`b`,`p`,`p1`,`p2`] mp_tac pair_morphism_maps_to >>
qspecl_then [`c`,`x`,`y`] mp_tac pi_maps_to >>
fsrw_tac [SATISFY_ss][] >>
strip_tac >>
imp_res_tac maps_to_in_def >>
unabbrev_all_tac >>
fsrw_tac [SATISFY_ss][] >>
srw_tac [][maps_to_in_def]);

val product_functor_def = Define`
  product_functor c x = mk_functor (pre_product_functor c x)`;

val is_functor_product_functor = Q.store_thm(
"is_functor_product_functor",
`∀c y. is_category c ∧ has_binary_products c ∧ y ∈ c.obj ⇒ is_functor (product_functor c y)`,
srw_tac [][product_functor_def] >>
qpat_assum `has_binary_products c` mp_tac >> srw_tac [][has_binary_products_thm] >>
srw_tac [][functor_axioms_def] >- (
  imp_res_tac maps_to_obj >>
  imp_res_tac maps_to_in_def >>
  srw_tac [][pre_product_functor_objf] >>
  match_mp_tac pair_morphism_maps_to >>
  qspecl_then [`c`,`f.dom`,`y`] mp_tac pi_maps_to >>
  fsrw_tac [][] >>
  strip_tac >>
  qmatch_assum_rename_tac `f :- x → w -:c` [] >>
  qspecl_then [`c`,`π1 x×y -:c`,`f`,`x × y-:c`,`x`,`w`] mp_tac maps_to_comp >>
  fsrw_tac [][] >> strip_tac >>
  imp_res_tac maps_to_in_def >>
  fsrw_tac [][])
>- (
  qexists_tac `x × y-:c` >>
  srw_tac [][] >>
  qspecl_then [`c`,`x`,`y`] mp_tac pi_maps_to >>
  fsrw_tac [][] >> strip_tac >>
  fsrw_tac [][maps_to_in_def,pair_pi_id]) >>
qmatch_abbrev_tac `⟨p o q-:c, r o s-:c⟩-:c = (⟨t,u⟩-:c) o (⟨v,w⟩-:c) -:c` >>
`p.dom = f.dom` by (
  unabbrev_all_tac >>
  qspecl_then [`c`,`f`,`g`,`f.dom`,`g.cod`] mp_tac composable_maps_to >>
  srw_tac [][maps_to_in_def] ) >>
srw_tac [][Abbr`r`] >>
qabbrev_tac `a = f.dom` >>
qabbrev_tac `b = g.dom` >>
qpat_assum `Abbrev (p = X)` assume_tac >>
fsrw_tac [][] >>
qspecl_then [`c`,`a`,`y`] mp_tac pi_maps_to >>
qspecl_then [`c`,`b`,`y`] mp_tac pi_maps_to >>
`a ∈ c.obj ∧ b ∈ c.obj` by metis_tac [composable_obj] >>
fsrw_tac [SATISFY_ss][] >> ntac 2 strip_tac >>
`t :- b×y-:c → g.cod -:c` by (
  qunabbrev_tac `t` >>
  match_mp_tac maps_to_comp >>
  qexists_tac `b` >>
  fsrw_tac [][Abbr`b`,composable_in_def] ) >>
`v :- a×y-:c → f.cod -:c` by (
  qunabbrev_tac `v` >>
  match_mp_tac maps_to_comp >>
  qexists_tac `a` >>
  fsrw_tac [][Abbr`a`,composable_in_def] ) >>
`u :- b×y-:c → y -:c` by (
  qunabbrev_tac `u` >>
  match_mp_tac maps_to_comp >>
  qexists_tac `y` >>
  fsrw_tac [][] ) >>
`w :- a×y-:c → y -:c` by (
  qunabbrev_tac `w` >>
  match_mp_tac maps_to_comp >>
  qexists_tac `y` >>
  fsrw_tac [][]) >>
`⟨v,w⟩-:c :- a×y-:c → b×y-:c -:c` by (
  match_mp_tac pair_morphism_maps_to >>
  fsrw_tac [][maps_to_in_def,composable_in_def] ) >>
`t o ⟨v,w⟩-:c -:c = p o q -:c` by (
  qunabbrev_tac `t` >>
  qspecl_then [`c`,`⟨v,w⟩-:c`,`π1 b×y -:c`,`g`] mp_tac comp_assoc >>
  `⟨v,w⟩-:c ≈> π1 b×y -:c -:c` by metis_tac [maps_to_composable] >>
  `π1 b×y-:c ≈> g -:c` by metis_tac [maps_to_composable,maps_to_in_def,maps_to_def,composable_in_def] >>
  srw_tac [][] >>
  `(π1 b×y -:c) o ⟨v,w⟩-:c -:c = v` by (
    match_mp_tac pi1_comp_pair >>
    qexists_tac `p.dom × y-:c` >> fsrw_tac [][] >>
    metis_tac [composable_in_def,composable_def] ) >>
  fsrw_tac [][Abbr`p`,Abbr`v`] >>
  match_mp_tac (GSYM comp_assoc) >>
  fsrw_tac [][] >>
  match_mp_tac maps_to_composable >>
  unabbrev_all_tac >>
  metis_tac [maps_to_in_def,maps_to_def,composable_in_def] ) >>
`u o ⟨v,w⟩-:c -:c = w` by (
  qunabbrev_tac `u` >>
  qspecl_then [`c`,`⟨v,w⟩-:c`,`π2 b×y -:c`,`id y -:c`] mp_tac comp_assoc >>
  `⟨v,w⟩-:c ≈> π2 b×y-:c -:c` by metis_tac [maps_to_composable] >>
  `π2 b×y -:c ≈> id y -:c -:c` by metis_tac [maps_to_composable,id_maps_to] >>
  srw_tac [][] >>
  `(π2 b×y -:c) o ⟨v,w⟩-:c -:c = w` by (
    match_mp_tac pi2_comp_pair >>
    qexists_tac `p.dom × y-:c` >> fsrw_tac [][] >>
    metis_tac [composable_in_def,composable_def] ) >>
  fsrw_tac [][maps_to_in_def] ) >>
ntac 2 (pop_assum (mp_tac o SYM)) >>
qabbrev_tac `h = ⟨v,w⟩-:c` >>
srw_tac [][] >>
match_mp_tac (GSYM pair_morphism_comp) >>
fsrw_tac [][] >>
conj_tac >- metis_tac [maps_to_composable] >>
conj_tac >- metis_tac [maps_to_composable] >>
srw_tac [][DECIDE ``(1 = n) = (n = 1)``] >>
first_x_assum match_mp_tac >>
fsrw_tac [][maps_to_in_def]);

val _ = export_theory ();
