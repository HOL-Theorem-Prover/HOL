open HolKernel Parse boolLib bossLib lcsymtacs categoryTheory;

val _ = new_theory "functor";

val _ = type_abbrev("functor",
``:(('a,'b) category, ('c,'d) category, ('a,'b) mor -> ('c,'d) mor)
   morphism``)

val _ = add_rule {
  term_name = "objf",
  fixity = Infixl 2000,
  pp_elements = [TOK "@@"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val _ = add_rule {
  term_name = "morf",
  fixity = Infixl 2000,
  pp_elements = [TOK "##"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val morf_def = Define`
  G##f = G.map f`;

val objf_def = Define`
  f@@x = @y. y ∈ f.cod.obj ∧ (f##(id x -:f.dom) = id y -:f.cod)`;

val functor_axioms_def = Define`
  functor_axioms G =
  is_category G.dom ∧ is_category G.cod ∧
  (∀f x y. f :- x → y -:G.dom ⇒ G##f :- G@@x → G@@y -:G.cod) ∧
  (∀x. x ∈ G.dom.obj ⇒ ∃y. y ∈ G.cod.obj ∧ (G##(id x -:G.dom) = id y -:G.cod)) ∧
  (∀f g. f ≈> g -:G.dom ⇒ (G##(g o f -:G.dom) = (G##g) o (G##f) -:G.cod))`;

val extensional_functor_def = Define`
  extensional_functor f = extensional f.map f.dom.mor`;

val mk_functor_def = Define`
  mk_functor (f:('a,'b,'c,'d) functor) =
    <| dom := f.dom; cod := f.cod; map := restrict f.map f.dom.mor |>`;

val is_functor_def = Define`
  is_functor f = extensional_functor f ∧ functor_axioms f`;

val functor_eq_thm = Q.store_thm(
"functor_eq_thm",
`∀f g. is_functor f ∧ is_functor g ∧
       (f.dom = g.dom) ∧ (f.cod = g.cod) ∧
       (∀h. h ∈ f.dom.mor ⇒ (f##h = g##h)) ⇒
         (f = g)`,
srw_tac [][morphism_component_equality,FUN_EQ_THM,morf_def] >>
fsrw_tac [][is_functor_def,extensional_functor_def] >>
metis_tac [extensional_def]);

val is_functor_is_category = Q.store_thm(
"is_functor_is_category",
`∀f. is_functor f ⇒ is_category f.dom ∧ is_category f.cod`,
srw_tac [][is_functor_def,functor_axioms_def]);

val maps_to_morf = Q.store_thm(
"maps_to_morf",
`∀G f. is_functor G ∧ f ∈ G.dom.mor ⇒
  G##f :- G@@(f.dom) → G@@(f.cod) -:G.cod`,
srw_tac [][is_functor_def,functor_axioms_def] >>
first_assum match_mp_tac >>
srw_tac [][maps_to_in_def]);

val morf_mor_dom_cod = Q.store_thm(
"morf_mor_dom_cod",
`∀G f. is_functor G ∧ f ∈ G.dom.mor ⇒
 G##f ∈ G.cod.mor ∧
 ((G##f).dom = G@@(f.dom)) ∧
 ((G##f).cod = G@@(f.cod))`,
rpt strip_tac >>
imp_res_tac maps_to_morf >>
fsrw_tac [][maps_to_in_def]);

val composable_morf = Q.store_thm(
"composable_morf",
`∀G f g. is_functor G ∧ f ≈> g -:G.dom ⇒ G##f ≈> G##g -:G.cod`,
rpt strip_tac >>
imp_res_tac is_functor_is_category >>
match_mp_tac maps_to_composable >>
fsrw_tac [][composable_in_def] >>
imp_res_tac maps_to_morf >>
metis_tac []);

val morf_comp = Q.store_thm(
"morf_comp",
`∀G c1 c2 f g. is_functor G ∧ (G :- c1 → c2) ∧ f ≈> g -:c1 ⇒
  (G##(g o f -:c1) = ((G##g) o (G##f) -:c2))`,
srw_tac [][is_functor_def,functor_axioms_def] >>
srw_tac [][]);

val morf_composable = Q.store_thm(
"morf_composable",
`∀G c1 c2 f g. is_functor G ∧ (G :- c1 → c2) ∧ f ≈> g -:c1
  ⇒ G##f ≈> G##g -:c2`,
srw_tac [][] >> srw_tac [][composable_morf]);

val morf_maps_to = Q.store_thm(
"morf_maps_to",
`∀G c1 c2 f x y a b. is_functor G ∧ (G :- c1 → c2) ∧ f :- x → y -:c1 ∧ (a = G@@x) ∧ (b = G@@y)
  ⇒ G##f :- a → b -:c2`,
srw_tac [][Once maps_to_in_def] >>
srw_tac [][maps_to_morf]);

val morf_id = Q.store_thm(
"morf_id",
`∀G c1 c2 x. is_functor G ∧ (G :- c1 → c2) ∧ x ∈ c1.obj ⇒
 (G##(id x -:c1) = id (G@@x) -:c2)`,
srw_tac [][is_functor_def,functor_axioms_def,objf_def,morf_def] >>
SELECT_ELIM_TAC >> fsrw_tac [][]);

val mk_functor_dom = Q.store_thm(
"mk_functor_dom",
`∀f. (mk_functor f).dom = f.dom`,
srw_tac [][mk_functor_def]);

val mk_functor_cod = Q.store_thm(
"mk_functor_cod",
`∀f. (mk_functor f).cod = f.cod`,
srw_tac [][mk_functor_def]);

val mk_functor_map = Q.store_thm(
"mk_functor_map",
`∀f x. x ∈ f.dom.mor ⇒ ((mk_functor f).map x = f.map x)`,
srw_tac [][mk_functor_def,restrict_def]);

val mk_functor_morf = Q.store_thm(
"mk_functor_morf",
`∀f x. x ∈ f.dom.mor ⇒ ((mk_functor f)##x = f##x)`,
srw_tac [][mk_functor_map,morf_def]);

val mk_functor_objf = Q.store_thm(
"mk_functor_objf",
`∀f x. is_category f.dom ∧ x ∈ f.dom.obj ⇒ ((mk_functor f)@@x = f@@x)`,
rpt strip_tac >> imp_res_tac id_mor >>
srw_tac [][objf_def,mk_functor_def,restrict_def,morf_def]);

val _ = export_rewrites
["mk_functor_dom","mk_functor_cod","mk_functor_map",
 "mk_functor_objf","mk_functor_morf"];

val is_functor_mk_functor = Q.store_thm(
"is_functor_mk_functor",
`∀f. is_functor (mk_functor f) ⇔ functor_axioms f`,
srw_tac [][is_functor_def,extensional_functor_def] >>
srw_tac [][Once mk_functor_def] >>
srw_tac [][functor_axioms_def] >>
EQ_TAC >> strip_tac >> fsrw_tac [][] >>
imp_res_tac id_mor >>
imp_res_tac comp_mor_dom_cod >>
imp_res_tac is_category_def >>
fsrw_tac [][category_axioms_def] >>
fsrw_tac [][maps_to_in_def,composable_in_def]);
val _ = export_rewrites["is_functor_mk_functor"];

val id_functor_def = Define`
  id_functor c = mk_functor <| dom := c; cod := c; map := I |>`;

val is_functor_id_functor = Q.store_thm(
"is_functor_id_functor",
`∀c. is_category c ⇒ is_functor (id_functor c)`,
srw_tac [][id_functor_def] >>
reverse (srw_tac [][functor_axioms_def,maps_to_in_def,morf_def,objf_def]) >- (
  qexists_tac `x` >> srw_tac [][] ) >> (
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  full_simp_tac std_ss [is_category_def,category_axioms_def] >>
  metis_tac [] ) >>
imp_res_tac id_inj >>
full_simp_tac std_ss [is_category_def,category_axioms_def]));

val id_functor_dom = Q.store_thm(
"id_functor_dom",
`∀c. (id_functor c).dom = c`,
srw_tac [][id_functor_def]);

val id_functor_cod = Q.store_thm(
"id_functor_cod",
`∀c. (id_functor c).cod = c`,
srw_tac [][id_functor_def]);

val id_functor_map = Q.store_thm(
"id_functor_map",
`∀c f. f ∈ c.mor ⇒ ((id_functor c).map f = f)`,
srw_tac [][id_functor_def]);

val id_functor_morf = Q.store_thm(
"id_functor_morf",
`∀c f. f ∈ c.mor ⇒ ((id_functor c)##f = f)`,
srw_tac [][id_functor_map,morf_def]);

val id_functor_objf = Q.store_thm(
"id_functor_objf",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ ((id_functor c)@@x = x)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
srw_tac [][id_functor_cod,id_functor_dom] >>
metis_tac [id_functor_morf,id_mor,id_inj,morf_def]);

val _ = export_rewrites
["is_functor_id_functor","id_functor_dom","id_functor_cod",
 "id_functor_map","id_functor_morf","id_functor_objf"];

val K_functor_def = Define`
  K_functor c1 c2 x = mk_functor <|
    dom := c1; cod := c2; map := K (id x -:c2) |>`;

val is_functor_K_functor = Q.store_thm(
"is_functor_K_functor",
`∀c1 c2 x.  is_category c1 ∧ is_category c2 ∧
   ((∀y. y ∉ c1.obj) ∨ (x ∈ c2.obj))
⇒ is_functor (K_functor c1 c2 x)`,
srw_tac [][K_functor_def] >- (
  srw_tac [][functor_axioms_def,morf_def] >>
  metis_tac [composable_obj,maps_to_obj] ) >>
srw_tac [][functor_axioms_def,morf_def,EQ_IMP_THM] >- (
  imp_res_tac id_mor >>
  imp_res_tac id_dom_cod >>
  srw_tac [][maps_to_in_def] >>
  srw_tac [][objf_def,morf_def] >>
  SELECT_ELIM_TAC >>
  metis_tac [id_inj] ) >>
metis_tac []);

val K_functor_dom = Q.store_thm(
"K_functor_dom",
`∀c1 c2 x. (K_functor c1 c2 x).dom = c1`,
srw_tac [][K_functor_def]);

val K_functor_cod = Q.store_thm(
"K_functor_cod",
`∀c1 c2 x. (K_functor c1 c2 x).cod = c2`,
srw_tac [][K_functor_def]);

val K_functor_morf = Q.store_thm(
"K_functor_morf",
`∀c1 c2 x f. f ∈ c1.mor ⇒ ((K_functor c1 c2 x)##f = id x -:c2)`,
srw_tac [][K_functor_def,mk_functor_def,restrict_def,morf_def]);

val K_functor_objf = Q.store_thm(
"K_functor_objf",
`∀c1 c2 x y. is_category c1 ∧ is_category c2 ∧ x ∈ c2.obj ∧ y ∈ c1.obj
⇒ ((K_functor c1 c2 x)@@y = x)`,
srw_tac [][objf_def,morf_def] >>
SELECT_ELIM_TAC >>
srw_tac [][K_functor_def,mk_functor_def,restrict_def] >>
imp_res_tac id_mor >>
metis_tac [id_inj]);

val _ = export_rewrites["is_functor_K_functor",
"K_functor_dom","K_functor_cod",
"K_functor_morf","K_functor_objf"];

val K_functor_maps_to = Q.store_thm(
"K_functor_maps_to",
`∀c1 c2 x. is_category c1 ∧ is_category c2 ∧ x ∈ c2.obj ⇒
  (K_functor c1 c2 x) :- c1 → c2`,
srw_tac [][])
val _ = export_rewrites["K_functor_maps_to"];

val unit_functor_def = Define`
  unit_functor c = K_functor c unit_cat ()`;

val is_functor_unit_functor = Q.store_thm(
"is_functor_unit_functor",
`∀c. is_category c ⇒ is_functor (unit_functor c)`,
srw_tac [][unit_functor_def] >>
match_mp_tac is_functor_K_functor >>
srw_tac [][is_category_unit_cat] >>
srw_tac [][unit_cat_def]);

val objf_in_obj = Q.store_thm(
"objf_in_obj",
`∀f x. is_functor f ∧ x ∈ f.dom.obj ⇒ f@@x ∈ f.cod.obj`,
srw_tac [][objf_def] >>
imp_res_tac is_functor_def >>
fsrw_tac [][functor_axioms_def] >>
SELECT_ELIM_TAC >>
fsrw_tac [][morf_def]);

val functor_comp_def = Define`
  functor_comp (f:('c,'d,'e,'f) functor) (g:('a,'b,'c,'d) functor) =
    mk_functor (compose (λf g. g.map o f.map) g f)`;

val _ = set_fixity "\226\151\142" (Infixr 800);
val _ = overload_on("\226\151\142",``functor_comp``);

val functor_comp_dom_cod = Q.store_thm(
"functor_comp_dom_cod",
`∀f g. (g ≈> f) ⇒ (((f ◎ g).dom = g.dom) ∧ ((f ◎ g).cod = f.cod))`,
srw_tac [][functor_comp_def]);
val _ = export_rewrites["functor_comp_dom_cod"];

val functor_comp_morf = Q.store_thm(
"functor_comp_morf",
`∀X Y f. (X ≈> Y) ∧ f ∈ X.dom.mor ⇒ ((Y ◎ X)##f = Y##(X##f))`,
srw_tac [][morf_def,functor_comp_def,mk_functor_def,restrict_def]);
val _ = export_rewrites["functor_comp_morf"];

val functor_comp_id = Q.store_thm(
"functor_comp_id",
`∀f g x. x ∈ f.dom.obj ∧ is_functor f ∧ is_functor g ∧ (f ≈> g) ⇒
  (g@@(f@@x)) ∈ g.cod.obj ∧
  ((g◎f)##(id x -:f.dom) = id(g@@(f@@x)) -:g.cod)`,
srw_tac [][] >- (
  imp_res_tac is_functor_def >>
  imp_res_tac functor_axioms_def >>
  srw_tac [][objf_def] >>
  SELECT_ELIM_TAC >> srw_tac [][] >>
  SELECT_ELIM_TAC >> srw_tac [][] >>
  fsrw_tac [][morf_def] >>
  metis_tac [] ) >>
`id x -:f.dom ∈ f.dom.mor` by (
  imp_res_tac is_functor_is_category >>
  imp_res_tac id_mor ) >>
srw_tac [][] >>
metis_tac [objf_in_obj,morf_id,maps_to_def]);

val functor_comp_objf = Q.store_thm(
"functor_comp_objf",
`∀f g x.  is_functor f ∧ is_functor g ∧ (f ≈> g) ∧ x ∈ f.dom.obj
⇒ ((g ◎ f)@@x = g@@(f@@x))`,
srw_tac [][objf_def] >>
Q.ISPECL_THEN [`f`,`g`,`x`] mp_tac functor_comp_id >>
srw_tac [][] >>
pop_assum mp_tac >>
imp_res_tac is_functor_is_category >>
imp_res_tac id_mor >>
fsrw_tac [][morf_def,functor_comp_def,compose_def,restrict_def,mk_functor_def] >>
SELECT_ELIM_TAC >> srw_tac [][] >- metis_tac [] >>
SELECT_ELIM_TAC >> srw_tac [][] >> metis_tac
[morf_def,objf_def,id_inj,objf_in_obj,
 is_functor_is_category,morf_id,
 maps_to_def,compose_def] );
val _ = export_rewrites["functor_comp_objf"];

val functor_comp_comp = Q.store_thm(
"functor_comp_comp",
`∀X Y f g. f ≈> g -: X.dom ∧ (X ≈> Y) ∧ is_functor X ∧ is_functor Y ⇒
  ((Y ◎ X)##(g o f -: X.dom) =
   (Y##(X##g)) o Y##(X##f) -: Y.cod)`,
rpt strip_tac >>
`g o f -:X.dom ∈ X.dom.mor` by (
  imp_res_tac is_functor_is_category >>
  imp_res_tac comp_mor_dom_cod ) >>
srw_tac [][] >>
`X :- X.dom → X.cod` by srw_tac [][] >>
`X##(g o f -:X.dom) = (X##g) o X##f -:X.cod` by imp_res_tac morf_comp >>
srw_tac [][] >>
`Y :- Y.dom → Y.cod` by srw_tac [][] >>
match_mp_tac morf_comp >>
fsrw_tac [][] >>
match_mp_tac morf_composable >>
metis_tac [maps_to_def]);

val functor_comp_maps_to = Q.store_thm(
"functor_comp_maps_to",
`∀X Y f x y. f :- x → y -:X.dom ∧ (X ≈> Y) ∧ is_functor X ∧ is_functor Y ⇒
  (Y ◎ X)## f :- Y@@(X@@x) → Y@@(X@@y) -:Y.cod`,
rpt strip_tac >>
`f ∈ X.dom.mor` by imp_res_tac maps_to_in_def >>
srw_tac [][] >>
match_mp_tac morf_maps_to >>
map_every qexists_tac [`Y.dom`,`X@@x`,`X@@y`] >> srw_tac [][] >>
match_mp_tac morf_maps_to >>
map_every qexists_tac [`X.dom`,`x`,`y`] >> fsrw_tac [][]);

val functor_comp_extensional = Q.store_thm(
"functor_comp_extensional",
`∀f g. extensional_functor (f ◎ g)`,
srw_tac [][extensional_functor_def,mk_functor_def,functor_comp_def]);
val _ = export_rewrites["functor_comp_extensional"];

val is_functor_comp = Q.store_thm(
"is_functor_comp",
`∀f g. is_functor f ∧ is_functor g ∧ (f ≈> g) ⇒ is_functor (g ◎ f)`,
rpt strip_tac >>
simp_tac std_ss [is_functor_def,functor_comp_extensional] >>
imp_res_tac is_functor_is_category >>
asm_simp_tac std_ss [functor_axioms_def] >>
conj_tac >- srw_tac [][] >>
conj_tac >- srw_tac [][] >>
conj_tac >- (
  srw_tac [][] >>
  imp_res_tac maps_to_in_def >>
  imp_res_tac maps_to_obj >>
  imp_res_tac functor_comp_maps_to >>
  ntac 3 (pop_assum mp_tac) >>
  srw_tac [][] ) >>
srw_tac [][] >- (
  imp_res_tac composable_def >>
  imp_res_tac id_mor >>
  srw_tac [][] >>
  metis_tac [morf_id,objf_in_obj,maps_to_def] ) >>
qmatch_assum_rename_tac `x ≈> y -:f.dom` [] >>
Q.ISPECL_THEN [`f`,`f.dom`,`f.cod`,`x`,`y`] mp_tac morf_comp >>
imp_res_tac comp_mor_dom_cod >>
srw_tac [][] >>
match_mp_tac morf_comp >>
fsrw_tac [][] >>
match_mp_tac morf_composable >>
metis_tac [maps_to_def]);
val _ = export_rewrites["is_functor_comp"];

val functor_comp_id_functor = Q.store_thm(
"functor_comp_id_functor",
`∀f c. (is_functor f ∧ (c = f.dom) ⇒ (f ◎ id_functor c = f)) ∧
       (is_functor f ∧ (c = f.cod) ⇒ (id_functor c ◎ f = f))`,
srw_tac [][morphism_component_equality] >>
srw_tac [][functor_comp_def,mk_functor_def,restrict_def] >>
srw_tac [][FUN_EQ_THM] >> srw_tac [][] >>
imp_res_tac is_functor_def >>
imp_res_tac extensional_functor_def >>
fsrw_tac [][extensional_def] >>
fsrw_tac [][functor_axioms_def,morf_def,maps_to_in_def]);

val functor_comp_assoc = Q.store_thm(
"functor_comp_assoc",
`∀f g h. is_functor f ∧ is_functor g ∧ is_functor h ∧
          (h ≈> g) ∧ (g ≈> f)
  ⇒ (f ◎ (g ◎ h) = (f ◎ g) ◎ h)`,
srw_tac [][] >>
match_mp_tac functor_eq_thm >>
srw_tac [][] >>
match_mp_tac (GSYM functor_comp_morf) >>
qmatch_assum_rename_tac `x ∈ h.dom.mor` [] >>
Q.ISPECL_THEN [`h`,`h.dom`,`h.cod`,`x`,`x.dom`,`x.cod`,`h@@x.dom`,`h@@x.cod`] mp_tac morf_maps_to >>
srw_tac [][maps_to_in_def]);

val functor_preserves_iso_pair = Q.store_thm(
"functor_preserves_iso_pair",
`∀G f g c1 c2. is_functor G ∧ (G :- c1 → c2) ∧ iso_pair c1 f g ⇒ iso_pair c2 (G##f) (G##g)`,
rpt strip_tac >>
`g <≃> f-:c1` by metis_tac [iso_pair_sym,is_functor_is_category,maps_to_def] >>
fsrw_tac [][iso_pair_def] >> srw_tac [][] >- (
  match_mp_tac composable_morf >>
  srw_tac [][] )
>- (
  `G##(f o g -:G.dom) = G##(id g.dom -:G.dom)` by srw_tac [][] >>
  qpat_assum `f o g -:G.dom = X` (K ALL_TAC) >>
  qspecl_then [`G`,`G.dom`,`G.cod`,`g`,`f`] mp_tac morf_comp >>
  qspecl_then [`G`,`G.dom`,`G.cod`,`g.dom`] mp_tac morf_id >>
  qspecl_then [`G`,`G.dom`,`G.cod`,`g`,`g.dom`,`g.cod`,`G@@g.dom`,`G@@g.cod`] mp_tac morf_maps_to >>
  imp_res_tac is_functor_is_category >>
  imp_res_tac composable_obj >>
  fsrw_tac [][maps_to_in_def,composable_in_def] ) >>
`G##(g o f -:G.dom) = G##(id f.dom -:G.dom)` by srw_tac [][] >>
qpat_assum `g o f -:G.dom = X` (K ALL_TAC) >>
qspecl_then [`G`,`G.dom`,`G.cod`,`f`,`g`] mp_tac morf_comp >>
qspecl_then [`G`,`G.dom`,`G.cod`,`f.dom`] mp_tac morf_id >>
qspecl_then [`G`,`G.dom`,`G.cod`,`f`,`f.dom`,`f.cod`,`G@@f.dom`,`G@@f.cod`] mp_tac morf_maps_to >>
imp_res_tac is_functor_is_category >>
imp_res_tac composable_obj >>
fsrw_tac [][maps_to_in_def,composable_in_def]);

val functor_preserves_iso = Q.store_thm(
"functor_preserves_iso",
`∀f x y k. is_functor f ∧ (f :- x → y) ∧ iso x k ⇒ iso y (f##k)`,
srw_tac [][iso_def] >>
qexists_tac `f##g` >>
imp_res_tac functor_preserves_iso_pair >>
first_x_assum match_mp_tac >>
srw_tac [][]);

val full_def = Define`
  full f = ∀h a b. a ∈ f.dom.obj ∧ b ∈ f.dom.obj ∧
                   h :- f@@a → f@@b -:f.cod ⇒
                   ∃g. g :- a → b -:f.dom ∧
                       (f##g = h)`;

val faithful_def = Define`
  faithful (f:('a,'b,'c,'d)functor) =
  ∀g h a b. g :- a → b -:f.dom ∧ h :- a → b -:f.dom ∧
   (f##g = f##h) ⇒ (g = h)`;

val embedding_def = Define`
  embedding (f:('a,'b,'c,'d)functor) = full f ∧ faithful f`;

val inj_obj_def = Define`
  inj_obj f = ∀a b. a ∈ f.dom.obj ∧ b ∈ f.dom.obj ∧
    (f@@a = f@@b) ⇒ (a = b)`;

val ess_inj_obj_def = Define`
  ess_inj_obj f = ∀a b. a ∈ f.dom.obj ∧ b ∈ f.dom.obj ∧
    (f@@a = f@@b) ⇒ (a ≅ b -:f.dom)`;

val surj_obj_def = Define`
  surj_obj f = ∀b. b ∈ f.cod.obj ⇒
    ∃a. a ∈ f.dom.obj ∧ (f@@a = b)`;

val ess_surj_obj_def = Define`
  ess_surj_obj f = ∀b. b ∈ f.cod.obj ⇒
    ∃a. a ∈ f.dom.obj ∧ (f@@a) ≅ b -:f.cod`;

val embedding_ess_inj = Q.store_thm(
"embedding_ess_inj",
`∀f. is_functor f ∧ embedding f ⇒ ess_inj_obj f`,
srw_tac [][embedding_def,ess_inj_obj_def,iso_objs_def,iso_pair_between_objs_def] >>
fsrw_tac [][full_def,faithful_def] >>
first_assum (qspecl_then [`id (f@@a) -:f.cod`,`a`,`b`] mp_tac) >>
first_x_assum (qspecl_then [`id (f@@b) -:f.cod`,`b`,`a`] mp_tac) >>
srw_tac [][is_functor_is_category,id_maps_to,objf_in_obj] >>
qmatch_assum_rename_tac `ba :- b → a -:f.dom` [] >>
qmatch_assum_rename_tac `ab :- a → b -:f.dom` [] >>
map_every qexists_tac [`ab`,`ba`] >>
`ab ≈> ba -:f.dom` by metis_tac [maps_to_composable] >>
`ba ≈> ab -:f.dom` by metis_tac [maps_to_composable] >>
fsrw_tac [][iso_pair_def] >>
conj_asm1_tac >- fsrw_tac [][maps_to_in_def] >>
conj_tac >- (
  first_x_assum match_mp_tac >>
  qspecl_then [`f.dom`,`ba`,`ab`,`b`,`b`] mp_tac composable_maps_to >>
  `(ba.dom = b) ∧ (ab.cod = b)` by fsrw_tac [][composable_in_def] >>
  imp_res_tac is_functor_is_category >>
  fsrw_tac [][] >> strip_tac >>
  map_every qexists_tac [`b`,`b`] >>
  fsrw_tac [][] >>
  qspecl_then [`f`,`f.dom`,`f.cod`,`ba`,`ab`] mp_tac morf_comp >>
  qspecl_then [`f`,`f.dom`,`f.cod`,`b`] mp_tac morf_id >>
  fsrw_tac [][objf_in_obj] ) >>
first_x_assum match_mp_tac >>
qspecl_then [`f.dom`,`ab`,`ba`,`a`,`a`] mp_tac composable_maps_to >>
`(ab.dom = a) ∧ (ba.cod = a)` by fsrw_tac [][composable_in_def] >>
imp_res_tac is_functor_is_category >>
fsrw_tac [][] >> strip_tac >>
map_every qexists_tac [`a`,`a`] >>
fsrw_tac [][] >>
qspecl_then [`f`,`f.dom`,`f.cod`,`ab`,`ba`] mp_tac morf_comp >>
qspecl_then [`f`,`f.dom`,`f.cod`,`a`] mp_tac morf_id >>
fsrw_tac [][objf_in_obj]);

val pre_discrete_functor_def = Define`
  pre_discrete_functor s c f = <|
    dom := discrete_cat s;
    cod := c;
    map := λg. id (f g.dom) -:c |>`;

val pre_discrete_functor_components = Q.store_thm(
"pre_discrete_functor_components",
`∀s c f. ((pre_discrete_functor s c f).dom = (discrete_cat s)) ∧
         ((pre_discrete_functor s c f).cod = c) ∧
         (∀g. (pre_discrete_functor s c f)##g = id (f g.dom) -:c)`,
srw_tac [][pre_discrete_functor_def,morf_def]);
val _ = export_rewrites["pre_discrete_functor_components"];

val pre_discrete_functor_objf = Q.store_thm(
"pre_discrete_functor_objf",
`∀s c f x. is_category c ∧ x ∈ s ∧ f x ∈ c.obj ⇒ ((pre_discrete_functor s c f)@@x = f x)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
srw_tac [][] >>
metis_tac [id_inj]);

val discrete_functor_def = Define`
  discrete_functor s c f = mk_functor (pre_discrete_functor s c f)`;

val is_functor_discrete_functor = Q.store_thm(
"is_functor_discrete_functor",
`∀s c f. is_category c ∧ (∀x. x ∈ s ⇒ f x ∈ c.obj) ⇒ is_functor (discrete_functor s c f)`,
srw_tac [][discrete_functor_def] >>
srw_tac [][functor_axioms_def,pre_discrete_functor_objf] >- metis_tac [] >>
srw_tac [][] >>
metis_tac [discrete_cat_obj_mor,discrete_cat_compose_in,discrete_mor_components]);

val discrete_functor_dom_cod = Q.store_thm(
"discrete_functor_dom_cod",
`∀s c f. ((discrete_functor s c f).dom = (discrete_cat s)) ∧
         ((discrete_functor s c f).cod = c)`,
srw_tac [][discrete_functor_def]);
val _ = export_rewrites["discrete_functor_dom_cod"];

val discrete_functor_morf = Q.store_thm(
"discrete_functor_morf",
`∀s c f g. g ∈ (discrete_cat s).mor ⇒ ((discrete_functor s c f)##g = id (f g.dom) -:c)`,
srw_tac [][discrete_functor_def]);

val discrete_functor_objf = Q.store_thm(
"discrete_functor_objf",
`∀s c f x. is_category c ∧ x ∈ s ∧ f x ∈ c.obj ⇒ ((discrete_functor s c f)@@x = f x)`,
srw_tac [][discrete_functor_def,pre_discrete_functor_objf]);

val _ = export_rewrites["discrete_functor_morf","discrete_functor_objf"];

val morf_discrete_mor = Q.store_thm(
"morf_discrete_mor",
`∀f s x. is_functor f ∧ (f.dom = discrete_cat s) ∧ (x ∈ s) ⇒ (f##(discrete_mor x) = id f@@x -:f.cod)`,
srw_tac [][] >>
match_mp_tac EQ_TRANS >>
qexists_tac `f##(id x -:(discrete_cat s))` >>
conj_tac >- srw_tac [][] >>
match_mp_tac morf_id >>
srw_tac [][]);
val _ = export_rewrites["morf_discrete_mor"];

val is_comma_cat_obj_def = Define`
  is_comma_cat_obj (t:('a,'b,'c,'d) functor) (s:('e,'f,'c,'d) functor) x =
    x.dom ∈ t.dom.obj ∧ x.cod ∈ s.dom.obj ∧
    x.map :- t@@x.dom → s@@x.cod -:t.cod`;

val is_comma_cat_mor_def = Define`
  is_comma_cat_mor t s m =
    is_comma_cat_obj t s m.dom ∧
    is_comma_cat_obj t s m.cod ∧
    (FST m.map) :- m.dom.dom → m.cod.dom -:t.dom ∧
    (SND m.map) :- m.dom.cod → m.cod.cod -:s.dom ∧
    m.dom.map ≈> s##(SND m.map) -:t.cod ∧
    t##(FST m.map) ≈> m.cod.map -:t.cod ∧
    ((s##(SND m.map)) o m.dom.map -:t.cod =
     m.cod.map o (t##(FST m.map)) -:t.cod)`;

val pre_comma_cat_def = Define`
  pre_comma_cat t s = <|
    obj := { x | is_comma_cat_obj t s x } ;
    mor := { m | is_comma_cat_mor t s m } ;
    id_map :=  λx. (id x.dom -:t.dom, id x.cod -:s.dom) ;
    comp := (λx y. ((FST y.map) o (FST x.map) -:t.dom,
                    (SND y.map) o (SND x.map) -:s.dom)) |>`;

val pre_comma_cat_obj = Q.store_thm(
"pre_comma_cat_obj",
`∀t s. (pre_comma_cat t s).obj = { x | is_comma_cat_obj t s x }`,
srw_tac [][pre_comma_cat_def]);

val pre_comma_cat_mor = Q.store_thm(
"pre_comma_cat_mor",
`∀t s. (pre_comma_cat t s).mor = { m | is_comma_cat_mor t s m }`,
srw_tac [][pre_comma_cat_def]);

val pre_comma_cat_id = Q.store_thm(
"pre_comma_cat_id",
`∀t s x. is_comma_cat_obj t s x ⇒
((id x -:(pre_comma_cat t s)).dom = x) ∧
((id x -:(pre_comma_cat t s)).cod = x) ∧
((id x -:(pre_comma_cat t s)).map = (id x.dom -:t.dom, id x.cod -:s.dom))`,
srw_tac [][pre_comma_cat_def,id_in_def,restrict_def]);

val _ = export_rewrites
["pre_comma_cat_obj","pre_comma_cat_mor","pre_comma_cat_id"];

val _ = add_rule {
  term_name = "comma_cat",
  fixity = Closefix,
  pp_elements = [TOK"(",TM,TOK"\226\134\147",TM,TOK")"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT,0))};

val comma_cat_def = Define`
  (t↓s) = mk_cat (pre_comma_cat t s)`;

val is_category_comma_cat = Q.store_thm(
"is_category_comma_cat",
`∀t s. is_functor t ∧ is_functor s ∧ (s.cod = t.cod) ⇒ is_category (t↓s)`,
srw_tac [][comma_cat_def] >>
imp_res_tac is_functor_is_category >>
fsrw_tac [][category_axioms_def] >>
conj_asm1_tac >- fsrw_tac [][is_comma_cat_mor_def] >>
conj_asm1_tac >- fsrw_tac [][is_comma_cat_mor_def] >>
conj_asm1_tac >- (
  srw_tac [][] >>
  imp_res_tac is_comma_cat_obj_def >>
  srw_tac [][maps_to_in_def] >>
  srw_tac [][is_comma_cat_mor_def]
  >- (
    match_mp_tac maps_to_composable >>
    imp_res_tac morf_id >>
    fsrw_tac [][] >>
    metis_tac [id_maps_to,objf_in_obj] )
  >- (
    match_mp_tac maps_to_composable >>
    imp_res_tac morf_id >>
    fsrw_tac [][] >>
    metis_tac [id_maps_to,objf_in_obj] ) >>
  `s :- s.dom → s.cod` by srw_tac [][] >>
  `t :- t.dom → t.cod` by srw_tac [][] >>
  imp_res_tac morf_id >> srw_tac [][] >>
  fsrw_tac [][maps_to_in_def]) >>
conj_asm1_tac >- (
  srw_tac [][] >>
  `id f.dom -:pre_comma_cat t s ≈> f -:pre_comma_cat t s` by (
    srw_tac [][composable_in_def] >> fsrw_tac [][maps_to_in_def] ) >>
  srw_tac [][morphism_component_equality,compose_in_thm] >>
  srw_tac [][Once pre_comma_cat_def] >>
  imp_res_tac is_comma_cat_mor_def >>
  fsrw_tac [][maps_to_in_def] ) >>
conj_asm1_tac >- (
  srw_tac [][] >>
  `f ≈> id f.cod -:pre_comma_cat t s -:pre_comma_cat t s` by (
    srw_tac [][composable_in_def] >> fsrw_tac [][maps_to_in_def] ) >>
  srw_tac [][morphism_component_equality,compose_in_thm] >>
  srw_tac [][Once pre_comma_cat_def] >>
  imp_res_tac is_comma_cat_mor_def >>
  fsrw_tac [][maps_to_in_def] ) >>
conj_asm2_tac >- (
  srw_tac [][] >>
  `(compose (pre_comma_cat t s).comp f g ≈> h -:pre_comma_cat t s)` by (
    match_mp_tac maps_to_composable >>
    first_x_assum (qspecl_then [`f`,`g`] mp_tac) >>
    srw_tac [][compose_in_thm] >>
    map_every qexists_tac [`f.dom`,`h.dom`,`h.cod`] >>
    imp_res_tac composable_in_def >>
    reverse conj_tac >- srw_tac [][] >>
    first_x_assum match_mp_tac >>
    qexists_tac `f.cod` >>
    fsrw_tac [][] >>
    qpat_assum `g.cod = X` (mp_tac o SYM) >> srw_tac [][] ) >>
  `(f ≈> compose (pre_comma_cat t s).comp g h -:pre_comma_cat t s)` by (
    match_mp_tac maps_to_composable >>
    first_x_assum (qspecl_then [`g`,`h`] mp_tac) >>
    srw_tac [][compose_in_thm] >>
    map_every qexists_tac [`f.dom`,`f.cod`,`h.cod`] >>
    imp_res_tac composable_in_def >>
    conj_tac >- srw_tac [][] >>
    first_x_assum match_mp_tac >>
    qexists_tac `h.dom` >>
    fsrw_tac [][] >>
    qpat_assum `g.cod = X` (mp_tac o SYM) >> srw_tac [][] ) >>
  srw_tac [][compose_in_thm] >>
  imp_res_tac composable_in_def >>
  srw_tac [][pre_comma_cat_def] >>
  match_mp_tac comp_assoc >>
  fsrw_tac [][pre_comma_cat_mor] >>
  srw_tac [][] >> match_mp_tac maps_to_composable >>
  metis_tac [is_comma_cat_mor_def] ) >>
srw_tac [][] >>
`f ≈> g -:pre_comma_cat t s` by imp_res_tac maps_to_composable >>
srw_tac [][compose_in_thm] >>
reverse (srw_tac [][maps_to_in_def])
>- fsrw_tac [][pre_comma_cat_def,compose_in_def,maps_to_in_def]
>- fsrw_tac [][pre_comma_cat_def,compose_in_def,maps_to_in_def] >>
imp_res_tac maps_to_composable >>
imp_res_tac composable_in_def >>
fsrw_tac [][compose_in_def] >>
srw_tac [][pre_comma_cat_def] >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >> srw_tac [][] >>
fsrw_tac [][is_comma_cat_mor_def] >>
conj_tac >- metis_tac [maps_to_comp] >>
conj_tac >- metis_tac [maps_to_comp] >>
imp_res_tac is_comma_cat_obj_def >>
`(SND f.map) ≈> (SND g.map) -:s.dom` by (
  fsrw_tac [][maps_to_in_def,composable_in_def]) >>
`(FST f.map) ≈> (FST g.map) -:t.dom` by (
  fsrw_tac [][maps_to_in_def,composable_in_def]) >>
Q.ISPECL_THEN [`s`,`s.dom`,`s.cod`,`SND f.map`,`SND g.map`] mp_tac morf_comp >>
fsrw_tac [][] >>
Q.ISPECL_THEN [`t`,`t.dom`,`t.cod`,`FST f.map`,`FST g.map`] mp_tac morf_comp >>
fsrw_tac [][] >>
metis_tac [morf_comp,composable_comp,composable_morf,comp_assoc]);

val comma_cat_obj = Q.store_thm(
"comma_cat_obj",
`∀t s. (t↓s).obj = { x | is_comma_cat_obj t s x }`,
srw_tac [][comma_cat_def]);

val comma_cat_mor = Q.store_thm(
"comma_cat_mor",
`∀t s. (t↓s).mor = { m | is_comma_cat_mor t s m }`,
srw_tac [][comma_cat_def]);

val comma_cat_id = Q.store_thm(
"comma_cat_id",
`∀t s x. is_comma_cat_obj t s x ⇒
((id x -:(t↓s)).dom = x) ∧
((id x -:(t↓s)).cod = x) ∧
((id x -:(t↓s)).map = (id x.dom -:t.dom, id x.cod -:s.dom))`,
srw_tac [][comma_cat_def]);

val _ = export_rewrites ["comma_cat_obj","comma_cat_mor","comma_cat_id"];

val _ = add_rule {
  term_name = "slice_cat",
  fixity = Closefix,
  pp_elements = [TOK"(",TM,TOK"/",TM,TOK")"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT,0))};

val slice_cat_def = Define` (* should define this nicer, then show isomorphic to the below *)
  (c/a) = (id_functor c ↓ K_functor unit_cat c a)`;

val is_category_slice_cat = Q.store_thm(
"is_category_slice_cat",
`∀c a. is_category c ∧ a ∈ c.obj ⇒ is_category (c/a)`,
srw_tac [][slice_cat_def] >>
match_mp_tac is_category_comma_cat >>
srw_tac [][]);

val slice_cat_obj = Q.store_thm(
"slice_cat_obj",
`∀c a x. is_category c ∧ a ∈ c.obj ⇒
  (x ∈ (c/a).obj ⇔ x.map :- x.dom → a -:c)`,
srw_tac [][slice_cat_def] >>
srw_tac [][is_comma_cat_obj_def] >>
EQ_TAC >- (
  strip_tac >>
  pop_assum mp_tac >>
  srw_tac [][] ) >>
strip_tac >>
imp_res_tac maps_to_obj >>
srw_tac [][]);

val slice_cat_mor = Q.store_thm(
"slice_cat_mor",
`∀c a f. is_category c ∧ a ∈ c.obj ⇒
  (f ∈ (c/a).mor ⇔
   (FST f.map) :- f.dom.dom → f.cod.dom -:c ∧
   f.dom.map :- f.dom.dom → a -:c ∧
   f.cod.map :- f.cod.dom → a -:c ∧
   (f.dom.map = f.cod.map o (FST f.map) -:c))`,
srw_tac [][slice_cat_def] >>
srw_tac [][is_comma_cat_mor_def] >>
srw_tac [][is_comma_cat_obj_def] >>
EQ_TAC >- (
  srw_tac [][] >>
  pop_assum mp_tac >>
  fsrw_tac [][maps_to_in_def]) >>
strip_tac >>
imp_res_tac maps_to_obj >>
fsrw_tac [][] >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >>
conj_asm2_tac >- (
  match_mp_tac (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL (SPEC_ALL composable_comp)))) >>
  srw_tac [][composable_in_def,id_mor,id_dom_cod] ) >>
srw_tac [][composable_in_def]);

val pre_cat_cat_def = Define`
  pre_cat_cat = <|
    obj := {c | is_category c};
    mor := {f | is_functor f};
    id_map := λf. (id_functor f).map ;
    comp := λf g. (g ◎ f).map |>`;

val pre_cat_cat_obj_mor = Q.store_thm(
"pre_cat_cat_obj_mor",
`(pre_cat_cat.obj = {c | is_category c}) ∧
 (pre_cat_cat.mor = {f | is_functor f})`,
srw_tac [][pre_cat_cat_def]);
val _ = export_rewrites["pre_cat_cat_obj_mor"];

val pre_cat_cat_id = Q.store_thm(
"pre_cat_cat_id",
`∀c. is_category c ⇒ (id c -:pre_cat_cat = id_functor c)`,
srw_tac [][morphism_component_equality] >>
srw_tac [][id_in_def,restrict_def] >>
srw_tac [][pre_cat_cat_def]);

val pre_cat_cat_composable_in = Q.store_thm(
"pre_cat_cat_composable_in",
`∀f g. f ≈> g -:pre_cat_cat = is_functor f ∧ is_functor g ∧ f ≈> g`,
srw_tac [][composable_in_def]);

val pre_cat_cat_compose_in = Q.store_thm(
"pre_cat_cat_compose_in",
`∀f g. f ≈> g -:pre_cat_cat ⇒ ((g o f -:pre_cat_cat) = g ◎ f)`,
srw_tac [][morphism_component_equality] >>
srw_tac [][compose_in_def,restrict_def] >>
imp_res_tac composable_in_def >>
srw_tac [][compose_def] >>
srw_tac [][pre_cat_cat_def]);

val _ = export_rewrites["pre_cat_cat_id","pre_cat_cat_composable_in","pre_cat_cat_compose_in"];

val cat_cat_def = Define`
  cat_cat = mk_cat pre_cat_cat`;

val is_category_cat_cat = Q.store_thm(
"is_category_cat_cat",
`is_category cat_cat`,
srw_tac [][cat_cat_def] >>
fsrw_tac [][category_axioms_def,is_functor_is_category] >>
conj_asm1_tac >- ( srw_tac [][maps_to_in_def] ) >>
conj_tac >- srw_tac [][functor_comp_id_functor] >>
conj_tac >- srw_tac [][functor_comp_id_functor] >>
conj_tac >- srw_tac [][functor_comp_assoc] >>
srw_tac [][maps_to_in_def]);

val cat_cat_obj_mor = Q.store_thm(
"cat_cat_obj_mor",
`(cat_cat.obj = {c | is_category c}) ∧
 (cat_cat.mor = {f | is_functor f})`,
srw_tac [][cat_cat_def]);
val _ = export_rewrites["cat_cat_obj_mor"];

val _ = export_theory ();
