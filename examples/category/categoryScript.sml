open HolKernel Parse boolLib bossLib lcsymtacs pairTheory pred_setTheory SatisfySimps boolSimps;

val _ = new_theory "category";

Definition extensional_def:
  extensional f x <=> ∀e. e ∉ x ⇒ (f e = ARB)
End

val restrict_def = Define`
  restrict f x = λe. if e ∈ x then f e else ARB`;

val extensional_restrict = Q.store_thm(
"extensional_restrict",
`∀f x. extensional (restrict f x) x`,
srw_tac [][extensional_def,restrict_def])
val _ = export_rewrites["extensional_restrict"];

val restrict_idem = Q.store_thm(
"restrict_idem",
`∀f x. restrict (restrict f x) x = restrict f x`,
srw_tac [][restrict_def])
val _ = export_rewrites["restrict_idem"];

val extensional_restrict_iff = Q.store_thm(
"extensional_restrict_iff",
`∀f x. extensional f x  = (f = restrict f x)`,
srw_tac [][EQ_IMP_THM] >- (
  fsrw_tac [][restrict_def,extensional_def,FUN_EQ_THM] >>
  srw_tac [][] ) >>
metis_tac [extensional_restrict]);

val _ = Hol_datatype`morphism = <|
  dom : α; cod : β; map : γ |>`;

val morphism_component_equality = DB.theorem"morphism_component_equality";

val HS = HardSpace 1;

val _ = add_rule {
  term_name = "composable",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK "\226\137\136>", HS],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Definition composable_def: f ≈> g <=> (f.cod = g.dom)
End

val compose_def = Define`
  compose (c:(α,β,γ) morphism -> (β,δ,ε) morphism -> ζ) =
  CURRY (restrict
    (λ(f,g). <| dom := f.dom; cod := g.cod; map := c f g |>)
    {(f,g) | f ≈> g})`;

val _ = add_rule {
  term_name = "maps_to",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK ":-", HS, TM, HS, TOK "\226\134\146", HS],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Definition maps_to_def:   f :- x → y <=> (f.dom = x) ∧ (f.cod = y)
End

val _ = type_abbrev("mor",``:(α,α,β) morphism``);

val _ = Hol_datatype `category =
  <| obj : α set ;
     mor : (α,β) mor set ;
     id_map : α -> β;
     comp : (α,β) mor -> (α,β) mor -> β |>`;

val category_component_equality = DB.theorem "category_component_equality";

val _ = add_rule {
  term_name = "maps_to_in_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK ":-", HS, TM, HS, TOK "\226\134\146", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Definition maps_to_in_def:   maps_to_in c f x y <=> f ∈ c.mor ∧ f :- x → y
End

val _ = overload_on("maps_to_in_syntax",``λf x y c. maps_to_in c f x y``);

val maps_to_in_dom_cod = Q.store_thm(
"maps_to_in_dom_cod",
`∀f c. f ∈ c.mor ⇒ maps_to_in c f f.dom f.cod`,
srw_tac [][maps_to_in_def,maps_to_def]);
val _ = export_rewrites["maps_to_in_dom_cod"];

val _ = add_rule {
  term_name = "id_in_syntax",
  fixity = Prefix 625,
  pp_elements = [TOK"id",HS,TM,HS,TOK"-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val id_in_def = Define`
  id_in c = restrict (λx. <|dom := x; cod := x; map := c.id_map x|>) c.obj`;

val _ = overload_on("id_in_syntax",``λx c. id_in c x``);

val _ = add_rule {
  term_name = "composable_in_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK "\226\137\136>", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val _ = add_rule{
  term_name="hom_syntax",
  fixity=Suffix 620,
  pp_elements=[TOK"|",TM,TOK"\226\134\146",TM,TOK"|"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val hom_def = Define`
  hom c x y = {f | f :- x → y -:c}`;

val _ = overload_on("hom_syntax",``hom``);

Definition composable_in_def:
  composable_in c f g <=> f ∈ c.mor ∧ g ∈ c.mor ∧ f ≈> g
End

val _ = overload_on("composable_in_syntax",``λf g c. composable_in c f g``);

val _ = add_rule {
  term_name = "compose_in_syntax",
  fixity = Infixr 800,
  pp_elements = [HS, TOK "o", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundSameName, (PP.INCONSISTENT, 0))
};

val compose_in_def = Define`
  compose_in c = CURRY (restrict (UNCURRY (compose c.comp)) {(f,g) | f ≈> g -: c})`;

val _ = overload_on("compose_in_syntax",``λg f c. compose_in c f g``);

val compose_in_thm = Q.store_thm(
"compose_in_thm",
`∀c f g. f ≈> g -:c ⇒ (g o f -: c = compose c.comp f g)`,
srw_tac [][compose_in_def,restrict_def]);

Definition extensional_category_def:
  extensional_category c <=>
    extensional c.id_map c.obj ∧
    extensional (UNCURRY c.comp) {(f,g) | f ≈> g -: c}
End

Definition category_axioms_def:
  category_axioms c <=>
    (∀f. f ∈ c.mor ⇒ f.dom ∈ c.obj) ∧
    (∀f. f ∈ c.mor ⇒ f.cod ∈ c.obj) ∧
    (∀a. a ∈ c.obj ⇒ (id a -:c) :- a → a -: c) ∧
    (∀f. f ∈ c.mor ⇒ (f o (id f.dom -:c) -: c = f)) ∧
    (∀f. f ∈ c.mor ⇒ ((id f.cod -:c) o f -: c = f)) ∧
    (∀f g h. f ≈> g -: c ∧ g ≈> h -: c ⇒
               (((h o g -: c) o f -: c) = h o g o f -: c -: c)) ∧
    (∀f g x y z. f :- x → y -: c ∧ g :- y → z -: c ⇒
                   g o f -: c :- x → z -: c)
End

Definition is_category_def:
  is_category c ⇔ extensional_category c ∧ category_axioms c
End

val compose_thm = Q.store_thm(
"compose_thm",
`∀c f g. (f ≈> g) ⇒ (compose c f g = <|dom := f.dom; cod := g.cod; map := c f g|>)`,
srw_tac [][compose_def,restrict_def]);

val _ = export_rewrites["composable_def","maps_to_def","compose_thm"];

val mk_cat_def = Define`
  mk_cat (c:(α,β) category) = <|
    obj := c.obj;
    mor := c.mor;
    id_map := restrict c.id_map c.obj;
    comp := CURRY (restrict (UNCURRY c.comp) {(f,g) | f ≈> g -: c}) |>`;

Theorem mk_cat_maps_to_in:
  ∀c f x y. f :- x → y -: (mk_cat c) <=> f :- x → y -: c
Proof srw_tac [][maps_to_in_def,mk_cat_def,restrict_def]
QED

Theorem mk_cat_composable_in:
  ∀c f g. (f ≈> g -: (mk_cat c)) <=> f ≈> g -: c
Proof srw_tac [][composable_in_def,mk_cat_def,restrict_def]
QED

val mk_cat_id = Q.store_thm(
"mk_cat_id",
`∀c a. a ∈ c.obj ⇒ (id a -:(mk_cat c) = id a -:c)`,
srw_tac [][mk_cat_def,restrict_def,id_in_def]);

val mk_cat_obj = Q.store_thm(
"mk_cat_obj",
`∀c. (mk_cat c).obj = c.obj`,
srw_tac [][mk_cat_def]);

val mk_cat_mor = Q.store_thm(
"mk_cat_mor",
`∀c. (mk_cat c).mor = c.mor`,
srw_tac [][mk_cat_def]);

val mk_cat_comp = Q.store_thm(
"mk_cat_comp",
`∀c f g. f ≈> g -: c ⇒ (g o f -: (mk_cat c) = g o f -: c)`,
srw_tac [][mk_cat_def,restrict_def,compose_in_def,compose_def,composable_in_def]);

val _ = export_rewrites
["mk_cat_maps_to_in","mk_cat_composable_in",
 "mk_cat_id","mk_cat_obj","mk_cat_mor","mk_cat_comp"];

val extensional_mk_cat = Q.store_thm(
"extensional_mk_cat",
`∀c. extensional_category (mk_cat c)`,
srw_tac [][extensional_category_def,mk_cat_def])
val _ = export_rewrites["extensional_mk_cat"];

val maps_to_dom_composable = Q.store_thm(
"maps_to_dom_composable",
`∀c f g x. g ∈ c.mor ∧ (f :- x → g.dom -: c) ⇒ f ≈> g -: c`,
srw_tac [][composable_in_def,maps_to_in_def]);

val maps_to_cod_composable = Q.store_thm(
"maps_to_cod_composable",
`∀c f g y. f ∈ c.mor ∧ (g :- f.cod → y -: c) ⇒ f ≈> g -: c`,
srw_tac [][maps_to_in_def,composable_in_def]);

val is_category_mk_cat = Q.store_thm(
"is_category_mk_cat",
`∀c. is_category (mk_cat c) = category_axioms c`,
srw_tac [][is_category_def] >>
reverse EQ_TAC >>
fsrw_tac [][category_axioms_def] >>
strip_tac >- (
conj_tac >- (
  qx_gen_tac `f` >>
  qspecl_then [`c`,`id f.dom -:c`,`f`,`f.dom`] mp_tac maps_to_dom_composable >>
  srw_tac [][] ) >>
conj_tac >- (
  qx_gen_tac `f` >>
  qspecl_then [`c`,`f`,`id f.cod -:c`,`f.cod`] mp_tac maps_to_cod_composable >>
  srw_tac [][] ) >>
conj_tac  >- (
  srw_tac [][] >>
  `f ≈> (h o g -: c) -: c` by (
    fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
  `(g o f -: c) ≈> h -: c` by (
    fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
  srw_tac [][] ) >>
srw_tac [][] >>
`f ≈> g -: c` by (
  fsrw_tac [][composable_in_def,maps_to_in_def] ) THEN
fsrw_tac [][maps_to_in_def,composable_in_def]) >>
conj_tac >- (
  qx_gen_tac `f` >> strip_tac >>
  `id f.dom -:(mk_cat c) = id f.dom -:c` by srw_tac [][] >>
  `f o (id f.dom -:(mk_cat c)) -:mk_cat c = f o (id f.dom -:c) -:c` by (
    pop_assum mp_tac >>
    simp_tac (srw_ss()) [] >>
    srw_tac [][] >>
    match_mp_tac mk_cat_comp >>
    srw_tac [][composable_in_def] >>
    fsrw_tac [][maps_to_in_def] ) >>
  pop_assum mp_tac >> srw_tac [][] >>
  fsrw_tac [][] >> metis_tac []) >>
conj_tac >- (
  qx_gen_tac `f` >> strip_tac >>
  `id f.cod -:(mk_cat c) = id f.cod -:c` by srw_tac [][] >>
  `(id f.cod -:(mk_cat c)) o f -: mk_cat c = (id f.cod -:c) o f -: c` by (
    pop_assum mp_tac >>
    simp_tac (srw_ss()) [] >>
    srw_tac [][] >>
    match_mp_tac mk_cat_comp >>
    srw_tac [][composable_in_def] >>
    fsrw_tac [][maps_to_in_def] ) >>
  pop_assum mp_tac >> srw_tac [][] >>
  fsrw_tac [][] >> metis_tac []) >>
conj_tac  >- (
  srw_tac [][] >>
  `f ≈> (h o g -: c) -: c` by (
    fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
  `(g o f -: c) ≈> h -: c` by (
    fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
  metis_tac [mk_cat_comp] ) >>
srw_tac [][] >>
`f ≈> g -: c` by (
  fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
fsrw_tac [][maps_to_in_def,composable_in_def]);

val _ = export_rewrites["is_category_mk_cat"];

val comp_assoc = Q.store_thm(
"comp_assoc",
`∀c f g h. is_category c ∧ f ≈> g -: c ∧ g ≈> h -: c
  ⇒ ((h o g -: c) o f -: c = h o (g o f -: c) -: c)`,
srw_tac [][is_category_def,category_axioms_def]);

val composable_maps_to = Q.store_thm(
"composable_maps_to",
`∀c f g a b. is_category c ∧ f ≈> g -: c ∧ (a = f.dom) ∧ (b = g.cod)
  ⇒ g o f -:c :- a → b -:c`,
srw_tac [][composable_in_def] >>
fsrw_tac [][is_category_def,category_axioms_def] >>
first_assum match_mp_tac >> srw_tac [][maps_to_in_def]);

val maps_to_composable = Q.store_thm(
"maps_to_composable",
`∀c f g x y z. f :- x → y -:c ∧ g :- y → z -:c ⇒ f ≈> g -:c`,
srw_tac [][composable_in_def,maps_to_in_def]);

val maps_to_comp = Q.store_thm(
"maps_to_comp",
`∀c f g x y z. is_category c ∧ f :- x → y -:c ∧ g :- y → z -:c ⇒
          g o f -:c :- x → z -:c`,
srw_tac [][is_category_def,category_axioms_def] >> metis_tac []);

val comp_mor_dom_cod = Q.store_thm(
"comp_mor_dom_cod",
`∀c f g. is_category c ∧ f ≈> g -:c ⇒
 f ∈ c.mor ∧ g ∈ c.mor ∧ g o f -:c ∈ c.mor ∧
 ((g o f -:c).dom = f.dom) ∧
 ((g o f -:c).cod = g.cod)`,
rpt strip_tac >>
imp_res_tac composable_maps_to >>
fsrw_tac [][maps_to_in_def,composable_in_def]);

val mor_obj = Q.store_thm(
"mor_obj",
`∀c f. is_category c ∧ f ∈ c.mor ⇒ f.dom ∈ c.obj ∧ f.cod ∈ c.obj`,
srw_tac [][is_category_def,category_axioms_def]);
val _ = export_rewrites["mor_obj"];

val maps_to_obj = Q.store_thm(
"maps_to_obj",
`∀c f x y.  is_category c ∧ f :- x → y -:c
⇒ x ∈ c.obj ∧ y ∈ c.obj`,
srw_tac [][maps_to_in_def] >> srw_tac [][]);

val composable_obj = Q.store_thm(
"composable_obj",
`∀c f g. is_category c ∧ f ≈> g -:c  ⇒
  f.dom ∈ c.obj ∧ g.dom ∈ c.obj ∧ f.cod ∈ c.obj ∧ g.cod ∈ c.obj`,
srw_tac [][composable_in_def]);

val id_maps_to = Q.store_thm(
"id_maps_to",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ (id x -:c) :- x → x -:c`,
metis_tac [is_category_def,category_axioms_def]);

val id_inj = Q.store_thm(
"id_inj",
`∀c x y. is_category c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧ (id x -:c = id y -:c) ⇒ (x = y)`,
srw_tac [][id_maps_to,id_in_def,restrict_def]);

val composable_comp = Q.store_thm(
"composable_comp",
`∀c f g h. is_category c ∧ f ≈> g -:c ∧ g ≈> h -:c ⇒
 f ≈> h o g -:c -:c ∧ g o f -:c ≈> h -:c`,
srw_tac [][] >> fsrw_tac [][composable_in_def,comp_mor_dom_cod]);

val id_mor = Q.store_thm(
"id_mor",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ (id x -:c) ∈ c.mor`,
srw_tac [][] >>
imp_res_tac id_maps_to >>
fsrw_tac [][maps_to_in_def]);

val id_composable_id = Q.store_thm(
"id_composable_id",
`∀c x. is_category c ∧ x ∈ c.obj ⇒
 (id x -:c) ≈> (id x -:c) -:c`,
srw_tac [][] >>
match_mp_tac maps_to_composable >>
metis_tac [id_maps_to]);

val id_dom_cod = Q.store_thm(
"id_dom_cod",
`∀c x. is_category c ∧ x ∈ c.obj ⇒
 ((id x -:c).dom = x) ∧ ((id x -:c).cod = x)`,
srw_tac [][] >>
imp_res_tac id_maps_to >>
fsrw_tac [][maps_to_in_def]);

val id_comp1 = Q.store_thm(
"id_comp1",
`∀c f x. is_category c ∧ f ∈ c.mor ∧ (x = f.dom) ⇒
  (f o (id x -:c) -:c = f)`,
metis_tac [is_category_def,category_axioms_def]);

val id_comp2 = Q.store_thm(
"id_comp2",
`∀c f x. is_category c ∧ f ∈ c.mor ∧ (x = f.cod) ⇒
  ((id x -:c) o f -:c = f)`,
metis_tac [is_category_def,category_axioms_def]);

val left_right_inv_unique = Q.store_thm(
"left_right_inv_unique",
`∀c f g h. is_category c ∧ h ≈> f -:c ∧ f ≈> g -:c ∧
 (g o f -:c = id f.dom -:c) ∧ (f o h -:c = id f.cod -:c) ⇒
 (h = g)`,
simp_tac std_ss [is_category_def,category_axioms_def] >>
rpt strip_tac >>
`h ∈ c.mor ∧ g ∈ c.mor ∧
 (f.dom = h.cod) ∧ (f.cod = g.dom)`
   by fsrw_tac [][composable_in_def] >>
metis_tac [composable_in_def,composable_def]);

val id_comp_id = Q.store_thm(
"id_comp_id",
`∀c x. is_category c ∧ x ∈ c.obj ⇒
 ((id x -:c) o (id x -:c) -:c = (id x -:c))`,
rpt strip_tac >>
imp_res_tac id_dom_cod >>
full_simp_tac std_ss [is_category_def,category_axioms_def,maps_to_in_def] >>
metis_tac []);

val _ = export_rewrites["id_dom_cod","id_comp1","id_comp2","id_comp_id","id_maps_to","id_mor"];

val _ = add_rule {
  term_name = "iso_pair_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK "<\226\137\131>", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Definition iso_pair_def:
  iso_pair c f g <=> f ≈> g -:c ∧ (f o g -:c = id g.dom -:c) ∧
                     (g o f -:c = id f.dom -:c)
End

val _ = overload_on("iso_pair_syntax",``λf g c. iso_pair c f g``);

val iso_def = Define`
  iso c f = ∃g. f <≃> g -:c`;

Theorem iso_pair_sym:
  ∀c f g. is_category c ⇒ (f <≃> g -:c <=> g <≃> f -:c)
Proof
srw_tac [][] >>
imp_res_tac is_category_def >>
imp_res_tac category_axioms_def >>
fsrw_tac [][iso_pair_def,composable_in_def,maps_to_in_def] >>
metis_tac []
QED

val inv_unique = Q.store_thm(
"inv_unique",
`∀c f g h. is_category c ∧ f <≃> g -:c ∧ f <≃> h -:c ⇒ (g = h)`,
rpt strip_tac >>
match_mp_tac left_right_inv_unique >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def,composable_in_def] >>
metis_tac []);

val id_iso_pair = Q.store_thm(
"id_iso_pair",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ (id x -:c) <≃> (id x -:c) -:c`,
srw_tac [][iso_pair_def] >>
match_mp_tac maps_to_composable >>
imp_res_tac is_category_def >>
imp_res_tac category_axioms_def >>
metis_tac []);

val _ = add_rule {
  term_name = "inv_in_syntax",
  fixity = Infix(NONASSOC,2050),
  pp_elements = [TOK "\226\129\187\194\185", TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val inv_in_def = Define`
  inv_in c f = @g. f <≃> g -:c`;

val _ = overload_on("inv_in_syntax",``λf c. inv_in c f``);

val inv_elim_thm = Q.store_thm(
"inv_elim_thm",
`∀P (c:(α,β) category) f g. is_category c ∧ f <≃> g -:c ∧ P g ⇒ P f⁻¹-:c`,
srw_tac [][inv_in_def] >>
SELECT_ELIM_TAC >>
srw_tac [SATISFY_ss][] >>
qsuff_tac `x=g` >- srw_tac [][] >>
match_mp_tac inv_unique >>
fsrw_tac [SATISFY_ss][]);;

fun is_inv_in tm = let
  val (inv_in,[c,f]) = strip_comb tm
  val ("inv_in",ty) = dest_const inv_in
in
  can (match_type ``:(α,β) category -> (α,β) mor -> (α,β) mor``) ty
end handle HOL_ERR _ => false | Bind => false;

fun inv_elim_tac (g as (_, w)) = let
  val t = find_term is_inv_in w
in
  CONV_TAC (UNBETA_CONV t) THEN
  MATCH_MP_TAC inv_elim_thm THEN BETA_TAC
end g;

val inv_eq_iso_pair = Q.store_thm(
"inv_eq_iso_pair",
`∀c f g. is_category c ∧ f <≃> g -:c ⇒ (f⁻¹-:c = g)`,
srw_tac [][] >>
inv_elim_tac >>
srw_tac [][]);

val inv_idem = Q.store_thm(
"inv_idem",
`∀c f. is_category c ∧ iso c f ⇒
 iso c f⁻¹-:c ∧ ((f⁻¹-:c)⁻¹-:c = f)`,
srw_tac [][iso_def] >>
inv_elim_tac >>
srw_tac [][] >>
TRY inv_elim_tac >>
metis_tac [iso_pair_sym]);

val iso_pair_mor = Q.store_thm(
"iso_pair_mor",
`∀c f g. is_category c ∧ f <≃> g -:c ⇒
 f ∈ c.mor ∧ g ∈ c.mor`,
srw_tac [][iso_pair_def,composable_in_def]);

val iso_mor = Q.store_thm(
"iso_mor",
`∀c f. is_category c ∧ iso c f ⇒ f ∈ c.mor`,
srw_tac [][iso_def] >>
imp_res_tac iso_pair_mor >>
fsrw_tac [][]);

val inv_mor_dom_cod = Q.store_thm(
"inv_mor_dom_cod",
`∀c f. is_category c ∧ iso c f ⇒
 f⁻¹-:c ∈ c.mor ∧
 ((f⁻¹-:c).dom = f.cod) ∧
 ((f⁻¹-:c).cod = f.dom)`,
srw_tac [][iso_def] >>
imp_res_tac inv_eq_iso_pair >>
imp_res_tac iso_pair_mor >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def,composable_in_def]);

val inv_maps_to = Q.store_thm(
"inv_maps_to",
`∀c f a b. is_category c ∧ iso c f ∧ (a = f.cod) ∧ (b = f.dom) ⇒ f⁻¹ -:c :- a → b -:c`,
srw_tac [][maps_to_in_def,inv_mor_dom_cod]);

val inv_composable = Q.store_thm(
"inv_composable",
`∀c f. is_category c ∧ iso c f ⇒
  f⁻¹-:c ≈> f -:c ∧
  f ≈> f⁻¹-:c -:c`,
srw_tac [][iso_def] >>
imp_res_tac iso_pair_sym >>
match_mp_tac maps_to_composable >>
imp_res_tac inv_eq_iso_pair >>
fsrw_tac [][iso_pair_def] >>
srw_tac [][maps_to_in_def] >>
fsrw_tac [][composable_in_def]);

val comp_inv_id = Q.store_thm(
"comp_inv_id",
`∀c f. is_category c ∧ iso c f ⇒
 (f o (f⁻¹-:c) -:c = id f.cod -:c) ∧
 ((f⁻¹-:c) o f -:c = id f.dom -:c)`,
srw_tac [][iso_def] >>
inv_elim_tac >>
imp_res_tac iso_pair_sym >>
imp_res_tac iso_pair_def >>
fsrw_tac [][composable_in_def] >>
metis_tac []);

val invs_composable = Q.store_thm(
"invs_composable",
`∀c f g. is_category c ∧ f ≈> g -:c ∧ iso c f ∧ iso c g ⇒
 g⁻¹-:c ≈> f⁻¹-:c -:c`,
srw_tac [][] >>
imp_res_tac inv_mor_dom_cod >>
fsrw_tac [][composable_in_def]);

val iso_pair_comp = Q.store_thm(
"iso_pair_comp",
`∀c f g. is_category c ∧ f ≈> g -:c ∧ iso c f ∧ iso c g ⇒
 g o f -:c <≃> (f⁻¹-:c) o (g⁻¹-:c) -:c -:c`,
srw_tac [][] >>
`g⁻¹-:c ≈> f⁻¹-:c -:c` by imp_res_tac invs_composable >>
`(f⁻¹-:c) o g⁻¹-:c -:c ≈> g o f -:c -:c` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >>
  imp_res_tac composable_maps_to >>
  imp_res_tac inv_mor_dom_cod >>
  imp_res_tac comp_mor_dom_cod >>
  map_every qexists_tac [`g.cod`,`f.dom`,`g.cod`] >>
  srw_tac [][] >> fsrw_tac [][maps_to_in_def] ) >>
imp_res_tac is_category_def >>
`(g o f -:c) o ((f⁻¹ -:c) o (g⁻¹ -:c) -:c) -:c = ((g o f -:c) o (f⁻¹ -:c) -:c) o (g⁻¹ -:c) -:c` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum (match_mp_tac o GSYM) >> srw_tac [][] >>
  match_mp_tac (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL (SPEC_ALL composable_comp)))) >>
  fsrw_tac [][inv_composable] ) >>
`(g o f -:c) o (f⁻¹ -:c) -:c = g o (f o (f⁻¹ -:c) -:c) -:c` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum match_mp_tac >> srw_tac [][] >>
  fsrw_tac [][inv_composable] ) >>
`((f⁻¹ -:c) o (g⁻¹ -:c) -:c) o (g o f -:c) -:c = (f⁻¹ -:c) o ((g⁻¹ -:c) o (g o f -:c) -:c) -:c` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum match_mp_tac >> srw_tac [][] >>
  match_mp_tac (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL (SPEC_ALL composable_comp)))) >>
  fsrw_tac [][inv_composable] ) >>
`(g⁻¹ -:c) o (g o f -:c) -:c = ((g⁻¹ -:c) o g -:c) o f -:c` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum (match_mp_tac o GSYM) >> srw_tac [][] >>
  fsrw_tac [][inv_composable] ) >>
`f.cod = g.dom` by fsrw_tac [][composable_in_def] >>
imp_res_tac comp_inv_id >>
imp_res_tac inv_mor_dom_cod >>
imp_res_tac comp_mor_dom_cod >>
fsrw_tac [][] >>
fsrw_tac [][category_axioms_def] >>
srw_tac [][iso_pair_def] >>
match_mp_tac maps_to_composable >>
metis_tac [maps_to_in_def,maps_to_def]);

val _ = add_rule {
  term_name = "iso_pair_between_objs_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK "<", TM, TOK "\226\137\131", TM, TOK ">", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Definition iso_pair_between_objs_def:
  iso_pair_between_objs c a f g b <=> (f :- a → b) ∧ f <≃> g -:c
End

val _ = overload_on("iso_pair_between_objs_syntax",
  ``λf a b g c. iso_pair_between_objs c a f g b``);

val iso_pair_between_objs_sym = Q.store_thm(
"iso_pair_between_objs_sym",
`∀f a b g c. is_category c ⇒ (f <a≃b> g -:c ⇔ g <b≃a> f -:c)`,
qsuff_tac `∀f a b g c. is_category c ⇒ (f <a≃b> g -:c ⇒ g <b≃a> f -:c)`
>- metis_tac [] >>
srw_tac [][iso_pair_between_objs_def] >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def] >>
imp_res_tac maps_to_in_def >>
imp_res_tac composable_in_def >>
fsrw_tac [][]);

val _ = add_rule {
  term_name = "iso_objs_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK "\226\137\133", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val iso_objs_def = Define`
  iso_objs c a b = ∃f g. f <a≃b> g -:c`;

val _ = overload_on("iso_objs_syntax",``λa b c. iso_objs c a b``);

val iso_objs_thm = Q.store_thm(
"iso_objs_thm",
`∀c a b. is_category c ⇒ (a ≅ b -:c = ∃f. f :- a → b -:c ∧ iso c f)`,
srw_tac [][iso_objs_def,iso_pair_between_objs_def,iso_def] >>
metis_tac [maps_to_in_def,maps_to_def,iso_pair_mor]);

val _ = add_rule {
  term_name = "uiso_objs_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HS, TOK "\226\137\161", HS, TM, HS, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

val uiso_objs_def = Define`
  uiso_objs c a b = ∃!fg. FST fg <a≃b> SND fg -:c`;

val _ = overload_on("uiso_objs_syntax",``λa b c. uiso_objs c a b``);

val uiso_objs_thm = Q.store_thm(
"uiso_objs_thm",
`∀c a b. is_category c ⇒ (a ≡ b -:c = ∃!f. f :- a → b -:c ∧ iso c f)`,
srw_tac [][uiso_objs_def,EXISTS_UNIQUE_THM,EXISTS_PROD,FORALL_PROD,
           iso_pair_between_objs_def,iso_def] >>
metis_tac [inv_unique,maps_to_in_def,maps_to_def,iso_pair_mor]);

val iso_objs_sym = Q.store_thm(
"iso_objs_sym",
`∀c a b. is_category c ⇒ (a ≅ b -:c ⇔ b ≅ a -:c)`,
srw_tac [][iso_objs_def] >>
metis_tac [iso_pair_between_objs_sym]);

val uiso_objs_sym = Q.store_thm(
"uiso_objs_sym",
`∀c a b. is_category c ⇒ (a ≡ b -:c ⇔ b ≡ a -:c)`,
qsuff_tac `∀c a b. is_category c ⇒ (a ≡ b -:c ⇒ b ≡ a -:c)`
>- metis_tac [] >>
srw_tac [][uiso_objs_def] >>
fsrw_tac [][EXISTS_UNIQUE_THM] >>
fsrw_tac [][FORALL_PROD,EXISTS_PROD] >>
Cases_on `fg` >>
metis_tac [iso_pair_between_objs_sym]);

val iso_objs_objs = Q.store_thm(
"iso_objs_objs",
`∀c a b. is_category c ∧ a ≅ b -:c ⇒ a ∈ c.obj ∧ b ∈ c.obj`,
srw_tac [][] >>
imp_res_tac iso_objs_thm >>
imp_res_tac maps_to_obj);

val unit_cat_def = Define`
  unit_cat = mk_cat <| obj := {()}; mor := {ARB:(unit,unit) mor}; id_map := ARB; comp := ARB |>`;

val is_category_unit_cat = Q.store_thm(
"is_category_unit_cat",
`is_category unit_cat`,
srw_tac []
[unit_cat_def,category_axioms_def,
 oneTheory.one,maps_to_in_def,compose_in_def,
 morphism_component_equality]);

val unit_cat_obj = Q.store_thm(
"unit_cat_obj",
`∀x. x ∈ unit_cat.obj`,
srw_tac [][unit_cat_def,oneTheory.one]);

val unit_cat_mor = Q.store_thm(
"unit_cat_mor",
`∀f. f ∈ unit_cat.mor`,
srw_tac [][unit_cat_def,oneTheory.one,morphism_component_equality]);

val unit_cat_mor_dom_cod_map = Q.store_thm(
"unit_cat_mor_dom_cod_map",
`∀f. f ∈ unit_cat.mor ⇒ (f.dom = ARB) ∧ (f.cod = ARB) ∧ (f.map = ARB)`,
srw_tac [][unit_cat_def,oneTheory.one]);

val unit_cat_maps_to = Q.store_thm(
"unit_cat_maps_to",
`∀f x y. f :- x → y -:unit_cat`,
srw_tac [][maps_to_in_def,unit_cat_mor,
   unit_cat_mor_dom_cod_map,oneTheory.one]);

val _ = export_rewrites
["is_category_unit_cat","unit_cat_obj","unit_cat_mor",
 "unit_cat_mor_dom_cod_map","unit_cat_maps_to"];

val discrete_mor_def = Define`
  discrete_mor x = <|dom := x; cod := x; map := ()|>`;

val discrete_mor_components = Q.store_thm(
"discrete_mor_components",
`∀x. ((discrete_mor x).dom = x) ∧
     ((discrete_mor x).cod = x) ∧
     ((discrete_mor x).map = ())`,
srw_tac [][discrete_mor_def]);
val _ = export_rewrites["discrete_mor_components"];

val discrete_cat_def = Define`
  discrete_cat s = mk_cat <| obj := s; mor := IMAGE discrete_mor s;
    id_map := K (); comp := K (K ()) |>`;

val is_category_discrete_cat = Q.store_thm(
"is_category_discrete_cat",
`∀s. is_category (discrete_cat s)`,
srw_tac [][discrete_cat_def] >>
fsrw_tac [][category_axioms_def] >>
conj_tac >- (ntac 2 (srw_tac [][])) >>
conj_tac >- (ntac 2 (srw_tac [][])) >>
conj_tac >- (srw_tac [][id_in_def,restrict_def,maps_to_in_def,morphism_component_equality]) >>
conj_tac >- (srw_tac [][compose_in_def,restrict_def,id_in_def,composable_in_def] >> fsrw_tac [][morphism_component_equality]) >>
conj_tac >- (srw_tac [][id_in_def,restrict_def,compose_in_def,composable_in_def] >> fsrw_tac [][morphism_component_equality]) >>
conj_tac >- (srw_tac [][compose_in_def,restrict_def,composable_in_def] >> fsrw_tac [][morphism_component_equality]) >>
srw_tac [][compose_in_def,restrict_def,maps_to_in_def,composable_in_def] >>
fsrw_tac [][morphism_component_equality]);
val _ = export_rewrites["is_category_discrete_cat"];

Theorem discrete_cat_obj_mor[simp]:
  ∀s. (∀x. x ∈ (discrete_cat s).obj ⇔ x ∈ s) ∧
      (∀f. f ∈ (discrete_cat s).mor ⇔ (∃x. (f = discrete_mor x) ∧ x ∈ s))
Proof  srw_tac [][discrete_cat_def]
QED

val discrete_cat_id = Q.store_thm(
"discrete_cat_id",
`∀s x. x ∈ s ⇒ (id x -:(discrete_cat s) = discrete_mor x)`,
srw_tac [][id_in_def,restrict_def,morphism_component_equality] >>
srw_tac [][discrete_cat_def,mk_cat_def,restrict_def]);
val _ = export_rewrites["discrete_cat_id"];

Theorem discrete_cat_maps_to[simp]:
  ∀f x y s. f :- x → y -:(discrete_cat s) ⇔
            x ∈ s ∧ (y = x) ∧ (f = id x -:(discrete_cat s))
Proof   srw_tac [][maps_to_in_def,EQ_IMP_THM] >> srw_tac [][] >>
        metis_tac []
QED

Theorem discrete_cat_composable[simp]:
  ∀s f g. f ≈> g -:discrete_cat s ⇔ ∃x. x ∈ s ∧ (g = f) ∧ (f = discrete_mor x)
Proof
  srw_tac [][composable_in_def,morphism_component_equality] >> metis_tac []
QED

val discrete_cat_compose_in = Q.store_thm(
"discrete_cat_compose_in",
`∀s f. f ∈ (discrete_cat s).mor ⇒ ((f o f -:discrete_cat s) = f)`,
fsrw_tac [boolSimps.DNF_ss][compose_in_def,restrict_def] >>
srw_tac [][morphism_component_equality] >>
srw_tac [][discrete_cat_def,mk_cat_def,restrict_def,composable_in_def] >>
metis_tac []);
val _ = export_rewrites["discrete_cat_compose_in"];

val unit_cat_discrete = Q.store_thm(
"unit_cat_discrete",
`unit_cat = discrete_cat {()}`,
srw_tac [][unit_cat_def,discrete_cat_def,mk_cat_def,restrict_def] >>
srw_tac [][composable_in_def] >>
srw_tac [][pred_setTheory.EXTENSION] >>
fsrw_tac [][oneTheory.one,morphism_component_equality,FUN_EQ_THM]);

val indiscrete_cat_def = Define`
  indiscrete_cat s = mk_cat <|
    obj := s; mor := { <|dom := x; cod := y; map := ()|> | x ∈ s ∧ y ∈ s };
    id_map := K ();
    comp := K (K ()) |>`;

val is_category_indiscrete_cat = Q.store_thm(
"is_category_indiscrete_cat",
`∀s. is_category (indiscrete_cat s)`,
srw_tac [][indiscrete_cat_def] >>
fsrw_tac [DNF_ss]
[category_axioms_def,maps_to_in_def,compose_in_def,
 id_in_def,composable_in_def,restrict_def]);
val _ = export_rewrites["is_category_indiscrete_cat"];

val indiscrete_cat_obj_mor = Q.store_thm(
"indiscrete_cat_obj_mor",
`∀s. ((indiscrete_cat s).obj = s) ∧
     ((indiscrete_cat s).mor = {f | f.dom ∈ s ∧ f.cod ∈ s })`,
srw_tac [][indiscrete_cat_def,morphism_component_equality,oneTheory.one,EXTENSION]);
val _ = export_rewrites["indiscrete_cat_obj_mor"];

val indiscrete_cat_id = Q.store_thm(
"indiscrete_cat_id",
`∀s x. x ∈ s ⇒ (id x -:(indiscrete_cat s) = <|dom := x; cod := x; map := ()|>)`,
srw_tac [][id_in_def,restrict_def,morphism_component_equality,oneTheory.one]);
val _ = export_rewrites["indiscrete_cat_id"];

Theorem indiscrete_cat_maps_to[simp]:
  ∀f x y s. f :- x → y -:(indiscrete_cat s) ⇔ (f :- x → y) ∧ x ∈ s ∧ y ∈ s
Proof srw_tac [][maps_to_in_def,EQ_IMP_THM] >> srw_tac [][]
QED

Theorem indiscrete_cat_composable[simp]:
  ∀s f g. f ≈> g -:indiscrete_cat s ⇔
          (f ≈> g) ∧ f ∈ (indiscrete_cat s).mor ∧ g ∈ (indiscrete_cat s).mor
Proof
  srw_tac [][composable_in_def,morphism_component_equality,EQ_IMP_THM]
QED

val indiscrete_cat_compose_in = Q.store_thm(
"indiscrete_cat_compose_in",
`∀s f g.  f ≈> g -:indiscrete_cat s ⇒ ((g o f -:indiscrete_cat s) = compose (K (K ())) f g)`,
fsrw_tac [][compose_in_def,restrict_def,oneTheory.one]);
val _ = export_rewrites["indiscrete_cat_compose_in"];

val _ = add_rule {
  term_name = "op_syntax",
  fixity = Suffix 2100,
  pp_elements = [TOK "\194\176"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundSameName, (PP.INCONSISTENT, 0))
};

val op_mor_def = Define`
  op_mor f = <| dom := f.cod; cod := f.dom; map := f.map |>`;

val _ = overload_on("op_syntax",``op_mor``);

val op_mor_dom = Q.store_thm(
"op_mor_dom",
`∀f. (op_mor f).dom = f.cod`,
srw_tac [][op_mor_def]);

val op_mor_cod = Q.store_thm(
"op_mor_cod",
`∀f. (op_mor f).cod = f.dom`,
srw_tac [][op_mor_def]);

val op_mor_map = Q.store_thm(
"op_mor_map",
`∀f. (op_mor f).map = f.map`,
srw_tac [][op_mor_def]);

val op_mor_maps_to = Q.store_thm(
"op_mor_maps_to",
`∀f x y. ((op_mor f) :- x → y) ⇔ f :- y → x`,
srw_tac [][op_mor_dom,op_mor_cod,EQ_IMP_THM]);

val op_mor_idem = Q.store_thm(
"op_mor_idem",
`∀f. op_mor (op_mor f) = f`,
srw_tac [][op_mor_def,morphism_component_equality]);

val op_mor_composable = Q.store_thm(
"op_mor_composable",
`∀f g. ((op_mor f) ≈> (op_mor g)) ⇔ g ≈> f`,
srw_tac [][EQ_IMP_THM,op_mor_cod,op_mor_dom]);

val op_mor_inj = Q.store_thm(
"op_mor_inj",
`∀f g. (op_mor f = op_mor g) ⇔ (f = g)`,
srw_tac [][morphism_component_equality] >>
srw_tac [][op_mor_cod,op_mor_dom,op_mor_map,EQ_IMP_THM]);

val _ = export_rewrites
["op_mor_dom","op_mor_cod","op_mor_map","op_mor_inj",
 "op_mor_maps_to","op_mor_idem","op_mor_composable"];

val BIJ_op_mor = Q.store_thm(
"BIJ_op_mor",
`∀s. BIJ op_mor s (IMAGE op_mor s)`,
srw_tac [][BIJ_DEF,INJ_DEF,SURJ_DEF] >>
metis_tac []);

val op_cat_def = Define`
  op_cat c = <| obj := c.obj; mor := IMAGE op_mor c.mor;
      id_map := c.id_map; comp := λf g. c.comp (op_mor g) (op_mor f) |>`;

val _ = overload_on("op_syntax",``op_cat``);

val op_cat_idem = Q.store_thm(
"op_cat_idem",
`∀c. op_cat (op_cat c) = c`,
srw_tac [][op_cat_def,category_component_equality,
           EXTENSION,FUN_EQ_THM] >>
metis_tac [op_mor_idem]);

val op_cat_maps_to_in = Q.store_thm(
"op_cat_maps_to_in",
`∀f x y c. f :- x → y -:(op_cat c) ⇔ (op_mor f) :- y → x -:c`,
simp_tac std_ss [op_cat_def,maps_to_in_def,op_mor_maps_to] >>
srw_tac [][] >>
metis_tac [op_mor_idem,op_mor_cod,op_mor_dom]);

val op_cat_obj = Q.store_thm(
"op_cat_obj",
`∀c. (op_cat c).obj = c.obj`,
srw_tac [][op_cat_def]);

val op_cat_mor = Q.store_thm(
"op_cat_mor",
`∀c. (op_cat c).mor = IMAGE op_mor c.mor`,
srw_tac [][op_cat_def]);

val op_cat_comp = Q.store_thm(
"op_cat_comp",
`∀c f g. (op_cat c).comp f g = c.comp (op_mor g) (op_mor f)`,
srw_tac [][op_cat_def]);

val op_cat_composable = Q.store_thm(
"op_cat_composable",
`∀c f g. f ≈> g -:(op_cat c) ⇔ (op_mor g) ≈> (op_mor f) -:c`,
srw_tac [][composable_in_def,op_cat_mor] >> metis_tac [op_mor_idem]);

val op_cat_id = Q.store_thm(
"op_cat_id",
`∀c x. id x -: (op_cat c) = id x -:c`,
srw_tac [][op_cat_def,id_in_def]);

val op_mor_id = Q.store_thm(
"op_mor_id",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ ((op_mor (id x -:c)) = id x -:c)`,
srw_tac [][morphism_component_equality,id_in_def]);

val _ = export_rewrites
["op_cat_idem","op_cat_maps_to_in","op_cat_obj","op_cat_mor",
 "op_cat_comp","op_cat_composable","op_cat_id","op_mor_id"];

val op_cat_compose_in = Q.store_thm(
"op_cat_compose_in",
`∀f g c. f° ≈> g° -:c ⇒ ((f o g -:op_cat c) = op_mor ((op_mor g) o (op_mor f) -:c))`,
srw_tac [][compose_def,compose_in_def,composable_in_def,restrict_def] >>
srw_tac [][morphism_component_equality] >> fsrw_tac [][]);

val op_cat_axioms = Q.store_thm(
"op_cat_axioms",
`∀c. category_axioms c ⇒ category_axioms (op_cat c)`,
fsrw_tac [][category_axioms_def] >>
gen_tac >> strip_tac >>
conj_tac >- ( srw_tac [][op_cat_def] >> srw_tac [][] ) >>
conj_tac >- ( srw_tac [][op_cat_def] >> srw_tac [][] ) >>
conj_tac >- (
  srw_tac [][] >>
  qsuff_tac `(id a -:c)° = (id a -:c)` >- srw_tac [][] >>
  fsrw_tac [][morphism_component_equality,maps_to_in_def] ) >>
conj_tac >- (
  srw_tac [][] >> srw_tac [][] >>
  match_mp_tac (fst (EQ_IMP_RULE (SPEC_ALL op_mor_inj))) >>
  `id x.cod -:c = (op_mor (id x.cod -:c))` by (
     srw_tac [][morphism_component_equality] >>
     fsrw_tac [][maps_to_in_def] ) >>
  `x° ° ≈> (id x.cod -:c)° -:c` by (
    srw_tac [][composable_in_def] >>
    metis_tac [maps_to_in_def,maps_to_def] ) >>
  metis_tac [op_cat_compose_in,op_mor_idem] ) >>
conj_tac >- (
  srw_tac [][] >> srw_tac [][] >>
  match_mp_tac (fst (EQ_IMP_RULE (SPEC_ALL op_mor_inj))) >>
  `id x.dom -:c = (op_mor (id x.dom -:c))` by (
     srw_tac [][morphism_component_equality] >>
     fsrw_tac [][maps_to_in_def] ) >>
  `(id x.dom -:c)° ≈> x° ° -:c` by (
    srw_tac [][composable_in_def] >>
    metis_tac [maps_to_in_def,maps_to_def] ) >>
  metis_tac [op_cat_compose_in,op_mor_idem] ) >>
conj_tac >- (
  srw_tac [][op_cat_compose_in] >>
  `(h° ≈> (f° o g° -:c)° ° -:c)` by (
    match_mp_tac maps_to_composable >>
    map_every qexists_tac [`h.cod`,`h.dom`,`f.dom`] >>
    fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
  `((g° o h° -:c)° ° ≈> f° -:c)` by (
    match_mp_tac maps_to_composable >>
    map_every qexists_tac [`h.cod`,`f.cod`,`f.dom`] >>
    fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
  srw_tac [][op_cat_compose_in]) >>
srw_tac [][] >>
`g° ≈> f° -:c` by (
  fsrw_tac [][composable_in_def] >>
  fsrw_tac [][maps_to_in_def] ) >>
srw_tac [][op_cat_compose_in,op_cat_maps_to_in] >>
fsrw_tac [][maps_to_in_def]);

val op_cat_extensional = Q.store_thm(
"op_cat_extensional",
`∀c. extensional_category c ⇒ extensional_category (op_cat c)`,
srw_tac [][extensional_category_def,op_cat_def] >>
fsrw_tac [][extensional_def,IN_DEF,UNCURRY,FORALL_PROD]);

val is_category_op_cat = Q.store_thm(
"is_category_op_cat",
`∀c. is_category (op_cat c) ⇔ is_category c`,
metis_tac [is_category_def,op_cat_axioms,op_cat_extensional,op_cat_idem])
val _ = export_rewrites["is_category_op_cat"];

val op_cat_iso_pair = Q.store_thm(
"op_cat_iso_pair",
`∀c f g. is_category c ⇒ (f <≃> g -:(op_cat c) ⇔ (op_mor f) <≃> (op_mor g) -:c)`,
qsuff_tac `∀c f g. is_category c ⇒ (f <≃> g -:c ⇒ (op_mor f) <≃> (op_mor g) -:(op_cat c))` >-
metis_tac [op_cat_idem,is_category_op_cat,op_mor_idem] >>
srw_tac [][] >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def,op_cat_composable,op_cat_compose_in] >>
fsrw_tac [][compose_in_def,morphism_component_equality,composable_in_def]);

val op_cat_iso_pair_between_objs = Q.store_thm(
"op_cat_iso_pair_between_objs",
`∀c x f g y. is_category c ⇒ (f <x≃y> g -:c° ⇔ g° <x≃y> f° -:c)`,
qsuff_tac `∀c x f g y. is_category c ⇒ (f <x≃y> g -:c° ⇒ g° <x≃y> f° -:c)` >-
metis_tac [op_cat_idem,is_category_op_cat,op_mor_idem] >>
srw_tac [][iso_pair_between_objs_def,op_cat_iso_pair,iso_pair_sym] >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def,maps_to_in_def,composable_in_def]);

val op_cat_iso = Q.store_thm(
"op_cat_iso",
`∀c f. is_category c ⇒ (iso c° f ⇔ iso c f°)`,
metis_tac [iso_def,op_cat_iso_pair,op_mor_idem]);

val op_cat_iso_objs = Q.store_thm(
"op_cat_iso_objs",
`∀c x y. is_category c ⇒ (x ≅ y -:c° ⇔ x ≅ y -:c)`,
qsuff_tac `∀c x y. is_category c ⇒ (x ≅ y -:c° ⇒ x ≅ y -:c)` >-
metis_tac [op_cat_idem,is_category_op_cat] >>
srw_tac [][iso_objs_def] >>
imp_res_tac iso_pair_between_objs_sym >>
fsrw_tac [][iso_pair_between_objs_def] >>
metis_tac [op_cat_maps_to_in,op_mor_dom,op_mor_cod,op_cat_iso_pair]);

val op_cat_uiso_objs = Q.store_thm(
"op_cat_uiso_objs",
`∀c x y. is_category c ⇒ (x ≡ y -:c° ⇔ x ≡ y -:c)`,
qsuff_tac `∀c x y. is_category c ⇒ (x ≡ y -:c° ⇒ x ≡ y -:c)` >-
metis_tac [op_cat_idem,is_category_op_cat] >>
srw_tac [][uiso_objs_def,op_cat_iso_pair_between_objs] >>
fsrw_tac [][EXISTS_UNIQUE_THM,EXISTS_PROD,FORALL_PROD] >>
metis_tac [iso_pair_between_objs_sym,op_mor_idem]);

val category_eq_thm = Q.store_thm(
"category_eq_thm",
`∀c1 c2. is_category c1 ∧ is_category c2 ∧
         (c1.obj = c2.obj) ∧ (c1.mor = c2.mor) ∧
         (∀x. x ∈ c1.obj ⇒ (id x -:c1 = id x -:c2)) ∧
         (∀f g. f ≈> g -:c1 ⇒ (g o f -:c1 = g o f-:c2))
⇒ (c1 = c2)`,
srw_tac [][category_component_equality] >>
srw_tac [][FUN_EQ_THM] >- (
  qmatch_rename_tac `c1.id_map x = c2.id_map x` >>
  Cases_on `x ∈ c1.obj` >- (
    first_x_assum (qspec_then `x` mp_tac) >>
    srw_tac [][id_in_def,restrict_def] >>
    metis_tac [] ) >>
  fsrw_tac [][is_category_def,extensional_category_def,extensional_def] >>
  metis_tac [] ) >>
qmatch_rename_tac `c1.comp f g = c2.comp f g` >>
Cases_on `f ≈> g-:c1` >- (
  first_x_assum (qspecl_then [`f`,`g`] mp_tac) >>
  srw_tac [][compose_in_def,restrict_def,compose_def,composable_in_def] >>
  fsrw_tac [][composable_in_def] >>
  metis_tac [] ) >>
fsrw_tac [][is_category_def,extensional_category_def,extensional_def,FORALL_PROD] >>
fsrw_tac [][composable_in_def] >> metis_tac []);

val op_discrete_cat = Q.store_thm(
"op_discrete_cat",
`∀s. (discrete_cat s)° = discrete_cat s`,
srw_tac [][] >> match_mp_tac category_eq_thm >>
srw_tac [][] >- (
  srw_tac [DNF_ss][morphism_component_equality,EXTENSION] >>
  metis_tac [] ) >>
fsrw_tac [][compose_in_def,restrict_def,compose_def,op_cat_comp] >>
srw_tac [][] >> fsrw_tac [][morphism_component_equality] >>
srw_tac [][] >> metis_tac []);
val _ = export_rewrites["op_discrete_cat"];

val op_indiscrete_cat = Q.store_thm(
"op_indiscrete_cat",
`∀s. (indiscrete_cat s)° = indiscrete_cat s`,
srw_tac [][] >> match_mp_tac category_eq_thm >>
srw_tac [][] >- (
  srw_tac [DNF_ss][morphism_component_equality,EXTENSION] >>
  srw_tac [][EQ_IMP_THM] >>
  fsrw_tac [][oneTheory.one] >>
  qexists_tac `op_mor x` >>
  srw_tac [][] ) >>
srw_tac [][compose_in_def,restrict_def,oneTheory.one]);
val _ = export_rewrites["op_indiscrete_cat"];

val product_mor_def = Define`
  product_mor (f,g) =
  <| dom := (f.dom,g.dom); cod := (f.cod,g.cod); map := (f.map,g.map) |>`;

val product_mor_components = Q.store_thm(
"product_mor_components",
`∀fg. ((product_mor fg).dom = ((FST fg).dom, (SND fg).dom)) ∧
      ((product_mor fg).cod = ((FST fg).cod, (SND fg).cod)) ∧
      ((product_mor fg).map = ((FST fg).map, (SND fg).map))`,
Cases >> srw_tac [][product_mor_def]);
val _ = export_rewrites["product_mor_components"];

val unproduct_mor_def = Define`
  unproduct_mor fg =
    (<|dom:= FST fg.dom; cod:= FST fg.cod; map := FST fg.map|>,
     <|dom:= SND fg.dom; cod:= SND fg.cod; map := SND fg.map|>)`;

val product_mor_unproduct_mor = Q.store_thm(
"product_mor_unproduct_mor",
`(∀x. product_mor (unproduct_mor x) = x) ∧
 (∀x. unproduct_mor (product_mor x) = x)`,
fsrw_tac [][FORALL_PROD,product_mor_def,unproduct_mor_def,
            morphism_component_equality]);
val _ = export_rewrites["product_mor_unproduct_mor"];

Theorem product_mor_eq[simp]:
  ∀f g f' g'. (product_mor (f,g) = product_mor (f',g')) ⇔
              (f = f') ∧ (g = g')
Proof
  srw_tac [][EQ_IMP_THM] >>
  fsrw_tac [][product_mor_def,morphism_component_equality]
QED

val pre_product_cat_def = Define`
  pre_product_cat c1 c2 = <|
    obj := c1.obj × c2.obj;
    mor := IMAGE product_mor (c1.mor × c2.mor);
    id_map := λab. (c1.id_map (FST ab), c2.id_map (SND ab));
    comp := λef gh.
      (c1.comp (FST (unproduct_mor ef)) (FST (unproduct_mor gh)),
       c2.comp (SND (unproduct_mor ef)) (SND (unproduct_mor gh)))|>`;

val pre_product_cat_obj_mor = Q.store_thm(
"pre_product_cat_obj_mor",
`∀c1 c2. ((pre_product_cat c1 c2).obj = c1.obj × c2.obj) ∧
         ((pre_product_cat c1 c2).mor =
          IMAGE product_mor (c1.mor × c2.mor))`,
srw_tac [][pre_product_cat_def]);
val _ = export_rewrites["pre_product_cat_obj_mor"];

Theorem pre_product_cat_maps_to_in:
  ∀c1 c2 f x y.
    f :- x → y -:(pre_product_cat c1 c2) ⇔
      (FST (unproduct_mor f)) :- (FST x) → (FST y) -: c1 ∧
      (SND (unproduct_mor f)) :- (SND x) → (SND y) -: c2
Proof
srw_tac [DNF_ss][maps_to_in_def,unproduct_mor_def,
                 morphism_component_equality,EXISTS_PROD] >>
Cases_on `f.dom` >> Cases_on `f.cod` >> Cases_on `f.map` >>
Cases_on `x` >> Cases_on `y` >>
srw_tac [DNF_ss][EQ_IMP_THM] >|[
  qmatch_abbrev_tac `x ∈ c1.mor` >>
  qsuff_tac `x=p_1` >- srw_tac [][] >>
  srw_tac [][Abbr`x`,morphism_component_equality],
  qmatch_abbrev_tac `x ∈ c2.mor` >>
  qsuff_tac `x=p_2` >- srw_tac [][] >>
  srw_tac [][Abbr`x`,morphism_component_equality],
  qmatch_assum_abbrev_tac `p1 ∈ c1.mor` >>
  qmatch_assum_abbrev_tac `p2 ∈ c2.mor` >>
  map_every qexists_tac [`p1`,`p2`] >>
  srw_tac [][Abbr`p1`,Abbr`p2`]]
QED

val pre_product_cat_id = Q.store_thm(
"pre_product_cat_id",
`∀c1 c2 x y. x ∈ c1.obj ∧ y ∈ c2.obj ⇒
  (id (x,y) -:(pre_product_cat c1 c2) =
   product_mor (id x -:c1, id y -:c2))`,
srw_tac [][id_in_def,restrict_def,product_mor_def,pre_product_cat_def]);

Theorem pre_product_cat_composable_in[simp]:
  ∀c1 c2 f g. f ≈> g -:(pre_product_cat c1 c2) ⇔
                (FST (unproduct_mor f) ≈> FST (unproduct_mor g) -:c1) ∧
                (SND (unproduct_mor f) ≈> SND (unproduct_mor g) -:c2)
Proof
  srw_tac [DNF_ss][composable_in_def,EXISTS_PROD,EQ_IMP_THM] >>
  fsrw_tac [][] >>
  map_every qexists_tac [`FST (unproduct_mor f)`,`SND (unproduct_mor f)`,
                         `FST (unproduct_mor g)`,`SND (unproduct_mor g)`] >>
  fsrw_tac [][] >>
  Cases_on `f.cod` >> Cases_on `g.dom` >> fsrw_tac [][unproduct_mor_def]
QED

val pre_product_cat_compose_in = Q.store_thm(
"pre_product_cat_compose_in",
`∀c1 c2 f g. (f ≈> g -:(pre_product_cat c1 c2)) ⇒
  (g o f -:(pre_product_cat c1 c2) =
    product_mor (FST (unproduct_mor g) o FST (unproduct_mor f) -:c1,
                 SND (unproduct_mor g) o SND (unproduct_mor f) -:c2))`,
srw_tac [][compose_in_def,restrict_def,product_mor_def,compose_def,
           unproduct_mor_def,pre_product_cat_def] >>
rpt (pop_assum mp_tac) >> srw_tac [][composable_in_def] >>
Cases_on `f.cod` >> Cases_on `g.dom` >> fsrw_tac [][]);
val _ = export_rewrites["pre_product_cat_compose_in"];

val product_cat_def = Define`
  product_cat c1 c2 = mk_cat (pre_product_cat c1 c2)`;

val is_category_product_cat = Q.store_thm(
"is_category_product_cat",
`∀c1 c2. is_category c1 ∧ is_category c2
  ⇒ is_category (product_cat c1 c2)`,
srw_tac [][product_cat_def] >>
fsrw_tac [DNF_ss][category_axioms_def,FORALL_PROD] >>
conj_tac >- srw_tac [][pre_product_cat_id,pre_product_cat_maps_to_in] >>
conj_tac >- (
  srw_tac [][pre_product_cat_id] >>
  qmatch_abbrev_tac `f o g -:(pre_product_cat c1 c2) = h` >>
  `g ≈> f -:(pre_product_cat c1 c2)` by (
    unabbrev_all_tac >>
    srw_tac [][composable_in_def] ) >>
  unabbrev_all_tac >> srw_tac [][] ) >>
conj_tac >- (
  srw_tac [][pre_product_cat_id] >>
  qmatch_abbrev_tac `f o g -:(pre_product_cat c1 c2) = h` >>
  `g ≈> f -:(pre_product_cat c1 c2)` by (
    unabbrev_all_tac >>
    srw_tac [][composable_in_def] ) >>
  unabbrev_all_tac >> srw_tac [][] ) >>
conj_tac >- (
  srw_tac [][] >>
  qmatch_abbrev_tac `ff o gg -:ppc = ee o hh -:ppc` >>
  `gg ≈> ff -:ppc` by (
    unabbrev_all_tac >> srw_tac [][composable_comp] ) >>
  `hh ≈> ee -:ppc` by (
    unabbrev_all_tac >> srw_tac [][composable_comp] ) >>
  unabbrev_all_tac >> srw_tac [][] >>
  match_mp_tac comp_assoc >> fsrw_tac [][] ) >>
srw_tac [][] >>
`f ≈> g -:pre_product_cat c1 c2` by (
  fsrw_tac [][pre_product_cat_maps_to_in] >>
  srw_tac [][] >>
  match_mp_tac maps_to_composable >>
  metis_tac [] ) >>
fsrw_tac [][pre_product_cat_maps_to_in] >>
srw_tac [][] >>
match_mp_tac composable_maps_to >>
fsrw_tac [][maps_to_in_def,composable_in_def]);

val _ = export_theory ();
