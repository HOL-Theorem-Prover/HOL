open HolKernel boolLib bossLib lcsymtacs SatisfySimps

val _ = new_theory "category"

val extensional_def = Define`
  extensional f x = ∀e. e ∉ x ⇒ (f e = ARB)`

val restrict_def = Define`
  restrict f x = λe. if e ∈ x then f e else ARB`

val extensional_restrict = Q.store_thm(
"extensional_restrict",
`∀f x. extensional (restrict f x) x`,
srw_tac [][extensional_def,restrict_def])
val _ = export_rewrites["extensional_restrict"]

val _ = Hol_datatype `category =
  <| obj : 'a set ;
     mor : 'b set ;
     dom : 'b -> 'a ;
     cod : 'b -> 'a ;
     id : 'a -> 'b ;
     comp : 'b # 'b -> 'b |>`
val category_component_equality = DB.theorem "category_component_equality"

val maps_to_def = Define`
  maps_to c f x y = f ∈ c.mor ∧ (c.dom f = x) ∧ (c.cod f = y)`

val composable_def = Define`
  composable c gf = (SND gf) IN c.mor ∧ (FST gf) IN c.mor ∧
                    (c.cod (SND gf) = c.dom (FST gf))`

val extensional_category_def = Define`
  extensional_category c =
    extensional c.dom c.mor ∧
    extensional c.cod c.mor ∧
    extensional c.id c.obj ∧
    extensional c.comp (composable c)`

val category_axioms_def = Define`
  category_axioms c =
    (∀f. f ∈ c.mor ⇒ c.dom f ∈ c.obj) ∧
    (∀f. f ∈ c.mor ⇒ c.cod f ∈ c.obj) ∧
    (∀a. a ∈ c.obj ⇒ maps_to c (c.id a) a a) ∧
    (∀f. f ∈ c.mor ⇒ (c.comp (f, c.id (c.dom f)) = f)) ∧
    (∀f. f ∈ c.mor ⇒ (c.comp (c.id (c.cod f), f) = f)) ∧
    (∀f g h. composable c (g,f) ∧ composable c (h,g) ⇒
             (c.comp (h, (c.comp (g,f))) = c.comp (c.comp (h,g), f))) ∧
    (∀f g x y z. maps_to c f x y ∧ maps_to c g y z ⇒
                 maps_to c (c.comp (g,f)) x z)`

val is_category_def = Define`
  is_category c = extensional_category c ∧ category_axioms c`

val mk_cat_def = Define`
  mk_cat (c:('a,'b) category) = <|
    obj := c.obj;
    mor := c.mor;
    dom := restrict c.dom c.mor;
    cod := restrict c.cod c.mor;
    id := restrict c.id c.obj;
    comp := restrict c.comp (composable c) |>`

val mk_cat_maps_to = Q.store_thm(
"mk_cat_maps_to",
`∀c f x y. maps_to (mk_cat c) f x y = maps_to c f x y`,
srw_tac [][maps_to_def,mk_cat_def,restrict_def])

val mk_cat_composable = Q.store_thm(
"mk_cat_composable",
`∀c gf. composable (mk_cat c) gf = composable c gf`,
srw_tac [][composable_def,mk_cat_def,restrict_def])

val mk_cat_id = Q.store_thm(
"mk_cat_id",
`∀c a. a ∈ c.obj ⇒ ((mk_cat c).id a = c.id a)`,
srw_tac [][mk_cat_def,restrict_def])

val mk_cat_obj = Q.store_thm(
"mk_cat_obj",
`∀c. (mk_cat c).obj = c.obj`,
srw_tac [][mk_cat_def])

val mk_cat_mor = Q.store_thm(
"mk_cat_mor",
`∀c. (mk_cat c).mor = c.mor`,
srw_tac [][mk_cat_def])

val mk_cat_dom = Q.store_thm(
"mk_cat_dom",
`∀c f. f ∈ c.mor ⇒ ((mk_cat c).dom f = c.dom f)`,
srw_tac [][mk_cat_def,restrict_def])

val mk_cat_cod = Q.store_thm(
"mk_cat_cod",
`∀c f. f ∈ c.mor ⇒ ((mk_cat c).cod f = c.cod f)`,
srw_tac [][mk_cat_def,restrict_def])

val _ = export_rewrites
["mk_cat_maps_to","mk_cat_composable",
 "mk_cat_id","mk_cat_obj","mk_cat_mor",
 "mk_cat_dom","mk_cat_cod"]

val mk_cat_composable = Q.store_thm(
"mk_cat_composable",
`∀c. composable (mk_cat c) = composable c `,
srw_tac [][FUN_EQ_THM,composable_def])

val mk_cat_comp = Q.store_thm(
"mk_cat_comp",
`∀c gf. composable c gf ⇒ ((mk_cat c).comp gf = c.comp gf)`,
srw_tac [][mk_cat_def,restrict_def,IN_DEF])

val _ = export_rewrites["mk_cat_composable","mk_cat_comp"]

val extensional_mk_cat = Q.store_thm(
"extensional_mk_cat",
`∀c. extensional_category (mk_cat c)`,
srw_tac [][extensional_category_def,mk_cat_def])
val _ = export_rewrites["extensional_mk_cat"]

val maps_to_dom_composable = Q.store_thm(
"maps_to_dom_composable",
`∀c gf x. (FST gf) ∈ c.mor ∧ maps_to c (SND gf) x (c.dom (FST gf)) ⇒ composable c gf`,
srw_tac [][composable_def,maps_to_def])

val maps_to_cod_composable = Q.store_thm(
"maps_to_cod_composable",
`∀c gf y. (SND gf) ∈ c.mor ∧ maps_to c (FST gf) (c.cod (SND gf)) y ⇒ composable c gf`,
srw_tac [][composable_def,maps_to_def])

val mk_cat_is_category = Q.store_thm(
"mk_cat_is_category",
`∀c. category_axioms c ⇒ is_category (mk_cat c)`,
let fun sspecl l th = SIMP_RULE (srw_ss()) [] (Q.SPECL l th) in
srw_tac [][is_category_def] >>
fsrw_tac [][category_axioms_def] >>
fsrw_tac [][sspecl [`c`,`(f,c.id(c.dom f))`,`c.dom f`] maps_to_dom_composable] >>
fsrw_tac [][sspecl [`c`,`(c.id(c.cod f),f)`,`c.cod f`] maps_to_cod_composable] >>
conj_tac  >- (
  srw_tac [][] >>
  `composable c (c.comp (h,g),f)` by (
    fsrw_tac [][composable_def,maps_to_def] ) >>
  `composable c (h,c.comp (g,f))` by (
    fsrw_tac [][composable_def,maps_to_def] ) >>
  srw_tac [][] ) THEN
srw_tac [][] >>
`composable c (g,f)` by (
  fsrw_tac [][composable_def,maps_to_def] ) THEN
fsrw_tac [][maps_to_def,composable_def] end)

val composable_maps_to = Q.store_thm(
"composable_maps_to",
`∀c gf. is_category c ∧ composable c gf
⇒ maps_to c (c.comp gf) (c.dom (SND gf)) (c.cod (FST gf))`,
Cases_on `gf` >> srw_tac [][composable_def] >>
fsrw_tac [][is_category_def,category_axioms_def] >>
first_assum match_mp_tac >> srw_tac [][maps_to_def])

val maps_to_composable = Q.store_thm(
"maps_to_composable",
`∀c gf x y z. maps_to c (SND gf) x y ∧ maps_to c (FST gf) y z
⇒ composable c gf`,
srw_tac [][composable_def,maps_to_def])

val comp_mor_dom_cod = Q.store_thm(
"comp_mor_dom_cod",
`∀ c gf. is_category c ∧ composable c gf ⇒
 (FST gf) ∈ c.mor ∧ (SND gf) ∈ c.mor ∧
 (c.dom (c.comp gf) = c.dom (SND gf)) ∧
 (c.cod (c.comp gf) = c.cod (FST gf))`,
rpt strip_tac >>
imp_res_tac composable_maps_to >>
fsrw_tac [][maps_to_def,composable_def])

val maps_to_obj = Q.store_thm(
"maps_to_obj",
`∀c f x y.
is_category c ∧ maps_to c f x y
⇒ x ∈ c.obj ∧ y ∈ c.obj`,
srw_tac [][maps_to_def] >>
fsrw_tac [][is_category_def,category_axioms_def])

val id_inj = Q.store_thm(
"id_inj",
`∀c x y. is_category c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧ (c.id x = c.id y)
⇒ (x = y)`,
srw_tac [][is_category_def,category_axioms_def] >>
res_tac >> metis_tac [maps_to_def])

val composable_comp = Q.store_thm(
"composable_comp",
`∀c f g h. is_category c ∧
 composable c (g,f) ∧ composable c (h,g) ⇒
 composable c (c.comp (h,g), f) ∧
 composable c (h, c.comp (g,f))`,
srw_tac [][] >>
fsrw_tac [][is_category_def,category_axioms_def] >>
fsrw_tac [][maps_to_def,composable_def])

val id_mor = Q.store_thm(
"id_mor",
`∀c x. is_category c ∧
 x ∈ c.obj ⇒
 c.id x ∈ c.mor`,
srw_tac [][is_category_def,category_axioms_def,maps_to_def])

val id_composable_id = Q.store_thm(
"id_composable_id",
`∀c x. is_category c ∧
 x ∈ c.obj ⇒
 composable c (c.id x,c.id x)`,
srw_tac [][] >>
match_mp_tac maps_to_composable >>
fsrw_tac [][is_category_def,category_axioms_def] >>
metis_tac [])

val left_right_inv_unique = Q.store_thm(
"left_right_inv_unique",
`∀c f g h. is_category c ∧
 composable c (f,h) ∧ composable c (g,f) ∧
 (c.comp (g,f) = c.id (c.dom f)) ∧
 (c.comp (f,h) = c.id (c.cod f)) ⇒
 (h = g)`,
srw_tac [][is_category_def,category_axioms_def] >>
`h ∈ c.mor ∧ g ∈ c.mor ∧
 (c.dom f = c.cod h) ∧ (c.cod f = c.dom g)`
   by fsrw_tac [][composable_def] >>
metis_tac [composable_def])

val id_dom_cod = Q.store_thm(
"id_dom_cod",
`∀c x. is_category c ∧ x ∈ c.obj ⇒
 (c.dom (c.id x) = x) ∧
 (c.cod (c.id x) = x)`,
srw_tac [][is_category_def,category_axioms_def,maps_to_def])

val id_comp_id = Q.store_thm(
"id_comp_id",
`∀c x. is_category c ∧ x ∈ c.obj ⇒
 (c.comp (c.id x, c.id x) = c.id x)`,
rpt strip_tac >>
imp_res_tac id_dom_cod >>
fsrw_tac [][is_category_def,category_axioms_def,maps_to_def] >>
metis_tac [])

val iso_pair_def = Define`
  iso_pair c gf = composable c gf ∧
    (c.comp gf = c.id (c.dom (SND gf))) ∧
    (c.comp (SND gf, FST gf) = c.id (c.cod (SND gf)))`

val iso_def = Define`
  iso c f = ∃g. iso_pair c (g,f)`

val iso_pair_sym = Q.store_thm(
"iso_pair_sym",
`is_category c ∧
 iso_pair c (g,f) ⇒ iso_pair c (f,g)`,
srw_tac [][is_category_def,category_axioms_def] >>
fsrw_tac [][iso_pair_def,composable_def,maps_to_def] >>
metis_tac [])

val inv_unique = Q.store_thm(
"inv_unique",
`∀c f g h. is_category c ∧ iso_pair c (g,f) ∧ iso_pair c (h,f)
⇒ (g = h)`,
rpt strip_tac >>
match_mp_tac left_right_inv_unique >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def] >>
metis_tac [])

val id_iso_pair = Q.store_thm(
"id_iso_pair",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ iso_pair c (c.id x, c.id x)`,
srw_tac [][iso_pair_def] >- (
  match_mp_tac (GEN_ALL maps_to_composable) >>
  fsrw_tac [][is_category_def,category_axioms_def] >>
  metis_tac [] ) >>
fsrw_tac [][is_category_def,category_axioms_def,maps_to_def] >>
metis_tac [])

val inv_def = Define`
  inv c f = @g. iso_pair c (g,f)`

val inv_elim_thm = Q.store_thm(
"inv_elim_thm",
`∀P (c:('a,'b) category) f g. is_category c ∧ iso_pair c (g,f) ∧ P g ⇒ P (inv c f)`,
srw_tac [][inv_def] >>
SELECT_ELIM_TAC >>
srw_tac [SATISFY_ss][] >>
qsuff_tac `x=g` >- srw_tac [][] >>
match_mp_tac inv_unique >>
fsrw_tac [SATISFY_ss][]);

fun is_inv tm = let
  val (f,_) = dest_comb tm
  val (f,_) = dest_comb f
  val ("inv",ty) = dest_const f
in
  can (match_type ``:('a,'b) category -> 'b -> 'b``) ty
end handle HOL_ERR _ => false | Bind => false

fun inv_elim_tac (g as (_, w)) = let
  val t = find_term is_inv w
in
  CONV_TAC (UNBETA_CONV t) THEN
  MATCH_MP_TAC inv_elim_thm THEN BETA_TAC
end g

val inv_eq_iso_pair = Q.store_thm(
"inv_eq_iso_pair",
`∀c f g. is_category c ∧ iso_pair c (g,f) ⇒ (inv c f = g)`,
srw_tac [][] >>
inv_elim_tac >>
srw_tac [][])

val inv_idem = Q.store_thm(
"inv_idem",
`∀c f. is_category c ∧
 iso c f ⇒
 iso c (inv c f) ∧ (inv c (inv c f) = f)`,
srw_tac [][iso_def] >>
inv_elim_tac >>
srw_tac [][] >>
TRY inv_elim_tac >>
metis_tac [iso_pair_sym])

val iso_pair_mor = Q.store_thm(
"iso_pair_mor",
`∀c gf. is_category c ∧
 iso_pair c gf ⇒
 (FST gf) ∈ c.mor ∧ (SND gf) ∈ c.mor`,
srw_tac [][iso_pair_def,composable_def])

val iso_mor = Q.store_thm(
"iso_mor",
`∀c f. is_category c ∧ iso c f
⇒ f ∈ c.mor`,
srw_tac [][iso_def] >>
imp_res_tac iso_pair_mor >>
fsrw_tac [][])

val inv_mor_dom_cod = Q.store_thm(
"inv_mor_dom_cod",
`∀c f. is_category c ∧
 iso c f ⇒
 (inv c f) ∈ c.mor ∧
 (c.dom (inv c f) = c.cod f) ∧
 (c.cod (inv c f) = c.dom f)`,
srw_tac [][iso_def] >>
imp_res_tac inv_eq_iso_pair >>
imp_res_tac iso_pair_mor >>
imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def,composable_def])

val inv_composable = Q.store_thm(
"inv_composable",
`∀c f. is_category c ∧ iso c f ⇒
 composable c (f, inv c f) ∧
 composable c (inv c f, f)`,
srw_tac [][iso_def] >>
imp_res_tac iso_pair_sym >>
match_mp_tac maps_to_composable >>
imp_res_tac inv_eq_iso_pair >>
fsrw_tac [][iso_pair_def] >>
srw_tac [][maps_to_def] >>
fsrw_tac [][composable_def])

val comp_inv_id = Q.store_thm(
"comp_inv_id",
`∀c f. is_category c ∧ iso c f ⇒
 (c.comp (f, inv c f) = c.id (c.cod f)) ∧
 (c.comp (inv c f, f) = c.id (c.dom f))`,
srw_tac [][iso_def] >>
inv_elim_tac >>
imp_res_tac iso_pair_sym >>
imp_res_tac iso_pair_def >>
fsrw_tac [][composable_def] >>
metis_tac [])

val invs_composable = Q.store_thm(
"invs_composable",
`∀c gf. is_category c ∧ composable c gf ∧
 iso c (FST gf) ∧ iso c (SND gf) ⇒
 composable c (inv c (SND gf), inv c (FST gf))`,
srw_tac [][] >>
imp_res_tac inv_mor_dom_cod >>
fsrw_tac [][composable_def])

val iso_pair_comp = Q.store_thm(
"iso_pair_comp",
`∀c gf. is_category c ∧ composable c gf ∧
 iso c (FST gf) ∧ iso c (SND gf) ⇒
 iso_pair c (c.comp gf, c.comp (inv c (SND gf), inv c (FST gf)))`,
srw_tac [][] >>
`composable c (inv c (SND gf), inv c (FST gf))` by imp_res_tac invs_composable >>
`composable c (c.comp gf, c.comp (inv c (SND gf), inv c (FST gf)))` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >>
  imp_res_tac composable_maps_to >>
  imp_res_tac inv_mor_dom_cod >>
  imp_res_tac comp_mor_dom_cod >>
  map_every qexists_tac [`c.cod (FST gf)`,`c.dom (SND gf)`,`c.cod (FST gf)`] >>
  srw_tac [][] >> fsrw_tac [][maps_to_def] ) >>
Cases_on `gf` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `composable c (inv c f,inv c g)` [] >>
imp_res_tac is_category_def >>
`c.comp (c.comp (g,f),c.comp(inv c f,inv c g)) = c.comp (c.comp (c.comp (g,f), inv c f), inv c g)` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum match_mp_tac >> srw_tac [][] >>
  match_mp_tac (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL (SPEC_ALL composable_comp)))) >>
  fsrw_tac [][inv_composable] ) >>
`c.comp (c.comp (g,f), inv c f) = c.comp (g, c.comp (f, inv c f))` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum (match_mp_tac o GSYM) >> srw_tac [][] >>
  fsrw_tac [][inv_composable] ) >>
`c.comp (c.comp (inv c f, inv c g), c.comp (g,f)) = c.comp (inv c f, c.comp (inv c g, c.comp (g,f)))` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum (match_mp_tac o GSYM) >> srw_tac [][] >>
  match_mp_tac (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL (SPEC_ALL composable_comp)))) >>
  fsrw_tac [][inv_composable] ) >>
`c.comp (inv c g, c.comp (g,f)) = c.comp (c.comp (inv c g, g), f)` by (
  fsrw_tac [][category_axioms_def] >>
  first_assum match_mp_tac >> srw_tac [][] >>
  fsrw_tac [][inv_composable] ) >>
`c.cod f = c.dom g` by fsrw_tac [][composable_def] >>
imp_res_tac comp_inv_id >>
imp_res_tac inv_mor_dom_cod >>
imp_res_tac comp_mor_dom_cod >>
fsrw_tac [][] >>
fsrw_tac [][category_axioms_def] >>
srw_tac [][iso_pair_def] >>
metis_tac [])

val iso_objs_def = Define`
  iso_objs c a b = ∃f. maps_to c f a b ∧ iso c f`

val unit_cat_def = Define`
  unit_cat = mk_cat <| obj := {()}; mor := {()}; dom := K (); cod := K (); id := K (); comp := K () |>`

val is_category_unit_cat = Q.store_thm(
"is_category_unit_cat",
`is_category unit_cat`,
srw_tac [][unit_cat_def] >>
match_mp_tac mk_cat_is_category >>
srw_tac [][category_axioms_def,maps_to_def])

val op_cat_def = Define`
  op_cat c = <| obj := c.obj; mor := c.mor; dom := c.cod; cod := c.dom; id := c.id; comp := λ(f,g). c.comp (g,f) |>`

val op_cat_idem = Q.store_thm(
"op_cat_idem",
`op_cat (op_cat c) = c`,
srw_tac [][op_cat_def,category_component_equality,
           FUN_EQ_THM,pairTheory.UNCURRY])

val op_cat_axioms = Q.store_thm(
"op_cat_axioms",
`category_axioms c ⇒ category_axioms (op_cat c)`,
srw_tac [][category_axioms_def,op_cat_def,maps_to_def,composable_def])

val op_cat_extensional = Q.store_thm(
"op_cat_extensional",
`extensional_category c ⇒ extensional_category (op_cat c)`,
srw_tac [][extensional_category_def,op_cat_def] >>
srw_tac [][extensional_def,IN_DEF,pairTheory.UNCURRY] >>
fsrw_tac [][composable_def,IN_DEF,extensional_def])

val is_category_op_cat = Q.store_thm(
"is_category_op_cat",
`is_category c ⇒ is_category (op_cat c)`,
srw_tac [][is_category_def,op_cat_axioms,op_cat_extensional])

val op_maps_to = Q.store_thm(
"op_maps_to",
`maps_to c f x y ⇒ maps_to (op_cat c) f y x`,
srw_tac [][maps_to_def,op_cat_def])

val op_composable = Q.store_thm(
"op_composable",
`composable c (SND gf, FST gf) ⇒ composable (op_cat c) gf`,
srw_tac [][composable_def,op_cat_def])

val _ = export_theory ()
