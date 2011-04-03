open HolKernel boolLib bossLib lcsymtacs pairTheory SatisfySimps

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

val restrict_idem = Q.store_thm(
"restrict_idem",
`∀f x. restrict (restrict f x) x = restrict f x`,
srw_tac [][restrict_def])

val extensional_restrict_iff = Q.store_thm(
"extensional_restrict_iff",
`∀f x. extensional f x  = (f = restrict f x)`,
srw_tac [][EQ_IMP_THM] >- (
  fsrw_tac [][restrict_def,extensional_def,FUN_EQ_THM] >>
  srw_tac [][] ) >>
metis_tac [extensional_restrict])

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

val is_category_mk_cat = Q.store_thm(
"is_category_mk_cat",
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

val comp_assoc = Q.store_thm(
"comp_assoc",
`∀c f g h. is_category c ∧ composable c (g,f) ∧ composable c (h,g)
 ⇒ (c.comp (h,c.comp (g,f)) = c.comp (c.comp (h,g), f))`,
srw_tac [][is_category_def,category_axioms_def])

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

val id_comp1 = Q.store_thm(
"id_comp1",
`∀c f x. is_category c ∧ f ∈ c.mor ∧ (x = c.dom f) ⇒
  (c.comp (f, c.id x) = f)`,
srw_tac [][is_category_def,category_axioms_def])

val id_comp2 = Q.store_thm(
"id_comp2",
`∀c f x. is_category c ∧ f ∈ c.mor ∧ (x = c.cod f) ⇒
  (c.comp (c.id x, f) = f)`,
srw_tac [][is_category_def,category_axioms_def])

val id_comp_id = Q.store_thm(
"id_comp_id",
`∀c x. is_category c ∧ x ∈ c.obj ⇒
 (c.comp (c.id x, c.id x) = c.id x)`,
rpt strip_tac >>
imp_res_tac id_dom_cod >>
fsrw_tac [][is_category_def,category_axioms_def,maps_to_def] >>
metis_tac [])
val _ = export_rewrites["id_comp_id"]

val iso_pair_def = Define`
  iso_pair c gf = composable c gf ∧
    (c.comp gf = c.id (c.dom (SND gf))) ∧
    (c.comp (SND gf, FST gf) = c.id (c.cod (SND gf)))`

val iso_def = Define`
  iso c f = ∃g. iso_pair c (g,f)`

val iso_pair_sym = Q.store_thm(
"iso_pair_sym",
`∀c g f. is_category c ∧ iso_pair c (g,f) ⇒ iso_pair c (f,g)`,
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
match_mp_tac is_category_mk_cat >>
srw_tac [][category_axioms_def,maps_to_def])

val op_cat_def = Define`
  op_cat c = <| obj := c.obj; mor := c.mor; dom := c.cod; cod := c.dom; id := c.id; comp := λ(f,g). c.comp (g,f) |>`

val op_cat_idem = Q.store_thm(
"op_cat_idem",
`∀c. op_cat (op_cat c) = c`,
srw_tac [][op_cat_def,category_component_equality,
           FUN_EQ_THM,UNCURRY])

val op_cat_axioms = Q.store_thm(
"op_cat_axioms",
`∀c. category_axioms c ⇒ category_axioms (op_cat c)`,
srw_tac [][category_axioms_def,op_cat_def,maps_to_def,composable_def])

val op_cat_extensional = Q.store_thm(
"op_cat_extensional",
`∀c. extensional_category c ⇒ extensional_category (op_cat c)`,
srw_tac [][extensional_category_def,op_cat_def] >>
srw_tac [][extensional_def,IN_DEF,UNCURRY] >>
fsrw_tac [][composable_def,IN_DEF,extensional_def])

val is_category_op_cat = Q.store_thm(
"is_category_op_cat",
`∀c. is_category c ⇒ is_category (op_cat c)`,
srw_tac [][is_category_def,op_cat_axioms,op_cat_extensional])

val op_maps_to = Q.store_thm(
"op_maps_to",
`∀c f x y. maps_to c f x y ⇒ maps_to (op_cat c) f y x`,
srw_tac [][maps_to_def,op_cat_def])

val op_composable = Q.store_thm(
"op_composable",
`∀c gf. composable c (SND gf, FST gf) ⇒ composable (op_cat c) gf`,
srw_tac [][composable_def,op_cat_def])

val _ = Hol_datatype `functor =
  <| dom : ('a1,'b1) category;
     cod : ('a2,'b2) category;
     morf : 'b1 -> 'b2 |>`

val objf_def = Define`
  objf f x = @y. y ∈ f.cod.obj ∧ (f.morf (f.dom.id x) = f.cod.id y)`

val functor_axioms_def = Define`
  functor_axioms G =
  is_category G.dom ∧ is_category G.cod ∧
  (∀f x y. maps_to G.dom f x y ⇒ maps_to G.cod (G.morf f) (objf G x) (objf G y)) ∧
  (∀x. x ∈ G.dom.obj ⇒ ∃y. y ∈ G.cod.obj ∧ (G.morf (G.dom.id x) = G.cod.id y)) ∧
  (∀f g. composable G.dom (g,f) ⇒ (G.morf (G.dom.comp (g,f)) = G.cod.comp (G.morf g, G.morf f)))`

val extensional_functor_def = Define`
  extensional_functor f = extensional f.morf f.dom.mor`

val mk_functor_def = Define`
  mk_functor f = <| dom := f.dom; cod := f.cod; morf := restrict f.morf f.dom.mor |>`

val is_functor_def = Define`
  is_functor f = extensional_functor f ∧ functor_axioms f`

val is_functor_is_category = Q.store_thm(
"is_functor_is_category",
`∀f. is_functor f ⇒ is_category f.dom ∧ is_category f.cod`,
srw_tac [][is_functor_def,functor_axioms_def])

val composable_functors_def = Define`
  composable_functors gf =
    (is_functor (FST gf)) ∧ (is_functor (SND gf)) ∧
    ((FST gf).dom = (SND gf).cod)`

val functor_maps_to_def = Define`
  functor_maps_to f x y = is_functor f ∧ (f.dom = x) ∧ (f.cod = y)`

val functor_maps_to_dom_cod = Q.store_thm(
"functor_maps_to_dom_cod",
`∀f. is_functor f ⇒ functor_maps_to f f.dom f.cod`,
srw_tac [][functor_maps_to_def])
val _ = export_rewrites["functor_maps_to_dom_cod"]

val maps_to_morf = Q.store_thm(
"maps_to_morf",
`∀G f. is_functor G ∧ f ∈ G.dom.mor ⇒
 maps_to G.cod (G.morf f) (objf G (G.dom.dom f)) (objf G (G.dom.cod f))`,
srw_tac [][is_functor_def,functor_axioms_def] >>
first_assum match_mp_tac >>
srw_tac [][maps_to_def])

val morf_mor_dom_cod = Q.store_thm(
"morf_mor_dom_cod",
`∀G f. is_functor G ∧ f ∈ G.dom.mor ⇒
 G.morf f ∈ G.cod.mor ∧
 (G.cod.dom (G.morf f) = objf G (G.dom.dom f)) ∧
 (G.cod.cod (G.morf f) = objf G (G.dom.cod f))`,
rpt strip_tac >>
imp_res_tac maps_to_morf >>
fsrw_tac [][maps_to_def])

val composable_morf = Q.store_thm(
"composable_morf",
`∀G gf. is_functor G ∧ composable G.dom gf ⇒
 composable G.cod (G.morf (FST gf), G.morf (SND gf))`,
rpt strip_tac >>
imp_res_tac is_functor_is_category >>
match_mp_tac maps_to_composable >>
fsrw_tac [][composable_def] >>
imp_res_tac maps_to_morf >>
metis_tac [])

val morf_comp = Q.store_thm(
"morf_comp",
`∀G c1 c2 gf. functor_maps_to G c1 c2 ∧ composable c1 gf ⇒
 (G.morf (c1.comp gf) = c2.comp (G.morf (FST gf), G.morf (SND gf)))`,
Cases_on `gf` >>
srw_tac [][functor_maps_to_def,is_functor_def,functor_axioms_def] >>
srw_tac [][])

val morf_composable = Q.store_thm(
"morf_composable",
`∀G c1 c2 gf. functor_maps_to G c1 c2 ∧ composable c1 gf ⇒
 composable c2 (G.morf (FST gf), G.morf (SND gf))`,
srw_tac [][functor_maps_to_def] >>
srw_tac [][composable_morf])

val morf_maps_to = Q.store_thm(
"morf_maps_to",
`∀G c1 c2 f x y. functor_maps_to G c1 c2 ∧ maps_to c1 f x y ⇒
 maps_to c2 (G.morf f) (objf G x) (objf G y)`,
srw_tac [][functor_maps_to_def,Once maps_to_def] >>
srw_tac [][maps_to_morf])

val morf_id = Q.store_thm(
"morf_id",
`∀G c1 c2 x. functor_maps_to G c1 c2 ∧ x ∈ c1.obj ⇒
 (G.morf (c1.id x) = c2.id (objf G x))`,
srw_tac [][functor_maps_to_def,is_functor_def,functor_axioms_def,objf_def] >>
SELECT_ELIM_TAC >>
srw_tac [][])

val mk_functor_dom = Q.store_thm(
"mk_functor_dom",
`∀f. (mk_functor f).dom = f.dom`,
srw_tac [][mk_functor_def])

val mk_functor_cod = Q.store_thm(
"mk_functor_cod",
`∀f. (mk_functor f).cod = f.cod`,
srw_tac [][mk_functor_def])

val mk_functor_morf = Q.store_thm(
"mk_functor_morf",
`∀f x. x ∈ f.dom.mor ⇒ ((mk_functor f).morf x = f.morf x)`,
srw_tac [][mk_functor_def,restrict_def])
val _ = export_rewrites["mk_functor_dom","mk_functor_cod","mk_functor_morf"]

val mk_functor_objf = Q.store_thm(
"mk_functor_objf",
`∀f x. is_category f.dom ∧ x ∈ f.dom.obj ⇒ (objf (mk_functor f) x = objf f x)`,
rpt strip_tac >> imp_res_tac id_mor >> srw_tac [][objf_def])
val _ = export_rewrites["mk_functor_objf"]

val is_functor_mk_functor = Q.store_thm(
"is_functor_mk_functor",
`∀f. functor_axioms f ⇒ is_functor (mk_functor f)`,
srw_tac [][is_functor_def,extensional_functor_def] >-
  srw_tac [][mk_functor_def] >>
fsrw_tac [][functor_axioms_def] >>
imp_res_tac id_mor >>
imp_res_tac comp_mor_dom_cod >>
imp_res_tac is_category_def >>
fsrw_tac [][category_axioms_def] >>
fsrw_tac [][maps_to_def,composable_def])

val id_functor_def = Define`
  id_functor c = mk_functor <| dom := c; cod := c; morf := I |>`

val is_functor_id_functor = Q.store_thm(
"is_functor_id_functor",
`∀c. is_category c ⇒ is_functor (id_functor c)`,
srw_tac [][id_functor_def] >>
match_mp_tac is_functor_mk_functor >>
reverse (srw_tac [][functor_axioms_def,maps_to_def,objf_def]) >- (
  qexists_tac `x` >> srw_tac [][] ) >> (
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  fsrw_tac [][is_category_def,category_axioms_def] >>
  metis_tac [] ) >>
imp_res_tac id_inj >>
fsrw_tac [][is_category_def,category_axioms_def]))

val K_functor_def = Define`
  K_functor c1 c2 x = mk_functor <|
    dom := c1; cod := c2; morf := K (c2.id x) |>`

val is_functor_K_functor = Q.store_thm(
"is_functor_K_functor",
`∀c1 c2 x. is_category c1 ∧ is_category c2 ∧ x ∈ c2.obj
⇒ is_functor (K_functor c1 c2 x)`,
srw_tac [][K_functor_def] >>
match_mp_tac is_functor_mk_functor >>
srw_tac [][functor_axioms_def] >- (
  imp_res_tac id_mor >>
  imp_res_tac id_dom_cod >>
  srw_tac [][maps_to_def] >>
  srw_tac [][objf_def] >>
  SELECT_ELIM_TAC >>
  metis_tac [id_inj] ) >-
metis_tac [] >>
srw_tac [][])

val unit_functor_def = Define`
  unit_functor c = K_functor c unit_cat ()`

val is_functor_unit_functor = Q.store_thm(
"is_functor_unit_functor",
`∀c. is_category c ⇒ is_functor (unit_functor c)`,
srw_tac [][unit_functor_def] >>
match_mp_tac is_functor_K_functor >>
srw_tac [][is_category_unit_cat] >>
srw_tac [][unit_cat_def])

val functor_comp_def = Define`
  functor_comp gf = mk_functor
    <| dom := (SND gf).dom; cod := (FST gf).cod;
       morf := (FST gf).morf o (SND gf).morf |>`

val functor_comp_comp = Q.store_thm(
"functor_comp_comp",
`!GF gf. composable (SND GF).dom gf ∧ composable_functors GF ⇒
 ((FST GF).morf ((SND GF).morf ((SND GF).dom.comp gf)) =
  (FST GF).cod.comp
    ((FST GF).morf ((SND GF).morf (FST gf)),
     (FST GF).morf ((SND GF).morf (SND gf))))`,
srw_tac [][composable_functors_def] >>
`functor_maps_to (SND GF) (SND GF).dom (SND GF).cod` by srw_tac [][] >>
`functor_maps_to (FST GF) (FST GF).dom (FST GF).cod` by srw_tac [][] >>
`(SND GF).morf ((SND GF).dom.comp gf) =
 (SND GF).cod.comp ((SND GF).morf (FST gf),(SND GF).morf (SND gf))` by
  imp_res_tac morf_comp >>
srw_tac [][] >>
qpat_assum `x = (SND GF).cod` (assume_tac o SYM) >>
srw_tac [][] >>
qmatch_abbrev_tac `G.morf (c1.comp X) = c2.comp (G.morf Y, G.morf Z)` >>
`(Y = (FST X)) ∧ (Z = (SND X))` by srw_tac [][Abbr`X`,Abbr`Y`,Abbr`Z`] >>
srw_tac [][] >>
match_mp_tac morf_comp >> srw_tac [][] >>
unabbrev_all_tac >>
match_mp_tac morf_composable >>
qexists_tac `(SND GF).dom` >>
srw_tac [][functor_maps_to_def])

val functor_comp_id = Q.store_thm(
"functor_comp_id",
`∀gf x. x ∈ (SND gf).dom.obj ∧
  composable_functors gf ⇒
  objf (FST gf) (objf (SND gf) x) ∈ (FST gf).cod.obj ∧
  ((FST gf).morf ((SND gf).morf ((SND gf).dom.id x)) =
   (FST gf).cod.id (objf (FST gf) (objf (SND gf) x)))`,
srw_tac [][composable_functors_def] >- (
  imp_res_tac is_functor_def >>
  imp_res_tac functor_axioms_def >>
  srw_tac [][objf_def] >>
  SELECT_ELIM_TAC >> srw_tac [][] >>
  SELECT_ELIM_TAC >> srw_tac [][] >>
  metis_tac [] ) >>
`functor_maps_to (SND gf) (SND gf).dom (SND gf).cod` by srw_tac [][] >>
`functor_maps_to (FST gf) (FST gf).dom (FST gf).cod` by srw_tac [][] >>
`objf (SND gf) x ∈ (FST gf).dom.obj` by (
  srw_tac [][objf_def] >>
  SELECT_ELIM_TAC >> srw_tac [][] >>
  fsrw_tac [][is_functor_def,functor_axioms_def] ) >>
Q.ISPECL_THEN [`SND gf`] imp_res_tac morf_id >>
srw_tac [][] >>
qpat_assum `X = (SND gf).cod` (assume_tac o SYM) >>
srw_tac [][] >>
Q.ISPECL_THEN [`FST gf`] imp_res_tac morf_id)

val functor_comp_maps_to = Q.store_thm(
"functor_comp_maps_to",
`∀GF f. f ∈ (functor_comp GF).dom.mor ∧ composable_functors GF ⇒
  maps_to (FST GF).cod ((FST GF).morf ((SND GF).morf f))
    (objf (FST GF) (objf (SND GF) ((SND GF).dom.dom f)))
    (objf (FST GF) (objf (SND GF) ((SND GF).dom.cod f)))`,
srw_tac [][] >>
imp_res_tac composable_functors_def >>
match_mp_tac morf_maps_to >>
qexists_tac `(FST GF).dom` >> srw_tac [][] >>
match_mp_tac morf_maps_to >>
qexists_tac `(SND GF).dom` >> srw_tac [][] >>
srw_tac [][maps_to_def] >>
fsrw_tac [][functor_comp_def])

val objf_in_obj = Q.store_thm(
"objf_in_obj",
`∀f x. x ∈ f.dom.obj ∧ is_functor f ⇒ objf f x ∈ f.cod.obj`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
fsrw_tac [][is_functor_def,functor_axioms_def])

val objf_functor_comp = Q.store_thm(
"objf_functor_comp",
`∀(gf:('f,'d,'e,'b) functor # ('c,'f,'a,'e) functor) fc x.
(fc.morf = (FST gf).morf o (SND gf).morf) ∧
 (fc.dom = (SND gf).dom) ∧ (fc.cod = (FST gf).cod) ∧
 composable_functors gf ∧
 x ∈ (SND gf).dom.obj
⇒ (objf fc x = objf (FST gf) (objf (SND gf) x))`,
srw_tac [][objf_def] >>
imp_res_tac functor_comp_id >>
srw_tac [][] >>
SELECT_ELIM_TAC >> srw_tac [][] >-
  metis_tac [] >>
SELECT_ELIM_TAC >> srw_tac [][] >- (
  `is_category (FST gf).cod` by (
    fsrw_tac [][composable_functors_def,is_functor_is_category] ) >>
  Q.ISPECL_THEN [`(FST gf).cod`,`objf (FST gf) (objf (SND gf) x)`]
    mp_tac id_inj >>
  srw_tac [][] >> res_tac >> srw_tac [][] >>
  qexists_tac `objf (FST gf) (objf (SND gf) x)` >>
  srw_tac [][] >>
  srw_tac [][GSYM objf_def] >>
  match_mp_tac morf_id >>
  imp_res_tac composable_functors_def >>
  srw_tac [][] >>
  match_mp_tac objf_in_obj >>
  srw_tac [][] ) >>
fsrw_tac [][GSYM objf_def] >>
match_mp_tac id_inj >>
qexists_tac `(FST gf).cod` >>
imp_res_tac composable_functors_def >>
imp_res_tac is_functor_is_category >>
srw_tac [][] >>
qmatch_abbrev_tac `A = B` >>
qpat_assum `X = B` (assume_tac o SYM) >>
qpat_assum `X = A` (assume_tac o SYM) >>
srw_tac [][] >>
match_mp_tac EQ_SYM >>
match_mp_tac morf_id >>
srw_tac [][functor_maps_to_def] >>
match_mp_tac objf_in_obj >>
srw_tac [][])

val is_functor_comp = Q.store_thm(
"is_functor_comp",
`∀gf. composable_functors gf ⇒ is_functor (functor_comp gf)`,
srw_tac [][] >>
imp_res_tac functor_comp_maps_to >>
fsrw_tac [][functor_comp_def] >>
match_mp_tac is_functor_mk_functor >>
imp_res_tac composable_functors_def >>
srw_tac [][functor_axioms_def]
>- fsrw_tac [][is_functor_def,functor_axioms_def]
>- fsrw_tac [][is_functor_def,functor_axioms_def]
>- (
  qmatch_abbrev_tac
    `maps_to (FST gf).cod ((FST gf).morf ((SND gf).morf f))
       (objf fc x) (objf fc y)` >>
  qsuff_tac
    `(objf fc x = objf (FST gf) (objf (SND gf) ((SND gf).dom.dom f))) ∧
     (objf fc y = objf (FST gf) (objf (SND gf) ((SND gf).dom.cod f)))` >-
    metis_tac [maps_to_def] >>
  fsrw_tac [][maps_to_def] >>
  srw_tac [][] >>
  match_mp_tac objf_functor_comp >>
  srw_tac [][Abbr`fc`] >>
  imp_res_tac is_functor_is_category >>
  imp_res_tac is_category_def >>
  metis_tac [category_axioms_def])
>- metis_tac [functor_comp_id] >>
qspecl_then [`GF`,`(g,f)`]
  (match_mp_tac o SIMP_RULE (srw_ss()) []) functor_comp_comp >>
srw_tac [][])

val functor_preserves_iso = Q.store_thm(
"functor_preserves_iso",
`∀f k. is_functor f ∧ iso f.dom k ⇒ iso f.cod (f.morf k)`,
srw_tac [][iso_def] >>
imp_res_tac is_functor_is_category >>
Q.ISPEC_THEN `f.dom` imp_res_tac iso_pair_sym >>
fsrw_tac [][iso_pair_def] >>
qexists_tac `f.morf g` >>
conj_tac >- (
  qspecl_then [`f`,`(g,k)`] mp_tac composable_morf >>
  srw_tac [][] ) >>
conj_tac >- (
  qspecl_then [`f`,`f.dom`,`f.cod`,`(g,k)`] mp_tac (GSYM morf_comp) >>
  srw_tac [][] >>
  `k ∈ f.dom.mor` by fsrw_tac [][composable_def] >>
  `f.dom.dom k ∈ f.dom.obj` by (
    fsrw_tac [][is_category_def,category_axioms_def] ) >>
  qspecl_then [`f`,`f.dom`,`f.cod`,`f.dom.dom k`] mp_tac morf_id >>
  srw_tac [][] >>
  fsrw_tac [][is_functor_def,functor_axioms_def,maps_to_def] ) >>
qspecl_then [`f`,`f.dom`,`f.cod`,`(k,g)`] mp_tac (GSYM morf_comp) >>
srw_tac [][] >>
`k ∈ f.dom.mor` by fsrw_tac [][composable_def] >>
`f.dom.cod k ∈ f.dom.obj` by (
  fsrw_tac [][is_category_def,category_axioms_def] ) >>
qspecl_then [`f`,`f.dom`,`f.cod`,`f.dom.cod k`] mp_tac morf_id >>
srw_tac [][] >>
fsrw_tac [][is_functor_def,functor_axioms_def,maps_to_def])

val full_def = Define`
  full f = ∀h a b. a ∈ f.dom.obj ∧ b ∈ f.dom.obj ∧
                   maps_to f.cod h (f.morf a) (f.morf b) ⇒
                   ∃g. maps_to f.dom g a b ∧ (f.morf g = h)`

val faithful_def = Define`
  faithful f = ∀g h a b. maps_to f.dom g a b ∧ maps_to f.dom h a b ∧
                         (f.morf g = f.morf h) ⇒
                           (g = h)`

val surj_obj_def = Define`
  surj_obj f = ∀c. c ∈ f.cod.obj ⇒ ∃a. a ∈ f.dom.obj ∧ iso_objs f.cod (objf f a) c`

val equivalence_def = Define`
  equivalence f = full f ∧ faithful f ∧ surj_obj f`

val _ = Hol_datatype `nat_trans =
  <| dom : ('a1,'b1,'a2,'b2) functor;
     cod : ('a1,'b1,'a2,'b2) functor;
     at : 'a1 -> 'b2 |>`

val nat_trans_component_equality = DB.theorem "nat_trans_component_equality"

val _ = Parse.overload_on("ntdom", ``λn. n.dom.dom``)
val _ = Parse.overload_on("ntcod", ``λn. n.cod.cod``)

val extensional_nat_trans_def = Define`
  extensional_nat_trans n = extensional n.at (ntdom n).obj`

val nat_trans_axioms_def = Define`
  nat_trans_axioms n =
    is_functor n.dom ∧
    is_functor n.cod ∧
    (n.dom.dom = n.cod.dom) ∧
    (n.dom.cod = n.cod.cod) ∧
    (∀x. x ∈ (ntdom n).obj ⇒
         maps_to (ntcod n) (n.at x) (objf n.dom x) (objf n.cod x)) ∧
    (∀f x y. maps_to (ntdom n) f x y ⇒
      ((ntcod n).comp (n.at y, n.dom.morf f) =
       (ntcod n).comp (n.cod.morf f, n.at x)))`

val is_nat_trans_def = Define`
  is_nat_trans n = extensional_nat_trans n ∧ nat_trans_axioms n`

val mk_nt_def = Define`
  mk_nt n = <| dom := n.dom; cod := n.cod; at := restrict n.at (ntdom n).obj |>`

val is_nat_trans_mk_nt = Q.store_thm(
"is_nat_trans_def",
`∀n. nat_trans_axioms n ⇒ is_nat_trans (mk_nt n)`,
srw_tac [][mk_nt_def,is_nat_trans_def,extensional_nat_trans_def] >>
fsrw_tac [][nat_trans_axioms_def] >>
srw_tac [][restrict_def] >>
imp_res_tac is_functor_is_category >>
imp_res_tac maps_to_obj)

val nt_maps_to_def = Define`
  nt_maps_to n f g = is_nat_trans n ∧ (n.dom = f) ∧ (n.cod = g)`

val nt_maps_to_dom_cod = Q.store_thm(
"nt_maps_to_dom_cod",
`∀n. is_nat_trans n ⇒ nt_maps_to n n.dom n.cod`,
srw_tac [][nt_maps_to_def])
val _ = export_rewrites["nt_maps_to_dom_cod"]

val naturality = Q.store_thm(
"naturality",
`∀n f g c k x y.
  nt_maps_to n f g ∧ (c = ntcod n) ∧
  maps_to (ntdom n) k x y ⇒
(c.comp (n.at y, f.morf k) = c.comp (g.morf k, n.at x))`,
srw_tac [][nt_maps_to_def,is_nat_trans_def,nat_trans_axioms_def] >>
first_assum match_mp_tac >> first_assum ACCEPT_TAC)

val nt_at_maps_to = Q.store_thm(
"nt_at_maps_to",
`∀n f g x. nt_maps_to n f g ∧ x ∈ f.dom.obj ⇒
   maps_to g.cod (n.at x) (objf f x) (objf g x)`,
srw_tac [][nt_maps_to_def,is_nat_trans_def,nat_trans_axioms_def] >>
res_tac)

val composable_nts_def = Define`
  composable_nts nm = is_nat_trans (FST nm) ∧ is_nat_trans (SND nm) ∧
    (ntdom (FST nm) = ntdom (SND nm)) ∧
    (ntcod (FST nm) = ntcod (SND nm)) ∧
    ((FST nm).dom = (SND nm).cod)`

val nt_eq_thm = Q.store_thm(
"nt_eq_thm",
`∀n1 n2. is_nat_trans n1 ∧ is_nat_trans n2 ∧
    (n1.dom = n2.dom) ∧ (n1.cod = n2.cod) ∧
    (∀x. x ∈ (ntdom n1).obj ⇒ (n1.at x = n2.at x)) ⇒
      (n1 = n2)`,
srw_tac [][nat_trans_component_equality,is_nat_trans_def,
     extensional_nat_trans_def,extensional_def,FUN_EQ_THM] >>
metis_tac [])

val id_nt_def = Define`
  id_nt f = mk_nt <| dom := f; cod := f; at := λx. f.cod.id (objf f x) |>`

val is_nat_trans_id_nt = Q.store_thm(
"is_nat_trans_id_nt",
`∀f. is_functor f ⇒ is_nat_trans (id_nt f)`,
srw_tac [][id_nt_def] >>
match_mp_tac is_nat_trans_mk_nt >>
srw_tac [][nat_trans_axioms_def] >- (
  metis_tac [maps_to_morf,id_mor,morf_id,functor_maps_to_def,
             is_functor_is_category,id_dom_cod] ) >>
`f.cod.id (objf f x) = f.morf (f.dom.id x)` by (
  match_mp_tac (GSYM morf_id) >> srw_tac [][] >>
  fsrw_tac [][maps_to_def] >>
  metis_tac [is_category_def,is_functor_is_category,category_axioms_def] ) >>
`f.cod.id (objf f y) = f.morf (f.dom.id y)` by (
  match_mp_tac (GSYM morf_id) >> srw_tac [][] >>
  fsrw_tac [][maps_to_def] >>
  metis_tac [is_category_def,is_functor_is_category,category_axioms_def] ) >>
srw_tac [][] >>
qmatch_assum_rename_tac `maps_to f.dom g x y` [] >>
match_mp_tac EQ_TRANS >>
qexists_tac `f.morf (f.dom.comp (f.dom.id y,g))` >>
conj_tac >- (
  match_mp_tac (GSYM (SIMP_RULE (srw_ss()) [FORALL_PROD] morf_comp)) >>
  srw_tac [][] >>
  match_mp_tac maps_to_composable >>
  map_every qexists_tac [`x`,`y`,`y`] >>
  srw_tac [][] >>
  imp_res_tac is_functor_is_category >>
  imp_res_tac maps_to_obj >>
  fsrw_tac [][is_category_def,category_axioms_def] ) >>
match_mp_tac EQ_TRANS >>
qexists_tac `f.morf (f.dom.comp (g, f.dom.id x))` >>
conj_tac >- (
  imp_res_tac is_functor_is_category >>
  imp_res_tac maps_to_def >>
  fsrw_tac [][is_category_def,category_axioms_def] >>
  metis_tac [] ) >>
match_mp_tac (SIMP_RULE (srw_ss()) [FORALL_PROD] morf_comp) >>
srw_tac [][] >>
match_mp_tac maps_to_composable >>
map_every qexists_tac [`x`,`x`,`y`] >>
srw_tac [][] >>
imp_res_tac is_functor_is_category >>
imp_res_tac maps_to_obj >>
fsrw_tac [][is_category_def,category_axioms_def])

val nt_comp_def = Define`
  nt_comp nm = mk_nt <|
    dom := (SND nm).dom; cod := (FST nm).cod;
    at := λx. (ntcod (FST nm)).comp ((FST nm).at x, (SND nm).at x) |>`

val nt_comp1 = Q.store_thm(
"nt_comp1",
`∀gf x. x ∈ (ntdom (SND gf)).obj ⇒
((nt_comp gf).at x = (ntcod (FST gf)).comp ((FST gf).at x, ((SND gf).at x)))`,
srw_tac [][nt_comp_def,mk_nt_def,restrict_def])

val nt_comp2 = Q.store_thm(
"nt_comp2",
`∀gf x. x ∈ (ntdom (SND gf)).obj ∧ composable_nts gf ⇒
((nt_comp gf).at x = (ntcod (SND gf)).comp ((FST gf).at x, ((SND gf).at x)))`,
srw_tac [][nt_comp_def,mk_nt_def,restrict_def,composable_nts_def])

val is_nat_trans_is_functor = Q.store_thm(
"is_nat_trans_is_functor",
`∀n. is_nat_trans n ⇒ is_functor n.dom ∧ is_functor n.cod`,
srw_tac [][is_nat_trans_def,nat_trans_axioms_def])

val is_nat_trans_is_category = Q.store_thm(
"is_nat_trans_is_category",
`∀n. is_nat_trans n ⇒ is_category (ntdom n) ∧ is_category (ntcod n)`,
metis_tac [is_nat_trans_is_functor,is_functor_is_category])

val is_nat_trans_comp = Q.store_thm(
"is_nat_trans_comp",
`∀nm. composable_nts nm ⇒ is_nat_trans (nt_comp nm)`,
srw_tac [][nt_comp_def] >>
match_mp_tac is_nat_trans_mk_nt >>
srw_tac [][nat_trans_axioms_def]
>- fsrw_tac [][composable_nts_def,is_nat_trans_is_functor]
>- fsrw_tac [][composable_nts_def,is_nat_trans_is_functor]
>- (fsrw_tac [][composable_nts_def,is_nat_trans_def] >>
    metis_tac [nat_trans_axioms_def])
>- (fsrw_tac [][composable_nts_def,is_nat_trans_def] >>
    metis_tac [nat_trans_axioms_def])
>- (
  fsrw_tac [][composable_nts_def] >>
  `nt_maps_to (SND nm) (SND nm).dom (SND nm).cod`
    by srw_tac [][nt_maps_to_def] >>
  imp_res_tac nt_at_maps_to >>
  imp_res_tac is_nat_trans_is_category >>
  `category_axioms (SND nm).cod.cod` by fsrw_tac [][is_category_def] >>
  fsrw_tac [][category_axioms_def] >>
  first_assum match_mp_tac >>
  qexists_tac `objf (SND nm).cod x` >>
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
`∃n m. nm = (n,m)` by (Cases_on `nm` >> srw_tac [][]) >> fsrw_tac [][] >>
qabbrev_tac `c = n.cod.cod.comp` >>
qabbrev_tac `A = m.dom.morf` >>
qabbrev_tac `B = n.cod.morf` >>
imp_res_tac composable_nts_def >> fsrw_tac [][] >>
imp_res_tac is_nat_trans_is_category >>
`maps_to n.cod.cod (n.at y) (objf n.dom y) (objf n.cod y)` by (
  match_mp_tac nt_at_maps_to >>
  fsrw_tac [][nt_maps_to_def] >>
  imp_res_tac maps_to_obj ) >>
`maps_to m.cod.cod (m.at y) (objf m.dom y) (objf m.cod y)` by (
  match_mp_tac nt_at_maps_to >>
  fsrw_tac [][nt_maps_to_def] >>
  imp_res_tac maps_to_obj ) >>
`maps_to m.cod.cod (A f) (objf m.dom x) (objf m.dom y)` by (
  qunabbrev_tac `A` >>
  match_mp_tac morf_maps_to >>
  qexists_tac `m.dom.dom` >>
  imp_res_tac is_nat_trans_def >>
  fsrw_tac [][functor_maps_to_def,nat_trans_axioms_def] ) >>
`maps_to n.cod.cod (n.at x) (objf n.dom x) (objf n.cod x)` by (
  match_mp_tac nt_at_maps_to >>
  fsrw_tac [][nt_maps_to_def] >>
  imp_res_tac maps_to_obj ) >>
`maps_to m.cod.cod (m.at x) (objf m.dom x) (objf m.cod x)` by (
  match_mp_tac nt_at_maps_to >>
  fsrw_tac [][nt_maps_to_def] >>
  imp_res_tac maps_to_obj ) >>
`maps_to n.cod.cod (B f) (objf n.cod x) (objf n.cod y)` by (
  qunabbrev_tac `B` >>
  match_mp_tac morf_maps_to >>
  qexists_tac `n.dom.dom` >>
  imp_res_tac is_nat_trans_def >>
  fsrw_tac [][functor_maps_to_def,nat_trans_axioms_def] >>
  metis_tac [] ) >>
`composable m.cod.cod (n.at y,m.at y)` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >> metis_tac [] ) >>
`composable m.cod.cod (m.at y,A f)` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >> metis_tac [] ) >>
`composable m.cod.cod (n.at x,m.at x)` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >> metis_tac [] ) >>
`composable m.cod.cod (B f,n.at x)` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >> metis_tac [] ) >>
`maps_to m.cod.cod (m.cod.morf f) (objf m.cod x) (objf m.cod y)` by (
  match_mp_tac morf_maps_to >>
  qexists_tac `m.cod.dom` >>
  fsrw_tac [][functor_maps_to_def,is_nat_trans_def,nat_trans_axioms_def] ) >>
`composable m.cod.cod (m.cod.morf f, m.at x)` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >> metis_tac []) >>
`composable m.cod.cod (n.at y, n.dom.morf f)` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >> metis_tac []) >>
match_mp_tac EQ_TRANS >>
qexists_tac `c (n.at y, c (m.at y, A f))` >>
conj_tac >- (
  qunabbrev_tac `c` >> match_mp_tac (GSYM comp_assoc) >> srw_tac [][] ) >>
match_mp_tac EQ_TRANS >>
qexists_tac `c (n.at y, c (m.cod.morf f, m.at x))` >>
conj_tac >- (
  AP_TERM_TAC >> srw_tac [][] >>
  qunabbrev_tac `c` >> qunabbrev_tac `A` >>
  match_mp_tac naturality >> srw_tac [][] ) >>
match_mp_tac EQ_TRANS >>
qexists_tac `c (c (n.at y, n.dom.morf f), m.at x)` >>
conj_tac >- metis_tac [comp_assoc] >>
match_mp_tac EQ_TRANS >>
qexists_tac `c (c (B f, n.at x), m.at x)` >>
conj_tac >- (
  AP_TERM_TAC >> srw_tac [][] >>
  qunabbrev_tac `c` >> qunabbrev_tac `B` >>
  match_mp_tac naturality >> srw_tac [][nt_maps_to_def] ) >>
unabbrev_all_tac >>
match_mp_tac (GSYM comp_assoc) >>
srw_tac [][])

val functor_cat_def = Define`
  functor_cat (c1,c2) = mk_cat
    <| obj := {f | functor_maps_to f c1 c2};
       mor := {n | is_nat_trans n ∧ (ntdom n = c1) ∧ (ntcod n = c2)};
       dom := λn. n.dom;
       cod := λn. n.cod;
       id := id_nt;
       comp := nt_comp |>`

val id_nt_comp = Q.store_thm(
"id_nt_comp",
`∀f. is_nat_trans f ⇒
  (nt_comp (f, id_nt f.dom) = f) ∧
  (nt_comp (id_nt f.cod, f) = f)`,
srw_tac [][id_nt_def,nt_comp_def,mk_nt_def,nat_trans_component_equality] >- (
  srw_tac [][restrict_def,FUN_EQ_THM] >> srw_tac [][] >- (
    `f.dom.cod = f.cod.cod` by (
      fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
    srw_tac [][] >>
    match_mp_tac id_comp1 >>
    fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def,
                maps_to_def,is_functor_is_category] ) >>
  fsrw_tac [][is_nat_trans_def,extensional_nat_trans_def,extensional_def] ) >>
srw_tac [][restrict_def,FUN_EQ_THM] >> srw_tac [][] >- (
  match_mp_tac id_comp2 >>
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def,
              maps_to_def,is_functor_is_category] )
>- metis_tac [is_nat_trans_def,nat_trans_axioms_def] >>
fsrw_tac [][is_nat_trans_def,extensional_nat_trans_def,extensional_def])

val composable_nts_composable = Q.store_thm(
"composable_nts_composable",
`∀nm x. composable_nts nm ∧ x ∈ (ntdom (SND nm)).obj ⇒
   composable (ntcod (SND nm)) ((FST nm).at x, (SND nm).at x)`,
srw_tac [][] >>
match_mp_tac maps_to_composable >>
srw_tac [][] >>
imp_res_tac composable_nts_def >>
Q.ISPECL_THEN [`FST nm`,`(FST nm).dom`,`(FST nm).cod`,`x`]
  mp_tac nt_at_maps_to >>
Q.ISPECL_THEN [`SND nm`,`(SND nm).dom`,`(SND nm).cod`,`x`]
  mp_tac nt_at_maps_to >>
srw_tac [][] >> metis_tac [])

val nt_comp_assoc = Q.store_thm(
"nt_comp_assoc",
`∀f g h. composable_nts (g,f) ∧ composable_nts (h,g) ⇒
 (nt_comp (h, nt_comp (g,f)) = nt_comp (nt_comp (h,g), f))`,
srw_tac [][nt_comp_def,mk_nt_def,restrict_def,FUN_EQ_THM] >>
srw_tac [][] >- (
  imp_res_tac composable_nts_def >>
  fsrw_tac [][] >>
  match_mp_tac comp_assoc >>
  fsrw_tac [][is_nat_trans_is_category] >>
  metis_tac [SIMP_RULE (srw_ss()) [FORALL_PROD] composable_nts_composable] ) >>
fsrw_tac [][composable_nts_def] >> metis_tac [])

val is_category_functor_cat = Q.store_thm(
"is_category_functor_cat",
`∀c1 c2. is_category c1 ∧ is_category c2 ⇒
  is_category (functor_cat (c1,c2))`,
srw_tac [][functor_cat_def] >>
match_mp_tac is_category_mk_cat >>
srw_tac [][category_axioms_def]
>- fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def,functor_maps_to_def]
>- fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def,functor_maps_to_def]
>- (
  srw_tac [][maps_to_def] >-
    fsrw_tac [][functor_maps_to_def,is_nat_trans_id_nt] >>
  fsrw_tac [][functor_maps_to_def,id_nt_def,mk_nt_def] )
>- srw_tac [][id_nt_comp]
>- srw_tac [][id_nt_comp]
>- (
  match_mp_tac nt_comp_assoc >>
  fsrw_tac [][composable_def] >>
  srw_tac [][composable_nts_def] >>
  fsrw_tac [][] ) >>
fsrw_tac [][maps_to_def] >>
srw_tac [][] >- (
  match_mp_tac is_nat_trans_comp >>
  srw_tac [][composable_nts_def] >>
  fsrw_tac [][] ) >>
srw_tac [][nt_comp_def,mk_nt_def])

val functor_cat_dom = Q.store_thm(
"functor_cat_dom",
`∀cs f. f ∈ (functor_cat cs).mor ⇒ ((functor_cat cs).dom f = f.dom)`,
Cases >> srw_tac [][functor_cat_def])

val functor_cat_cod = Q.store_thm(
"functor_cat_cod",
`∀cs f. f ∈ (functor_cat cs).mor ⇒ ((functor_cat cs).cod f = f.cod)`,
Cases >> srw_tac [][functor_cat_def])

val functor_cat_id = Q.store_thm(
"functor_cat_id",
`∀cs x. x ∈ (functor_cat cs).obj ⇒ ((functor_cat cs).id x = id_nt x)`,
Cases >> srw_tac [][functor_cat_def])

val functor_cat_mor_is_nat_trans = Q.store_thm(
"functor_cat_mor_is_nat_trans",
`∀cs f. f ∈ (functor_cat cs).mor ⇒ is_nat_trans f`,
Cases >> srw_tac [][functor_cat_def])

val functor_cat_composable = Q.store_thm(
"functor_cat_composable",
`∀cs gf. composable (functor_cat cs) gf ⇒ composable_nts gf`,
Cases >> Cases >> srw_tac [][] >>
fsrw_tac [][composable_def] >>
imp_res_tac functor_cat_dom >>
imp_res_tac functor_cat_cod >>
imp_res_tac functor_cat_mor_is_nat_trans >>
fsrw_tac [][composable_nts_def] >>
fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def])

val functor_cat_comp = Q.store_thm(
"functor_cat_comp",
`∀cs gf x. composable (functor_cat cs) gf ∧ x ∈ (ntdom (SND gf)).obj
 ⇒ (((functor_cat cs).comp gf).at x = (nt_comp gf).at x)`,
Cases >> srw_tac [][functor_cat_def,mk_cat_def] >>
srw_tac [][restrict_def,IN_DEF] >>
qsuff_tac `F` >> srw_tac [][] >>
pop_assum mp_tac >> srw_tac [][] >>
fsrw_tac [][composable_def,composable_nts_def] >>
ntac 2 (pop_assum mp_tac) >>
srw_tac [][restrict_def])

val functor_cat_dist = Q.store_thm(
"functor_cat_dist",
`∀cs gf x. composable (functor_cat cs) gf ∧ x ∈ (FST cs).obj ⇒
   (((functor_cat cs).comp gf).at x =
    (SND cs).comp ((FST gf).at x, (SND gf).at x))`,
srw_tac [][] >>
imp_res_tac functor_cat_comp >>
match_mp_tac EQ_TRANS >>
qexists_tac `(nt_comp gf).at x` >>
`x ∈ (SND gf).dom.dom.obj` by (
  Cases_on `cs` >> fsrw_tac [][composable_def,functor_cat_def] ) >>
srw_tac [][nt_comp_def,mk_nt_def,restrict_def] >>
AP_THM_TAC >> AP_TERM_TAC >>
Cases_on `cs` >> fsrw_tac [][composable_def,functor_cat_def])

val _ = export_theory ()
