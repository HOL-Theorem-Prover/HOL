open HolKernel boolLib bossLib categoryTheory zfsetTheory lcsymtacs

val _ = new_theory "set_cat"

val explode_def = Define`
  explode s = {x | x In s}`

val IdFn_eq_GraphFnI = Q.store_thm(
"IdFn_eq_GraphFnI",
`IdFn x = GraphFn x I`,
match_mp_tac FnEqThm >>
map_every qexists_tac [`x`,`x`] >>
srw_tac [][IdFnType] >- (
  match_mp_tac GraphFnType >>
  srw_tac [][HasFnType_def] ) >>
srw_tac [][IdFnAp,GraphFnAp])

val GraphFnExt = Q.store_thm(
"GraphFnExt",
`∀X f Y g. (X = Y) ∧ (∀x. x In X ⇒ (f x = g x)) ⇒ (GraphFn X f = GraphFn Y g)`,
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Image g X`] >>
srw_tac [][GraphFnAp] >>
match_mp_tac GraphFnType >>
srw_tac [][HasFnType_def] >>
metis_tac [zfset_axiomsTheory.Image_def])

val ComposeGraphFns = Q.store_thm(
"ComposeGraphFns",
`∀X Y Z f g. HasFnType f X Y ∧ HasFnType g Y Z ⇒
  (ComposeFn (X,Y,Z) (GraphFn Y g) (GraphFn X f) = GraphFn X (g o f))`,
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Z`] >>
srw_tac [][GraphFnType,ComposeFnType,ApComposeFn,GraphFnAp] >- (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] ) >>
match_mp_tac GraphFnAp >>
fsrw_tac [][HasFnType_def])

val _ = Hol_datatype `TypedFn = <| dom : zfset ; cod : zfset ; map : zfset |>`
val TypedFn_component_equality = DB.theorem "TypedFn_component_equality"

val IsTypedFn_def = Define`
  IsTypedFn f = f.map In (f.dom -> f.cod)`

val ComposeTypedFn_def = Define`
  ComposeTypedFn gf = <| dom := (SND gf).dom ; cod := (FST gf).cod ;
                map := ComposeFn ((SND gf).dom,(SND gf).cod,(FST gf).cod)
                                 (FST gf).map (SND gf).map |>`

val TypedGraphFn_def = Define`
  TypedGraphFn (X,Y) f = <|
    dom := X; cod := Y; map := GraphFn X f |>`

val IsTypedFnTypedGraphFn = Q.store_thm(
"IsTypedFnTypedGraphFn",
`HasFnType f X Y ⇒ IsTypedFn (TypedGraphFn (X,Y) f)`,
srw_tac [][IsTypedFn_def,TypedGraphFn_def,GraphFnType])

val set_cat_def = Define`
  set_cat = mk_cat <|
    obj := UNIV ;
    mor := {f | IsTypedFn f} ;
    dom := λf. f.dom ;
    cod := λf. f.cod ;
    id  := λx. <| dom := x; cod := x; map := IdFn x |> ;
    comp := ComposeTypedFn |>`

val is_category_set_cat = Q.store_thm(
"is_category_set_cat",
`is_category set_cat`,
srw_tac [][set_cat_def] >>
match_mp_tac is_category_mk_cat >>
srw_tac [][category_axioms_def] >- (
  srw_tac [][maps_to_def,IsTypedFn_def,IdFnType] )
>- (
  srw_tac [][ComposeTypedFn_def,TypedFn_component_equality] >>
  fsrw_tac [][IsTypedFn_def,ComposeFnId1] )
>- (
  srw_tac [][ComposeTypedFn_def,TypedFn_component_equality] >>
  fsrw_tac [][IsTypedFn_def,ComposeFnId2] )
>- (
  srw_tac [][ComposeTypedFn_def,TypedFn_component_equality] >>
  fsrw_tac [][composable_def] >>
  match_mp_tac ComposeFnAssoc >>
  fsrw_tac [][IsTypedFn_def] ) >>
fsrw_tac [][maps_to_def] >>
fsrw_tac [][IsTypedFn_def] >>
srw_tac [][ComposeTypedFn_def] >>
srw_tac [][ComposeFnType])

val set_cat_obj = Q.store_thm(
"set_cat_obj",
`∀x. x ∈ set_cat.obj`,
srw_tac [][set_cat_def])
val _ = export_rewrites["set_cat_obj"]

val set_cat_dom = Q.store_thm(
"set_cat_dom",
`∀f. IsTypedFn f ⇒ (set_cat.dom f = f.dom)`,
srw_tac [][set_cat_def])

val set_cat_cod = Q.store_thm(
"set_cat_cod",
`∀f. IsTypedFn f ⇒ (set_cat.cod f = f.cod)`,
srw_tac [][set_cat_def])

val set_cat_mor = Q.store_thm(
"set_cat_mor",
`∀f. IsTypedFn f ⇒ f ∈ set_cat.mor`,
srw_tac [][set_cat_def])

val set_cat_id = Q.store_thm(
"set_cat_id",
`∀x e. e In x ⇒ ((set_cat.id x).map ' e = e)`,
srw_tac [][set_cat_def,IdFnAp])
val _ = export_rewrites["set_cat_dom","set_cat_cod","set_cat_mor","set_cat_id"]

val set_cat_maps_to = Q.store_thm(
"set_cat_maps_to",
`∀f g x y. (f = TypedGraphFn (x,y) g) ∧ HasFnType g x y ⇒ maps_to set_cat f x y`,
rpt strip_tac >>
`IsTypedFn f` by metis_tac [IsTypedFnTypedGraphFn] >>
srw_tac [][] >>
fsrw_tac [][maps_to_def,set_cat_mor,set_cat_dom,set_cat_cod] >>
srw_tac [][TypedGraphFn_def])

val set_cat_comp = Q.store_thm(
"set_cat_comp",
`∀gf. composable set_cat gf ⇒ (set_cat.comp gf = ComposeTypedFn gf)`,
srw_tac [][set_cat_def])
val _ = export_rewrites["set_cat_comp"]

val hom_def = Define`
  hom c (x,y) = {f | maps_to c f x y}`

val _ = Hol_datatype `lscat = <| mrep : 'b -> zfset; cat : ('a,'b) category |>`

val mabs_def = Define`
  mabs c z = @f. f ∈ c.cat.mor ∧ (c.mrep f = z)`

val is_lscat_def = Define`
  is_lscat r = is_category (r.cat:('a,'b) category) ∧
    extensional r.mrep r.cat.mor ∧
    (∀f g. f ∈ r.cat.mor ∧ g ∈ r.cat.mor ∧ (r.mrep f = r.mrep g) ⇒ (f = g)) ∧
    (∀x y. x ∈ r.cat.obj ∧ y ∈ r.cat.obj ⇒
             ∃s. IMAGE r.mrep (hom r.cat (x,y)) = (explode s))`

val is_lscat_is_category = Q.store_thm(
"is_lscat_is_category",
`∀c. is_lscat c ⇒ is_category c.cat`,
srw_tac [][is_lscat_def])

val implode_def = Define`
  implode s = @z. s = explode z`

val homset_def = Define`
  homset c (x,y) = implode (IMAGE c.mrep (hom c.cat (x,y)))`

val mrep_in_homset = Q.store_thm(
"mrep_in_homset",
`∀c f x y. is_lscat c ∧ maps_to c.cat f x y ⇒ c.mrep f In homset c (x,y)`,
srw_tac [][homset_def,hom_def,implode_def] >>
SELECT_ELIM_TAC >> srw_tac [][] >- (
  fsrw_tac [][is_lscat_def,hom_def] >>
  first_assum match_mp_tac >>
  imp_res_tac maps_to_obj >> srw_tac [][] ) >>
fsrw_tac [][explode_def,pred_setTheory.EXTENSION] >>
metis_tac [])

val In_homset_mrep = Q.store_thm(
"In_homset_mrep",
`∀c z x y. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj ∧ z In homset c (x,y) ⇒
  ∃f. maps_to c.cat f x y ∧ (z = c.mrep f)`,
srw_tac [][homset_def,implode_def] >>
pop_assum mp_tac >>
SELECT_ELIM_TAC >> srw_tac [][] >-
  fsrw_tac [][is_lscat_def] >>
fsrw_tac [][explode_def,pred_setTheory.EXTENSION,hom_def] >>
metis_tac [])

val mabs_mrep = Q.store_thm(
"mabs_mrep",
`∀c f. is_lscat c ∧ f ∈ c.cat.mor ⇒ (mabs c (c.mrep f) = f)`,
srw_tac [][mabs_def] >>
SELECT_ELIM_TAC >>
fsrw_tac [][is_lscat_def] >>
metis_tac [])

val mrep_mabs = Q.store_thm(
"mrep_mabs",
`∀c f x y. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj ∧
         f In homset c (x,y) ⇒ (c.mrep (mabs c f) = f)`,
srw_tac [][mabs_def,homset_def] >>
SELECT_ELIM_TAC >>
fsrw_tac [][is_lscat_def,implode_def] >>
pop_assum mp_tac >>
SELECT_ELIM_TAC >>
srw_tac [][explode_def,pred_setTheory.EXTENSION,hom_def,maps_to_def] >>
metis_tac [])

val In_homset_mabs = Q.store_thm(
"In_homset_mabs",
`∀c f x y. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj ∧ f In homset c (x,y)
  ⇒ maps_to c.cat (mabs c f) x y`,
srw_tac [][] >>
`∃g. maps_to c.cat g x y ∧ (f = c.mrep g)` by srw_tac [][In_homset_mrep] >>
srw_tac [][] >> fsrw_tac [][maps_to_def,mabs_mrep])

val pre_hom_functor_def = Define`
  pre_hom_functor c x = <|
    dom := c.cat ; cod := set_cat ;
    morf := λg. TypedGraphFn
                  (homset c (x,c.cat.dom g), homset c (x,c.cat.cod g))
                  (λf. c.mrep (c.cat.comp (g, mabs c f)))
  |>`

val pre_hom_functor_dom = Q.store_thm(
"pre_hom_functor_dom",
`∀c x. (pre_hom_functor c x).dom = c.cat`,
srw_tac [][pre_hom_functor_def])

val pre_hom_functor_cod = Q.store_thm(
"pre_hom_functor_cod",
`∀c x. (pre_hom_functor c x).cod = set_cat`,
srw_tac [][pre_hom_functor_def])

val _ = export_rewrites["pre_hom_functor_cod","pre_hom_functor_dom"]

val pre_hom_functor_morf_dom_cod = Q.store_thm(
"pre_hom_functor_morf_dom_cod",
`∀c x f. (((pre_hom_functor c x).morf f).dom = homset c (x,c.cat.dom f)) ∧
         (((pre_hom_functor c x).morf f).cod = homset c (x,c.cat.cod f))`,
srw_tac [][pre_hom_functor_def,TypedGraphFn_def])
val _ = export_rewrites ["pre_hom_functor_morf_dom_cod"]

val pre_hom_functor_objf = Q.store_thm(
"pre_hom_functor_objf",
`∀c x y. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj
  ⇒ (objf (pre_hom_functor c x) y = homset c (x,y))`,
srw_tac [][objf_def,pre_hom_functor_def] >>
imp_res_tac is_lscat_is_category >>
imp_res_tac id_dom_cod >>
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  qexists_tac `homset c (x,y)` >>
  assume_tac is_category_set_cat >>
  `homset c (x,y) ∈ set_cat.obj` by srw_tac [][set_cat_obj] >>
  imp_res_tac id_maps_to >>
  `IsTypedFn (set_cat.id (homset c (x,y)))` by (
    srw_tac [][IsTypedFn_def] >>
    srw_tac [][set_cat_def] >>
    srw_tac [][IdFnType] ) >>
  fsrw_tac [][maps_to_def,set_cat_dom,set_cat_cod] >>
  srw_tac [][TypedFn_component_equality,TypedGraphFn_def] >>
  srw_tac [][set_cat_def] >>
  srw_tac [][IdFn_eq_GraphFnI] >>
  match_mp_tac GraphFnExt >>
  srw_tac [][] >>
  qmatch_assum_rename_tac `f In homset c (x,y)` [] >>
  `maps_to c.cat (mabs c f) x y` by
    imp_res_tac In_homset_mabs >>
  `c.cat.comp (c.cat.id y, mabs c f) = mabs c f` by (
    match_mp_tac id_comp2 >>
    fsrw_tac [][maps_to_def] ) >>
  srw_tac [][] >>
  match_mp_tac mrep_mabs >>
  metis_tac [] ) >>
fsrw_tac [][TypedGraphFn_def,set_cat_def])

val hom_functor_def = Define`
  hom_functor c x = mk_functor (pre_hom_functor c x)`

val is_functor_hom_functor = Q.store_thm(
"is_functor_hom_functor",
`∀c x. is_lscat c ∧ x ∈ c.cat.obj ⇒ is_functor (hom_functor c x)`,
srw_tac [][hom_functor_def] >>
match_mp_tac is_functor_mk_functor >>
srw_tac [][functor_axioms_def]
>- fsrw_tac [][is_lscat_def]
>- srw_tac [][is_category_set_cat]
>- (
  srw_tac [][] >>
  match_mp_tac set_cat_maps_to >>
  qexists_tac `λg. c.mrep (c.cat.comp (f, mabs c g))` >>
  fsrw_tac [][pre_hom_functor_dom] >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  srw_tac [][pre_hom_functor_objf,pre_hom_functor_def] >-
    fsrw_tac [][maps_to_def] >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  metis_tac [In_homset_mabs] )
>- (
  fsrw_tac [][pre_hom_functor_def] >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac id_dom_cod >> srw_tac [][] >>
  qmatch_abbrev_tac `∃y. TypedGraphFn (s,s) f = set_cat.id y` >>
  qexists_tac `s` >>
  srw_tac [][set_cat_def,TypedGraphFn_def] >>
  match_mp_tac FnEqThm >>
  map_every qexists_tac [`s`,`s`] >>
  srw_tac [][IdFnType] >- (
    match_mp_tac GraphFnType >>
    srw_tac [][HasFnType_def] >>
    srw_tac [][Abbr`f`,Abbr`s`] >>
    match_mp_tac mrep_in_homset >>
    srw_tac [][] >>
    qmatch_rename_tac
      `maps_to c.cat (c.cat.comp (c.cat.id b, mabs c f)) a b` [] >>
    `maps_to c.cat (mabs c f) a b` by srw_tac [][In_homset_mabs] >>
    `c.cat.comp (c.cat.id b, mabs c f) = mabs c f` by (
      match_mp_tac id_comp2 >> fsrw_tac [][maps_to_def] ) >>
    srw_tac [][] ) >>
  srw_tac [][GraphFnAp,IdFnAp,Abbr`f`,Abbr`s`] >>
  qmatch_assum_rename_tac `f In homset c (a,b)` [] >>
  `maps_to c.cat (mabs c f) a b` by srw_tac [][In_homset_mabs] >>
  `c.cat.comp (c.cat.id b, mabs c f) = mabs c f` by (
    match_mp_tac id_comp2 >> fsrw_tac [][maps_to_def] ) >>
  metis_tac [mrep_mabs,maps_to_obj]) >>
qmatch_abbrev_tac `xx = set_cat.comp (b,a)` >>
`IsTypedFn a ∧ IsTypedFn b` by (
  srw_tac [][Abbr`a`,Abbr`b`,pre_hom_functor_def] >> (
  match_mp_tac IsTypedFnTypedGraphFn >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  imp_res_tac is_lscat_is_category >>
  qmatch_assum_rename_tac `zf In homset c (x,c.cat.dom tf)` [] >>
  qexists_tac `c.cat.dom tf` >>
  reverse (srw_tac [][]) >- fsrw_tac [][composable_def,maps_to_def] >>
  match_mp_tac In_homset_mabs >>
  srw_tac [][] >>
  imp_res_tac composable_obj)) >>
`composable set_cat (b,a)` by (
  fsrw_tac [][Abbr`a`,Abbr`b`,composable_def] ) >>
srw_tac [][Abbr`xx`,pre_hom_functor_def] >>
imp_res_tac is_lscat_is_category >>
srw_tac [][Abbr`a`,Abbr`b`,comp_mor_dom_cod,
           TypedGraphFn_def,ComposeTypedFn_def] >>
srw_tac [][pre_hom_functor_def,TypedGraphFn_def] >>
qmatch_abbrev_tac `GraphFn X gof = ComposeFn (X,Y,Z) (GraphFn YY gg) (GraphFn X ff)` >>
`YY = Y` by fsrw_tac [][Abbr`Y`,Abbr`YY`,composable_def] >>
`ComposeFn (X,Y,Z) (GraphFn Y gg) (GraphFn X ff) = GraphFn X (gg o ff)` by (
  match_mp_tac ComposeGraphFns >>
  unabbrev_all_tac >>
  srw_tac [][HasFnType_def] >|[
    ALL_TAC, qpat_assum `X=Y` (assume_tac o SYM)] >>
  fsrw_tac [][] >> (
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  imp_res_tac is_lscat_is_category >>
  qmatch_assum_rename_tac `zf In homset c (x,c.cat.dom tf)` [] >>
  qexists_tac `c.cat.dom tf` >>
  reverse (srw_tac [][]) >- fsrw_tac [][composable_def,maps_to_def] >>
  match_mp_tac In_homset_mabs >>
  srw_tac [][] >>
  imp_res_tac composable_obj)) >>
srw_tac [][] >>
match_mp_tac GraphFnExt >>
srw_tac [][Abbr`gof`,Abbr`gg`,Abbr`ff`] >>
AP_TERM_TAC >>
qmatch_assum_rename_tac `e In X` [] >>
`composable c.cat (f, mabs c e)` by (
  match_mp_tac maps_to_composable >>
  srw_tac [][] >>
  map_every qexists_tac [`x`,`c.cat.dom f`,`c.cat.cod f`] >>
  srw_tac [][] >- (
    imp_res_tac composable_obj >>
    metis_tac [In_homset_mabs] ) >>
  fsrw_tac [][composable_def,maps_to_def] ) >>
imp_res_tac composable_maps_to >>
fsrw_tac [][maps_to_def,mabs_mrep] >>
match_mp_tac (GSYM comp_assoc) >>
srw_tac [][])

val hom_op_cat = Q.store_thm(
"hom_op_cat",
`∀c x y. hom (op_cat c) (x,y) = hom c (y,x)`,
srw_tac [][hom_def,pred_setTheory.EXTENSION] >>
metis_tac [op_cat_maps_to,op_cat_idem])
val _ = export_rewrites["hom_op_cat"]

val op_lscat_def = Define`
  op_lscat c = <| cat := op_cat c.cat; mrep := c.mrep |>`

val op_lscat_cat = Q.store_thm(
"op_lscat_cat",
`(op_lscat c).cat = op_cat c.cat`,
srw_tac [][op_lscat_def])
val _ = export_rewrites ["op_lscat_cat"]

val op_lscat_mrep = Q.store_thm(
"op_lscat_mrep",
`(op_lscat c).mrep = c.mrep`,
srw_tac [][op_lscat_def])
val _ = export_rewrites["op_lscat_mrep"]

val op_lscat_mabs = Q.store_thm(
"op_lscat_mabs",
`∀c f. mabs (op_lscat c) f = mabs c f`,
srw_tac [][mabs_def])
val _ = export_rewrites["op_lscat_mabs"]

val is_lscat_op = Q.store_thm(
"is_lscat_op",
`∀c. is_lscat c ⇒ is_lscat (op_lscat c)`,
srw_tac [][op_lscat_def,is_lscat_def])

val hom_functor_objf = Q.store_thm(
"hom_functor_objf",
`∀c x y. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj
  ⇒ (objf (hom_functor c x) y = homset c (x,y))`,
srw_tac [][hom_functor_def] >>
imp_res_tac is_lscat_is_category >>
srw_tac [][pre_hom_functor_objf])

val contra_hom_functor_objf = Q.store_thm(
"contra_hom_functor_objf",
`∀c x y. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj ⇒
  (objf (hom_functor (op_lscat c) x) y = homset c (y,x))`,
srw_tac [][] >>
`x ∈ (op_lscat c).cat.obj ∧ y ∈ (op_lscat c).cat.obj` by
  srw_tac [][op_lscat_def] >>
srw_tac [][is_lscat_op,hom_functor_objf] >>
srw_tac [][homset_def,op_lscat_def])

val hom_functor_morf = Q.store_thm(
"hom_functor_morf",
`∀c x f. f ∈ c.cat.mor ⇒
((hom_functor c x).morf f =
  TypedGraphFn (homset c (x,c.cat.dom f),homset c (x,c.cat.cod f))
    (λg. c.mrep (c.cat.comp (f, mabs c g))))`,
srw_tac [][hom_functor_def,pre_hom_functor_def,mk_functor_def,restrict_def])

val homset_op_lscat = Q.store_thm(
"homset_op_lscat",
`∀c x y. homset (op_lscat c) (x,y) = homset c (y,x)`,
srw_tac [][homset_def])
val _ = export_rewrites["homset_op_lscat"]

val contra_hom_functor_morf = Q.store_thm(
"contra_hom_functor_morf",
`∀c x f. is_lscat c ∧ f ∈ c.cat.mor ⇒
  ((hom_functor (op_lscat c) x).morf f =
   TypedGraphFn (homset c (c.cat.cod f,x),homset c (c.cat.dom f,x))
     (λg. c.mrep (c.cat.comp (mabs c g, f))))`,
srw_tac [][hom_functor_def,pre_hom_functor_def,mk_functor_def,restrict_def])

val _ = export_theory ()
