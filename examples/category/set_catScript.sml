open HolKernel boolLib bossLib categoryTheory zfsetTheory lcsymtacs

val _ = new_theory "set_cat"

val explode_def = Define`
  explode s = {x | x In s}`

val IdFn_eq_GraphFnI = Q.store_thm(
"IdFn_eq_GraphFnI",
`∀x. IdFn x = GraphFn x I`,
srw_tac [][] >> match_mp_tac FnEqThm >>
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
`∀f X Y. HasFnType f X Y ⇒ IsTypedFn (TypedGraphFn (X,Y) f)`,
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

val maps_to_set_cat = Q.store_thm(
"maps_to_set_cat",
`∀f x y. maps_to set_cat f x y ⇒ f.map In (x -> y)`,
srw_tac [][maps_to_def] >>
`IsTypedFn f` by fsrw_tac [][set_cat_def] >>
srw_tac [][] >> fsrw_tac [][IsTypedFn_def])

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
`∀c. (op_lscat c).cat = op_cat c.cat`,
srw_tac [][op_lscat_def])
val _ = export_rewrites ["op_lscat_cat"]

val op_lscat_mrep = Q.store_thm(
"op_lscat_mrep",
`∀c. (op_lscat c).mrep = c.mrep`,
srw_tac [][op_lscat_def])
val _ = export_rewrites["op_lscat_mrep"]

val op_lscat_mabs = Q.store_thm(
"op_lscat_mabs",
`∀c f. mabs (op_lscat c) f = mabs c f`,
srw_tac [][mabs_def])
val _ = export_rewrites["op_lscat_mabs"]

val is_lscat_op_cat = Q.store_thm(
"is_lscat_op_cat",
`∀c. is_lscat c ⇒ is_lscat (op_lscat c)`,
srw_tac [][op_lscat_def,is_lscat_def])
val _ = export_rewrites ["is_lscat_op_cat"]

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
srw_tac [][hom_functor_objf] >>
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

val hom_functor_dom = Q.store_thm(
"hom_functor_dom",
`∀c x. (hom_functor c x).dom = c.cat`,
srw_tac [][hom_functor_def])

val hom_functor_cod = Q.store_thm(
"hom_functor_cod",
`∀c x. (hom_functor c x).cod = set_cat`,
srw_tac [][hom_functor_def])

val _ = export_rewrites["hom_functor_cod","hom_functor_dom"]

val YfunctorNT_def = Define`
  YfunctorNT c f = mk_nt <|
    dom := hom_functor (op_lscat c) (c.cat.dom f);
    cod := hom_functor (op_lscat c) (c.cat.cod f);
    at := λx. (hom_functor c x).morf f |>`

val ntdom_YfunctorNT = Q.store_thm(
"ntdom_YfunctorNT",
`∀c f. ntdom (YfunctorNT c f) = op_cat c.cat`,
srw_tac [][YfunctorNT_def,mk_nt_def])

val ntcod_YfunctorNT = Q.store_thm(
"ntcod_YfunctorNT",
`∀c f. ntcod (YfunctorNT c f) = set_cat`,
srw_tac [][YfunctorNT_def,mk_nt_def])

val YfunctorNT_at = Q.store_thm(
"YfunctorNT_at",
`∀c f x. x ∈ c.cat.obj ⇒
  ((YfunctorNT c f).at x = (hom_functor c x).morf f)`,
srw_tac [][YfunctorNT_def,mk_nt_def,restrict_def])

val _ = export_rewrites ["ntdom_YfunctorNT","ntcod_YfunctorNT","YfunctorNT_at"]

val is_nat_trans_YfunctorNT = Q.store_thm(
"is_nat_trans_YfunctorNT",
`∀c f. is_lscat c ∧ f ∈ c.cat.mor ⇒ is_nat_trans (YfunctorNT c f)`,
srw_tac [][YfunctorNT_def] >>
match_mp_tac is_nat_trans_mk_nt >>
imp_res_tac is_lscat_is_category >>
srw_tac [][nat_trans_axioms_def]
>- srw_tac [][is_functor_hom_functor,mor_obj]
>- srw_tac [][is_functor_hom_functor,mor_obj]
>- (
  imp_res_tac mor_obj >>
  srw_tac [][contra_hom_functor_morf,contra_hom_functor_objf] >>
  srw_tac [][hom_functor_morf] >>
  match_mp_tac set_cat_maps_to >>
  srw_tac [][TypedGraphFn_def] >>
  qexists_tac `λg. c.mrep (c.cat.comp (f, mabs c g))` >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  metis_tac [In_homset_mabs,maps_to_def] ) >>
qmatch_assum_rename_tac `maps_to (op_cat c.cat) g x y` [] >>
imp_res_tac maps_to_def >>
fsrw_tac [][] >> srw_tac [][] >>
srw_tac [][contra_hom_functor_morf,hom_functor_morf] >>
qmatch_abbrev_tac
  `set_cat.comp (TypedGraphFn (t2,t3) f2, TypedGraphFn (t1,t2) f1) =
   set_cat.comp (TypedGraphFn (t4,t3) f1, TypedGraphFn (t1,t4) f2)` >>
`HasFnType f1 t1 t2 ∧
 HasFnType f1 t4 t3 ∧
 HasFnType f2 t2 t3 ∧
 HasFnType f2 t1 t4` by (
  unabbrev_all_tac >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  metis_tac [In_homset_mabs,maps_to_obj,maps_to_def,
             op_cat_obj,is_category_op_cat] ) >>
qmatch_abbrev_tac `set_cat.comp (x,w) = set_cat.comp (v,u)` >>
`IsTypedFn u ∧ IsTypedFn v ∧ IsTypedFn w ∧ IsTypedFn x` by
  metis_tac [IsTypedFnTypedGraphFn] >>
`u ∈ set_cat.mor ∧ v ∈ set_cat.mor ∧ w ∈ set_cat.mor ∧ x ∈ set_cat.mor` by
  metis_tac [set_cat_mor] >>
`composable set_cat (v,u)` by (
  srw_tac [][composable_def,Abbr`v`,Abbr`u`] >>
  fsrw_tac [][TypedGraphFn_def,maps_to_def] ) >>
`composable set_cat (x,w)` by (
  srw_tac [][composable_def,Abbr`x`,Abbr`w`] >>
  fsrw_tac [][maps_to_def,TypedGraphFn_def] ) >>
srw_tac [][] >>
map_every qunabbrev_tac [`u`,`v`,`w`,`x`] >>
srw_tac [][ComposeTypedFn_def,TypedGraphFn_def] >>
srw_tac [][ComposeGraphFns] >>
match_mp_tac GraphFnExt >>
srw_tac [][Abbr`t1`,Abbr`f1`,Abbr`f2`] >>
`maps_to c.cat (mabs c x) (c.cat.cod g) (c.cat.dom f)` by (
  match_mp_tac In_homset_mabs >>
  metis_tac [maps_to_obj,op_cat_obj,is_category_op_cat] ) >>
`composable c.cat (mabs c x, g) ∧ composable c.cat (f, mabs c x)` by (
   fsrw_tac [][composable_def,maps_to_def] ) >>
qspecl_then [`c.cat`,`(mabs c x, g)`] mp_tac composable_maps_to >>
qspecl_then [`c.cat`,`(f, mabs c x)`] mp_tac composable_maps_to >>
srw_tac [][] >>
fsrw_tac [][mabs_mrep,maps_to_def] >>
AP_TERM_TAC >>
match_mp_tac comp_assoc >>
srw_tac [][])

val YfunctorNT_mor = Q.store_thm(
"YfunctorNT_mor",
`∀c f. is_lscat c ∧ f ∈ c.cat.mor ⇒
  (YfunctorNT c f) ∈ (functor_cat (op_cat c.cat, set_cat)).mor`,
srw_tac [][functor_cat_def,is_nat_trans_YfunctorNT])

val YfunctorNT_maps_to = Q.store_thm(
"YfunctorNT_maps_to",
`∀c f. is_lscat c ∧ f ∈ c.cat.mor ⇒
  maps_to (functor_cat (op_cat c.cat, set_cat))
    (YfunctorNT c f)
    (hom_functor (op_lscat c) (c.cat.dom f))
    (hom_functor (op_lscat c) (c.cat.cod f))`,
srw_tac [][maps_to_def,YfunctorNT_mor,functor_cat_dom,functor_cat_cod] >>
srw_tac [][YfunctorNT_def,mk_nt_def])

val YfunctorNT_composable = Q.store_thm(
"YfunctorNT_composable",
`∀c f g. is_lscat c ∧ composable c.cat (g,f) ⇒
  composable (functor_cat (op_cat c.cat, set_cat))
    (YfunctorNT c g, YfunctorNT c f)`,
srw_tac [][YfunctorNT_mor,composable_def,functor_cat_dom,functor_cat_cod] >>
srw_tac [][YfunctorNT_def,mk_nt_def])

val is_category_presheaf_cat = Q.store_thm(
"is_category_presheaf_cat",
`∀c. is_lscat c ⇒ is_category (functor_cat (op_cat c.cat, set_cat))`,
metis_tac [is_category_functor_cat,is_category_set_cat,
           is_category_op_cat,is_lscat_is_category])

val pre_Yfunctor_def = Define`
  pre_Yfunctor c = <|
    dom := c.cat; cod := functor_cat (op_cat c.cat, set_cat);
    morf := λf. YfunctorNT c f |>`

val pre_Yfunctor_objf = Q.store_thm(
"pre_Yfunctor_objf",
`∀c x. is_lscat c ∧ x ∈ c.cat.obj
⇒ (objf (pre_Yfunctor c) x = hom_functor (op_lscat c) x)`,
srw_tac [][objf_def,pre_Yfunctor_def,functor_cat_obj] >>
SELECT_ELIM_TAC >> srw_tac [][] >- (
  qexists_tac `hom_functor (op_lscat c) x` >>
  srw_tac [][functor_maps_to_def,is_functor_hom_functor] >>
  `(hom_functor (op_lscat c) x) ∈
    (functor_cat (op_cat c.cat, set_cat)).obj` by (
    srw_tac [][functor_cat_obj,functor_maps_to_def,
               is_functor_hom_functor] ) >>
  srw_tac [][functor_cat_id] >>
  match_mp_tac nt_eq_thm >>
  srw_tac [][]
  >- srw_tac [][is_nat_trans_YfunctorNT,is_lscat_is_category,id_mor]
  >- srw_tac [][is_nat_trans_id_nt,is_functor_hom_functor]
  >- srw_tac [][YfunctorNT_def,mk_nt_def,id_nt_def,
                is_lscat_is_category,id_dom_cod]
  >- srw_tac [][YfunctorNT_def,mk_nt_def,id_nt_def,
                is_lscat_is_category,id_dom_cod] >>
  srw_tac [][id_nt_at] >>
  imp_res_tac is_lscat_is_category >>
  `c.cat.id x ∈ c.cat.mor` by imp_res_tac id_mor >>
  srw_tac [][hom_functor_morf] >>
  `(c.cat.dom (c.cat.id x) = x) ∧ (c.cat.cod (c.cat.id x) = x)` by
    metis_tac [id_dom_cod] >>
  srw_tac [][TypedGraphFn_def,set_cat_def,hom_functor_objf,IdFn_eq_GraphFnI] >>
  match_mp_tac GraphFnExt >> srw_tac [][] >>
  metis_tac [maps_to_def,id_comp2,maps_to_obj,mrep_mabs,In_homset_mabs]) >>
fsrw_tac [][functor_maps_to_def] >>
match_mp_tac functor_eq_thm >>
srw_tac [][is_functor_hom_functor] >>
qmatch_assum_rename_tac `is_functor z` [] >>
`(functor_cat (op_cat c.cat,set_cat)).id z = id_nt z` by (
  match_mp_tac functor_cat_id >>
  srw_tac [][functor_cat_obj] >>
  srw_tac [][functor_maps_to_def] ) >>
srw_tac [][hom_functor_morf] >>
fsrw_tac [][nat_trans_component_equality] >>
fsrw_tac [][id_nt_def,mk_nt_def] >>
srw_tac [][YfunctorNT_def,mk_nt_def] >>
srw_tac [][hom_functor_morf] >>
srw_tac [][is_lscat_is_category,id_dom_cod])

val pre_Yfunctor_dom = Q.store_thm(
"pre_Yfunctor_dom",
`∀c. (pre_Yfunctor c).dom = c.cat`,
srw_tac [][pre_Yfunctor_def])

val pre_Yfunctor_cod = Q.store_thm(
"pre_Yfunctor_cod",
`∀c. (pre_Yfunctor c).cod = functor_cat (op_cat c.cat, set_cat)`,
srw_tac [][pre_Yfunctor_def])

val _ = export_rewrites["pre_Yfunctor_dom","pre_Yfunctor_cod","pre_Yfunctor_objf"]

val Yfunctor_def = Define`
  Yfunctor c = mk_functor (pre_Yfunctor c)`

val is_functor_Yfunctor = Q.store_thm(
"is_functor_Yfunctor",
`∀c. is_lscat c ⇒ is_functor (Yfunctor c)`,
srw_tac [][Yfunctor_def] >>
match_mp_tac is_functor_mk_functor >>
srw_tac [][functor_axioms_def]
>- srw_tac [][is_lscat_is_category,pre_Yfunctor_def]
>- srw_tac [][is_category_presheaf_cat,pre_Yfunctor_def]
>- (
  `(pre_Yfunctor c).dom = c.cat` by srw_tac [][pre_Yfunctor_def] >>
  imp_res_tac is_lscat_is_category >>
  fsrw_tac [][] >>
  imp_res_tac maps_to_obj >>
  srw_tac [][pre_Yfunctor_objf] >>
  srw_tac [][pre_Yfunctor_def] >>
  fsrw_tac [][maps_to_def] >>
  conj_asm1_tac >- srw_tac [][YfunctorNT_mor] >>
  srw_tac [][functor_cat_dom,functor_cat_cod] >>
  srw_tac [][YfunctorNT_def,mk_nt_def] )
>- (
  fsrw_tac [][pre_Yfunctor_def] >>
  qexists_tac `hom_functor (op_lscat c) x` >>
  conj_asm1_tac >- (
    srw_tac [][functor_cat_obj] >>
    srw_tac [][functor_maps_to_def,is_functor_hom_functor] ) >>
  srw_tac [][functor_cat_id] >>
  match_mp_tac nt_eq_thm >>
  imp_res_tac is_lscat_is_category >>
  `c.cat.id x ∈ c.cat.mor` by imp_res_tac id_mor >>
  `is_functor (hom_functor (op_lscat c) x)` by
    srw_tac [][is_functor_hom_functor] >>
  imp_res_tac YfunctorNT_maps_to >>
  fsrw_tac [][maps_to_def,is_nat_trans_YfunctorNT,is_nat_trans_id_nt] >>
  imp_res_tac id_dom_cod >>
  srw_tac [][YfunctorNT_def] >>
  srw_tac [][id_nt_at] >>
  srw_tac [][hom_functor_objf] >>
  srw_tac [][hom_functor_morf] >>
  srw_tac [][TypedGraphFn_def,set_cat_def,IdFn_eq_GraphFnI] >>
  match_mp_tac GraphFnExt >> srw_tac [][] >>
  metis_tac [maps_to_def,id_comp2,maps_to_obj,mrep_mabs,In_homset_mabs]) >>
fsrw_tac [][pre_Yfunctor_def] >>
imp_res_tac YfunctorNT_composable >>
match_mp_tac nt_eq_thm >> srw_tac [][]
>- metis_tac [is_nat_trans_YfunctorNT,composable_maps_to,
              maps_to_def,is_lscat_is_category]
>- metis_tac [functor_cat_comp,is_nat_trans_nt_comp,
              functor_cat_composable]
>- (
  srw_tac [][Once YfunctorNT_def,SimpLHS] >>
  srw_tac [][functor_cat_comp] >>
  srw_tac [][nt_comp_def,YfunctorNT_def] >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac comp_mor_dom_cod >>
  fsrw_tac [][] )
>- (
  srw_tac [][Once YfunctorNT_def,SimpLHS] >>
  srw_tac [][functor_cat_comp] >>
  srw_tac [][nt_comp_def,YfunctorNT_def] >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac comp_mor_dom_cod >>
  fsrw_tac [][] ) >>
srw_tac [][functor_cat_comp] >>
srw_tac [][nt_comp1] >>
`f ∈ c.cat.mor ∧ g ∈ c.cat.mor` by fsrw_tac [][composable_def] >>
imp_res_tac hom_functor_morf >>
rpt (pop_assum (qspec_then `x` mp_tac)) >>
srw_tac [][] >>
qmatch_abbrev_tac
  `h = set_cat.comp (TypedGraphFn (i,j) k, TypedGraphFn (l,m) n)` >>
`HasFnType k i j ∧ HasFnType n l m` by (
  unabbrev_all_tac >>
  srw_tac [][HasFnType_def] >>
  metis_tac [mrep_in_homset,maps_to_comp,is_lscat_is_category,
             mor_obj,In_homset_mabs,maps_to_def] ) >>
imp_res_tac IsTypedFnTypedGraphFn >>
imp_res_tac set_cat_mor >>
`composable set_cat (TypedGraphFn (i,j) k, TypedGraphFn (l,m) n)` by (
  srw_tac [][composable_def] >>
  srw_tac [][TypedGraphFn_def] >>
  fsrw_tac [][composable_def,Abbr`m`,Abbr`i`] ) >>
`c.cat.comp (g,f) ∈ c.cat.mor ∧
(c.cat.dom (c.cat.comp (g,f)) = c.cat.dom (SND (g,f))) ∧
(c.cat.cod (c.cat.comp (g,f)) = c.cat.cod (FST (g,f)))` by
  metis_tac [is_lscat_is_category,comp_mor_dom_cod] >>
srw_tac [][Abbr`h`,hom_functor_morf] >>
srw_tac [][TypedGraphFn_def,ComposeTypedFn_def] >>
`m = i` by (
  fsrw_tac [][composable_def,Abbr`m`,Abbr`i`] ) >>
srw_tac [][ComposeGraphFns] >>
match_mp_tac GraphFnExt >>
srw_tac [][] >>
unabbrev_all_tac >>
fsrw_tac [][] >>
AP_TERM_TAC >>
qmatch_assum_rename_tac `e In X` ["X"] >>
`composable c.cat (f, mabs c e)` by (
  match_mp_tac maps_to_composable >>
  srw_tac [][] >>
  map_every qexists_tac [`x`,`c.cat.dom f`,`c.cat.cod f`] >>
  srw_tac [][] >-
    metis_tac [is_lscat_is_category,composable_obj,In_homset_mabs] >>
  fsrw_tac [][composable_def,maps_to_def] ) >>
imp_res_tac is_lscat_is_category >>
imp_res_tac composable_maps_to >>
fsrw_tac [][maps_to_def,mabs_mrep] >>
match_mp_tac (GSYM comp_assoc) >> srw_tac [][])

val Yfunctor_dom = Q.store_thm(
"Yfunctor_dom",
`∀c. (Yfunctor c).dom = c.cat`,
srw_tac [][Yfunctor_def])

val Yfunctor_cod = Q.store_thm(
"Yfunctor_cod",
`∀c. (Yfunctor c).cod = functor_cat (op_cat c.cat, set_cat)`,
srw_tac [][Yfunctor_def])

val Yfunctor_objf = Q.store_thm(
"Yfunctor_objf",
`∀c x. is_lscat c ∧ x ∈ c.cat.obj ⇒
 (objf (Yfunctor c) x = hom_functor (op_lscat c) x)`,
srw_tac [][Yfunctor_def,mk_functor_objf,is_lscat_is_category])

val Yfunctor_morf = Q.store_thm(
"Yfunctor_morf",
`∀c f. is_lscat c ∧ f ∈ c.cat.mor ⇒
  ((Yfunctor c).morf f = YfunctorNT c f)`,
srw_tac [][Yfunctor_def,pre_Yfunctor_def])

val _ = export_rewrites["Yfunctor_dom","Yfunctor_cod","Yfunctor_objf","Yfunctor_morf"]

val YMap_def = Define`
  YMap c x n = (n.at x).map ' (c.mrep (c.cat.id x))`

val YMapInv_def = Define`
  YMapInv c x f y = mk_nt <|
    dom := objf (Yfunctor c) x;
    cod := f;
    at := λz. TypedGraphFn (homset c (z,x), objf f z)
               (λg. (f.morf (mabs c g)).map ' y) |>`

val YMapInv_at = Q.store_thm(
"YMapInv_at",
`∀c x f y z. is_lscat c ∧ x ∈ c.cat.obj ∧ z ∈ c.cat.obj ⇒
    ((YMapInv c x f y).at z =
     TypedGraphFn (homset c (z,x), objf f z)
       (λg. (f.morf (mabs c g)).map ' y))`,
srw_tac [][YMapInv_def,mk_nt_def,restrict_def])

val YMapImage = Q.store_thm(
"YMapImage",
`∀c x n f. is_lscat c ∧ functor_maps_to f (op_cat c.cat) set_cat ∧
           x ∈ c.cat.obj ∧ nt_maps_to n (objf (Yfunctor c) x) f ⇒
             (YMap c x n) In (objf f x)`,
srw_tac [][YMap_def] >>
pop_assum mp_tac >> srw_tac [][nt_maps_to_def] >>
`maps_to n.dom.cod (n.at x) (objf n.dom x) (objf n.cod x)` by
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
pop_assum mp_tac >> srw_tac [][hom_functor_cod] >>
fsrw_tac [][maps_to_def] >>
`IsTypedFn (n.at x)` by fsrw_tac [][set_cat_def] >>
fsrw_tac [][] >>
ntac 3 (pop_assum mp_tac) >> srw_tac [][hom_functor_objf] >>
fsrw_tac [][IsTypedFn_def] >>
match_mp_tac InFn >>
pop_assum mp_tac >> srw_tac [][] >>
qexists_tac `homset c (x,x)` >>
srw_tac [][] >>
match_mp_tac mrep_in_homset >>
fsrw_tac [][id_maps_to,is_lscat_is_category])

val is_nat_trans_YMapInv = Q.store_thm(
"is_nat_trans_YMapInv",
`∀c x f y. is_lscat c ∧ functor_maps_to f (op_cat c.cat) set_cat ∧
           x ∈ c.cat.obj ∧ y In (objf f x)
 ⇒ is_nat_trans (YMapInv c x f y)`,
srw_tac [][YMapInv_def] >>
match_mp_tac is_nat_trans_mk_nt >>
srw_tac [][nat_trans_axioms_def]
>- srw_tac [][is_functor_hom_functor]
>- fsrw_tac [][functor_maps_to_def]
>- fsrw_tac [][functor_maps_to_def]
>- fsrw_tac [][functor_maps_to_def]
>- (
  fsrw_tac [][functor_maps_to_def,hom_functor_objf] >>
  match_mp_tac set_cat_maps_to >>
  qexists_tac `λg. (f.morf (mabs c g)).map ' y` >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac InFn >>
  qexists_tac `objf f x` >>
  qmatch_assum_rename_tac `g In homset c (u,x)` [] >>
  `maps_to c.cat (mabs c g) u x` by imp_res_tac In_homset_mabs >>
  imp_res_tac op_cat_maps_to >>
  `maps_to set_cat (f.morf (mabs c g)) (objf f x) (objf f u)` by
    metis_tac [is_functor_def,functor_axioms_def] >>
  `IsTypedFn (f.morf (mabs c g))` by
    fsrw_tac [][maps_to_def,set_cat_def] >>
  fsrw_tac [][maps_to_def] >>
  metis_tac [IsTypedFn_def] ) >>
qmatch_assum_rename_tac `maps_to (op_cat c.cat) g u v` [] >>
`g ∈ (op_lscat c).cat.mor` by fsrw_tac [][maps_to_def] >>
srw_tac [][hom_functor_morf] >>
fsrw_tac [][functor_maps_to_def] >>
`(u = c.cat.cod g) ∧ (v = c.cat.dom g)` by fsrw_tac [][maps_to_def] >>
srw_tac [][] >>
qmatch_abbrev_tac
`set_cat.comp (TypedGraphFn (i,j) k, TypedGraphFn (l,i) n) =
 set_cat.comp (q, TypedGraphFn (l,s) k)` >>
`HasFnType k i j ∧ HasFnType k l s` by (
 unabbrev_all_tac >> srw_tac [][HasFnType_def] >>
 match_mp_tac InFn >>
 qexists_tac `objf f x` >>
 qmatch_assum_abbrev_tac `z In homset c (q,x)`  >>
 `maps_to c.cat (mabs c z) q x` by
   metis_tac [In_homset_mabs,maps_to_obj,op_cat_obj,
              is_lscat_is_category,is_category_op_cat] >>
  imp_res_tac op_cat_maps_to >>
  `maps_to set_cat (f.morf (mabs c z)) (objf f x) (objf f q)` by
    metis_tac [is_functor_def,functor_axioms_def] >>
  `IsTypedFn (f.morf (mabs c z))` by
    fsrw_tac [][maps_to_def,set_cat_def] >>
  fsrw_tac [][maps_to_def] >>
  metis_tac [IsTypedFn_def] ) >>
`HasFnType n l i` by (
  srw_tac [][HasFnType_def,Abbr`n`,Abbr`i`,Abbr`l`] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `c.cat.cod g` >>
  imp_res_tac is_lscat_is_category >>
  conj_tac >- srw_tac [][] >>
  conj_asm1_tac >- srw_tac [][maps_to_def] >>
  imp_res_tac maps_to_obj >>
  imp_res_tac maps_to_def >>
  metis_tac [In_homset_mabs] ) >>
`maps_to set_cat q s j` by
  metis_tac [is_functor_def,functor_axioms_def] >>
`q ∈ set_cat.mor` by fsrw_tac [][maps_to_def] >>
`IsTypedFn q` by fsrw_tac [][set_cat_def] >>
`(q.dom = s) ∧ (q.cod = j)` by fsrw_tac [][maps_to_def] >>
srw_tac [][] >>
imp_res_tac IsTypedFnTypedGraphFn >>
`composable set_cat (TypedGraphFn (i,q.cod) k, TypedGraphFn (l,i) n) ∧
 composable set_cat (q,TypedGraphFn (l,q.dom) k)` by (
   srw_tac [][composable_def] >> srw_tac [][TypedGraphFn_def] ) >>
srw_tac [][] >>
srw_tac [][ComposeTypedFn_def] >>
srw_tac [][TypedGraphFn_def] >>
srw_tac [][ComposeGraphFns] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`l`,`q.cod`] >>
conj_tac >- (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] ) >>
`GraphFn l k In (l -> q.dom)` by (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] ) >>
conj_tac >- (
  match_mp_tac ComposeFnType >>
  fsrw_tac [][IsTypedFn_def] ) >>
srw_tac [][GraphFnAp] >>
qmatch_assum_rename_tac `z In l` [] >>
`ComposeFn (l,q.dom,q.cod) q.map (GraphFn l k) ' z = q.map ' (GraphFn l k ' z)`
  by fsrw_tac [][IsTypedFn_def,ApComposeFn] >>
srw_tac [][GraphFnAp,Abbr`k`,Abbr`l`,Abbr`n`] >>
`maps_to c.cat (mabs c z) (c.cat.cod g) x` by (
  match_mp_tac In_homset_mabs >>
  srw_tac [][] >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  fsrw_tac [][] ) >>
`composable c.cat (mabs c z,g)` by (
  srw_tac [][composable_def] >>
  fsrw_tac [][maps_to_def] ) >>
imp_res_tac is_lscat_is_category >>
`c.cat.comp (mabs c z,g) ∈ c.cat.mor` by imp_res_tac comp_mor_dom_cod >>
srw_tac [][mabs_mrep] >>
Q.ISPECL_THEN [`f`,`f.dom`,`f.cod`,`(g,mabs c z)`] mp_tac morf_comp >>
srw_tac [][op_cat_composable] >>
unabbrev_all_tac >>
`maps_to set_cat (f.morf (mabs c z)) (objf f x) (objf f (c.cat.cod g))` by
  metis_tac [functor_axioms_def,is_functor_def,op_cat_maps_to,maps_to_def] >>
`(f.morf (mabs c z)) ∈ set_cat.mor` by fsrw_tac [][maps_to_def] >>
`IsTypedFn (f.morf (mabs c z))` by fsrw_tac [][set_cat_def] >>
`composable set_cat (f.morf g,f.morf (mabs c z))` by (
  fsrw_tac [][composable_def,set_cat_dom,set_cat_cod,set_cat_mor] >>
  fsrw_tac [][maps_to_def] ) >>
srw_tac [][] >>
srw_tac [][ComposeTypedFn_def] >>
match_mp_tac (MP_CANON ApComposeFn) >>
fsrw_tac [][maps_to_def] >>
fsrw_tac [][IsTypedFn_def] >>
metis_tac [])

val YMapInvImage = Q.store_thm(
"YMapInvImage",
`∀c x f y. is_lscat c ∧ functor_maps_to f (op_cat c.cat) set_cat ∧
           x ∈ c.cat.obj ∧ y In (objf f x) ⇒
             nt_maps_to (YMapInv c x f y) (objf (Yfunctor c) x) f`,
srw_tac [][nt_maps_to_def]
>- srw_tac [][is_nat_trans_YMapInv]
>> srw_tac [][YMapInv_def])

val YMap1 = Q.store_thm(
"YMap1",
`∀c f x n. is_lscat c ∧ functor_maps_to f (op_cat c.cat) set_cat ∧
           x ∈ c.cat.obj ∧ nt_maps_to n (objf (Yfunctor c) x) f ⇒
             (YMapInv c x f (YMap c x n) = n)`,
srw_tac [][] >>
match_mp_tac nt_eq_thm >>
imp_res_tac YMapImage >>
imp_res_tac is_nat_trans_YMapInv >>
conj_tac >- srw_tac [][] >>
conj_tac >- fsrw_tac [][nt_maps_to_def] >>
conj_tac >- fsrw_tac [][YMapInv_def,nt_maps_to_def] >>
conj_tac >- fsrw_tac [][YMapInv_def,nt_maps_to_def] >>
qx_gen_tac `z` >>
strip_tac >>
`z ∈ c.cat.obj` by (
  fsrw_tac [][YMapInv_def] >>
  pop_assum mp_tac >> srw_tac [][] ) >>
srw_tac [][YMapInv_at] >>
fsrw_tac [][nt_maps_to_def] >>
qpat_assum `X = objf (Yfunctor c) x` mp_tac >> srw_tac [][] >>
`∀z. z ∈ c.cat.obj ⇒ maps_to n.cod.cod (n.at z) (homset c (z,x)) (objf n.cod z)` by (
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
  metis_tac [contra_hom_functor_objf] ) >>
first_assum (qspec_then `z` mp_tac) >>
first_x_assum (qspec_then `x` mp_tac) >>
srw_tac [][] >>
fsrw_tac [][functor_maps_to_def] >>
qpat_assum `maps_to n.cod.cod (n.at z) X Y` mp_tac >> srw_tac[][maps_to_def] >>
`IsTypedFn (n.at z)` by fsrw_tac [][set_cat_def] >>
fsrw_tac [][set_cat_dom,set_cat_cod] >>
srw_tac [][TypedGraphFn_def,TypedFn_component_equality] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`(n.at z).dom`,`(n.at z).cod`] >>
conj_tac >- (
  srw_tac [][] >>
  match_mp_tac GraphFnType >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac InFn >>
  qexists_tac `objf n.cod x` >>
  srw_tac [][] >>
  `maps_to c.cat (mabs c g) z x` by imp_res_tac In_homset_mabs >>
  imp_res_tac op_cat_maps_to >>
  Q.ISPECL_THEN [`n.cod`,`op_cat c.cat`,`set_cat`,`mabs c g`,`x`,`z`]
    mp_tac morf_maps_to >>
  srw_tac [][functor_maps_to_def] >>
  imp_res_tac maps_to_set_cat ) >>
conj_tac >- fsrw_tac [][IsTypedFn_def] >>
qx_gen_tac `f` >>
srw_tac [][GraphFnAp] >>
srw_tac [][YMap_def] >>
Q.ISPECL_THEN [`n`,`hom_functor (op_lscat c) x`,`n.cod`,`set_cat`,
               `mabs c f`,`x`,`z`]
  mp_tac naturality >>
imp_res_tac is_lscat_is_category >>
`maps_to c.cat (mabs c f) z x` by (
  match_mp_tac In_homset_mabs >> srw_tac [][] ) >>
imp_res_tac maps_to_def >>
fsrw_tac [][op_cat_maps_to,contra_hom_functor_morf,nt_maps_to_def] >>
qmatch_abbrev_tac `(set_cat.comp (f1,f2) = set_cat.comp (f3,f4)) ⇒ X` >>
`IsTypedFn f2` by (
  srw_tac [][Abbr`f2`] >>
  match_mp_tac IsTypedFnTypedGraphFn >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `c.cat.cod (mabs c f)` >>
  srw_tac [][] >>
  imp_res_tac In_homset_mabs ) >>
`composable set_cat (f1,f2)` by (
  srw_tac [][composable_def,Abbr`f2`] >>
  srw_tac [][TypedGraphFn_def] ) >>
`maps_to set_cat f3 (objf n.cod ((op_cat c.cat).dom (mabs c f)))
                    (objf n.cod ((op_cat c.cat).cod (mabs c f)))`
 by metis_tac [maps_to_morf,op_cat_mor] >>
`f3 ∈ set_cat.mor` by fsrw_tac [][maps_to_def] >>
`IsTypedFn f3` by fsrw_tac [][set_cat_def] >>
`f4 ∈ set_cat.mor` by metis_tac [] >>
`IsTypedFn f4` by fsrw_tac [][set_cat_def] >>
`composable set_cat (f3,f4)` by (
  srw_tac [][composable_def] >>
  qpat_assum `n.cod.cod = set_cat` assume_tac >>
  fsrw_tac [][Abbr`f3`,Abbr`f4`,maps_to_def] ) >>
asm_simp_tac (srw_ss()) [] >>
asm_simp_tac (srw_ss()) [ComposeTypedFn_def] >>
`f1.map In (f2.cod -> objf n.cod z)` by (
  fsrw_tac [][IsTypedFn_def,Abbr`f2`,TypedGraphFn_def] >>
  metis_tac [] ) >>
`f2.map In (f2.dom -> f2.cod)` by fsrw_tac [][IsTypedFn_def] >>
`ComposeFn (f2.dom,f2.cod,objf n.cod z) f1.map f2.map In
 (f2.dom -> objf n.cod z)` by srw_tac [][ComposeFnType] >>
`f3.map In (f4.cod -> f3.cod)` by (
  qpat_assum `n.cod.cod = set_cat` assume_tac >>
  fsrw_tac [][set_cat_cod] >>
  fsrw_tac [][IsTypedFn_def,maps_to_def] >>
  metis_tac [] ) >>
`f4.map In (f4.dom -> f4.cod)` by fsrw_tac [][IsTypedFn_def] >>
`ComposeFn (f4.dom,f4.cod,f3.cod) f3.map f4.map In
  (f4.dom -> f3.cod)` by srw_tac [][ComposeFnType] >>
`f4.dom = f2.dom` by (
  qpat_assum `n.cod.cod = set_cat` assume_tac >>
  fsrw_tac [][set_cat_dom] >>
  srw_tac [][Abbr`f2`,TypedGraphFn_def] ) >>
`f3.cod = objf n.cod z` by (
  fsrw_tac [][maps_to_def] ) >>
fsrw_tac [][] >>
strip_tac >>
`c.mrep (c.cat.id x) In f2.dom` by (
  srw_tac [][Abbr`f2`,TypedGraphFn_def] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][id_maps_to] ) >>
`ComposeFn (f2.dom,f2.cod,objf n.cod z) f1.map f2.map ' c.mrep (c.cat.id x) =
 ComposeFn (f2.dom,f4.cod,objf n.cod z) f3.map f4.map ' c.mrep (c.cat.id x)`
  by metis_tac [ExtFn] >>
pop_assum (mp_tac o SYM) >>
srw_tac [][ApComposeFn] >>
fsrw_tac [][Abbr`f2`,TypedGraphFn_def] >>
srw_tac [][GraphFnAp] >>
srw_tac [][mabs_mrep,id_mor,mor_obj] >>
srw_tac [][id_comp2] >>
metis_tac [mrep_mabs,mor_obj])

val YMap2 = Q.store_thm(
"YMap2",
`∀c x f y. is_lscat c ∧ functor_maps_to f (op_cat c.cat) set_cat ∧
           x ∈ c.cat.obj ∧ y In (objf f x) ⇒
             (YMap c x (YMapInv c x f y) = y)`,
srw_tac [][YMap_def,YMapInv_at,TypedGraphFn_def] >>
imp_res_tac is_lscat_is_category >>
`c.mrep (c.cat.id x) In homset c (x,x)` by (
  match_mp_tac mrep_in_homset >>
  srw_tac [][id_maps_to] ) >>
srw_tac [][GraphFnAp] >>
srw_tac [][mabs_mrep,id_mor] >>
`f.morf ((op_cat c.cat).id x) = set_cat.id (objf f x)` by srw_tac [][morf_id] >>
imp_res_tac op_cat_id >> fsrw_tac [][])

val YfunctorNT_YMapInv = Q.store_thm(
"YfunctorNT_YMapInv",
`∀c f x y. is_lscat c ∧ maps_to c.cat f x y ⇒
    (YfunctorNT c f = YMapInv c x (hom_functor (op_lscat c) y) (c.mrep f))`,
srw_tac [][] >>
match_mp_tac nt_eq_thm >>
imp_res_tac maps_to_def >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
conj_tac >- srw_tac [][is_nat_trans_YfunctorNT] >>
conj_tac >- (
  match_mp_tac is_nat_trans_YMapInv >>
  srw_tac [][hom_functor_objf,functor_maps_to_def,is_functor_hom_functor] >>
  match_mp_tac mrep_in_homset >> srw_tac [][] ) >>
conj_tac >- srw_tac [][YfunctorNT_def,YMapInv_def] >>
conj_tac >- srw_tac [][YfunctorNT_def,YMapInv_def] >>
srw_tac [][YfunctorNT_at,YMapInv_at,hom_functor_morf,hom_functor_objf] >>
srw_tac [][TypedGraphFn_def] >>
match_mp_tac GraphFnExt >> srw_tac [][] >>
qmatch_assum_rename_tac `g In homset c (z,c.cat.dom f)` [] >>
`maps_to c.cat (mabs c g) z (c.cat.dom f)` by imp_res_tac In_homset_mabs >>
imp_res_tac maps_to_def >>
srw_tac [][hom_functor_morf] >>
srw_tac [][TypedGraphFn_def] >>
imp_res_tac mrep_in_homset >>
srw_tac [][GraphFnAp] >>
srw_tac [][mabs_mrep])

val YMapYoneda = Q.store_thm(
"YMapYoneda",
`∀c f x y. is_lscat c ∧ maps_to c.cat f x y ⇒
  ((Yfunctor c).morf f = YMapInv c x (objf (Yfunctor c) y) (c.mrep f))`,
srw_tac [][] >>
imp_res_tac maps_to_def >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
srw_tac [][YfunctorNT_YMapInv])

val YonedaFull = Q.store_thm(
"YonedaFull",
`∀c x y n. is_lscat c ∧ x ∈ c.cat.obj ∧ y ∈ c.cat.obj ∧
           nt_maps_to n (objf (Yfunctor c) x) (objf (Yfunctor c) y) ⇒
             (maps_to c.cat (mabs c (YMap c x n)) x y) ∧
             ((Yfunctor c).morf (mabs c (YMap c x n)) = n)`,
rpt gen_tac >> strip_tac >>
`YMap c x n In objf (hom_functor (op_lscat c) y) x` by (
  match_mp_tac YMapImage >>
  imp_res_tac Yfunctor_objf >>
  fsrw_tac [][] >>
  srw_tac [][functor_maps_to_def] >>
  srw_tac [][is_functor_hom_functor] ) >>
`YMap c x n In homset c (x,y)` by metis_tac [contra_hom_functor_objf] >>
conj_asm1_tac >- srw_tac [][In_homset_mabs] >>
imp_res_tac YMapYoneda >>
srw_tac [][] >>
`c.mrep (mabs c (YMap c x n)) = YMap c x n` by metis_tac [mrep_mabs] >>
srw_tac [][] >>
match_mp_tac YMap1 >>
qpat_assum `x ∈ c.cat.obj` assume_tac >>
qpat_assum `y ∈ c.cat.obj` assume_tac >>
qpat_assum `is_lscat c` assume_tac >>
fsrw_tac [][] >>
srw_tac [][functor_maps_to_def,is_functor_hom_functor])

val YonedaFaithful = Q.store_thm(
"YonedaFaithful",
`∀c f g x y. is_lscat c ∧ maps_to c.cat f x y ∧ maps_to c.cat g x y ∧
             ((Yfunctor c).morf f = (Yfunctor c).morf g) ⇒
               (f = g)`,
srw_tac [][] >>
imp_res_tac maps_to_def >>
imp_res_tac Yfunctor_morf >>
imp_res_tac YfunctorNT_YMapInv >>
fsrw_tac [][] >>
`YMap c x (YMapInv c x (hom_functor (op_lscat c) y) (c.mrep f)) =
 YMap c x (YMapInv c x (hom_functor (op_lscat c) y) (c.mrep g))`
 by metis_tac [] >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
`functor_maps_to (hom_functor (op_lscat c) y) (op_cat c.cat) set_cat` by (
  srw_tac [][functor_maps_to_def,is_functor_hom_functor] ) >>
`c.mrep f In objf (hom_functor (op_lscat c) y) x` by (
  srw_tac [][hom_functor_objf] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][maps_to_def] ) >>
`c.mrep g In objf (hom_functor (op_lscat c) y) x` by (
  srw_tac [][hom_functor_objf] >>
  match_mp_tac mrep_in_homset >>
  srw_tac [][maps_to_def] ) >>
imp_res_tac YMap2 >>
fsrw_tac [][] >>
metis_tac [is_lscat_def])

val YonedaEmbedding = Q.store_thm(
"YonedaEmbedding",
`∀c a b. is_lscat c ∧ a ∈ c.cat.obj ∧ b ∈ c.cat.obj ∧
         (objf (Yfunctor c) a = objf (Yfunctor c) b) ⇒
           (a = b)`,
srw_tac [][] >> pop_assum mp_tac >> srw_tac [][] >>
`(hom_functor (op_lscat c) a).morf (c.cat.id a) =
 (hom_functor (op_lscat c) b).morf (c.cat.id a)`
by srw_tac [][] >>
pop_assum mp_tac >>
pop_assum (K ALL_TAC) >>
imp_res_tac is_lscat_is_category >>
imp_res_tac id_mor >>
srw_tac [][hom_functor_morf] >>
fsrw_tac [][TypedGraphFn_def] >>
imp_res_tac id_dom_cod >>
fsrw_tac [][] >>
`c.mrep (c.cat.id a) In homset c (a,a)` by (
  match_mp_tac mrep_in_homset >>
  imp_res_tac id_maps_to >>
  srw_tac [][] ) >>
`c.mrep (c.cat.id a) In homset c (a,b)` by metis_tac [] >>
`maps_to c.cat (mabs c (c.mrep (c.cat.id a))) a b` by (
  match_mp_tac In_homset_mabs >> srw_tac [][] ) >>
pop_assum mp_tac >> srw_tac [][mabs_mrep] >>
fsrw_tac [][maps_to_def])

val _ = export_theory ()
