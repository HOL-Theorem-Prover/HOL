open HolKernel Parse boolLib boolSimps bossLib pred_setTheory zfset_axiomsTheory zfsetTheory pairTheory categoryTheory limitTheory ens_catTheory functorTheory nat_transTheory hom_functorTheory YonedaTheory lcsymtacs;

val _ = new_theory "zfset_cat";

val explode_def = Define`
  explode z = {x | x In z}`;

val implode_def = Define`
  implode s = @z. explode z = s`;

val implode_explode = Q.store_thm(
"implode_explode",
`∀z. implode (explode z) = z`,
srw_tac [][implode_def] >>
SELECT_ELIM_TAC >>
srw_tac [][] >- metis_tac [] >>
fsrw_tac [][explode_def,EXTENSION] >>
fsrw_tac [][Extension_ax]);
val _ = export_rewrites["implode_explode"];

val explode_inj = Q.store_thm(
"explode_inj",
`∀x y. (explode x = explode y) ⇒ (x = y)`,
srw_tac [][explode_def,EXTENSION] >>
srw_tac [][Extension_ax]);

val IsSmall_def = Define`
  IsSmall s = ∃f z. INJ f s (explode z)`;
(* WARNING THIS IS NOT HEREDITARILY SMALL *)

val IsSmall_FINITE = Q.store_thm(
"IsSmall_FINITE",
`∀s. FINITE s ⇒ IsSmall s`,
ho_match_mp_tac FINITE_INDUCT >>
srw_tac [][IsSmall_def] >- (
  srw_tac [][INJ_DEF] ) >>
map_every qexists_tac [`λx. if x = e then z else f x`,`Suc z`] >>
fsrw_tac [][INJ_DEF,explode_def,Suc_def,U_def,Singleton_def] >>
srw_tac [][] >> metis_tac [NotInSelf]);

val IsSmall_IMAGE = Q.store_thm(
"IsSmall_IMAGE",
`∀s f. IsSmall s ⇒ IsSmall (IMAGE f s)`,
srw_tac [][IsSmall_def] >>
qmatch_assum_rename_tac `INJ g s (explode z)` [] >>
map_every qexists_tac [`λx. g (@y. y ∈ s ∧ (f y = x))`,`z`] >>
fsrw_tac [DNF_ss][INJ_DEF] >>
srw_tac [][] >- (
  SELECT_ELIM_TAC >>
  srw_tac [][] >>
  metis_tac []) >>
pop_assum mp_tac >>
SELECT_ELIM_TAC >>
SELECT_ELIM_TAC >>
srw_tac [][] >>
metis_tac []);
val _ = export_rewrites["IsSmall_IMAGE"];

val IsSmall_IMAGE_iff = Q.store_thm(
"IsSmall_IMAGE_iff",
`∀s t f. INJ f s t ⇒ (IsSmall (IMAGE f s) ⇔ IsSmall s)`,
srw_tac [][EQ_IMP_THM] >>
fsrw_tac [][IsSmall_def] >>
qmatch_assum_rename_tac `INJ g (IMAGE f s) (explode z)` [] >>
map_every qexists_tac [`g o f`,`z`] >>
fsrw_tac [DNF_ss][INJ_DEF]);

val IsSmall_explode = Q.store_thm(
"IsSmall_explode",
`∀s. IsSmall s ⇔ (∃z. s = explode z)`,
srw_tac [][IsSmall_def,explode_def,EQ_IMP_THM] >>
srw_tac [][EXTENSION] >- (
  qexists_tac `Image (LINV f s) (Spec z (λx. ∃y. y ∈ s ∧ (x = f y)))` >>
  srw_tac [][Spec_def,Image_def] >>
  srw_tac [][EQ_IMP_THM] >- (
    IMP_RES_TAC LINV_DEF >>
    fsrw_tac [][INJ_DEF] >>
    metis_tac []) >>
  metis_tac [LINV_DEF]) >>
map_every qexists_tac [`I`,`z`] >>
srw_tac [][INJ_DEF]);

val explode_IsSmall = Q.store_thm(
"explode_IsSmall",
`∀s. IsSmall (explode s)`,
metis_tac [IsSmall_explode]);
val _ = export_rewrites["explode_IsSmall"];

val In_implode = Q.store_thm(
"In_implode",
`∀s x. IsSmall s ⇒ (x In implode s ⇔ x ∈ s)`,
srw_tac [][] >>
imp_res_tac IsSmall_explode >>
srw_tac [][explode_def]);
val _ = export_rewrites["In_implode"];

val explode_implode = Q.store_thm(
"explode_implode",
`∀s. IsSmall s ⇒ (explode (implode s) = s)`,
srw_tac [][explode_def]);
val _ = export_rewrites["explode_implode"];

val IsSmall_BIJ = Q.store_thm(
"IsSmall_BIJ",
`∀s. IsSmall s ⇒ ∃b z. BIJ b s (IMAGE SOME (explode z)) ∧
                       ∀x. x ∉ s ⇒ (b x = NONE)`,
srw_tac [][IsSmall_def] >>
qexists_tac `λx. if x ∈ s then SOME (f x) else NONE` >>
qexists_tac `Spec z (λx. ∃y. y ∈ s ∧ (x = f y))` >>
fsrw_tac [DNF_ss][BIJ_DEF,INJ_DEF,SURJ_DEF,explode_def,Spec_def] >>
metis_tac []);

val the_zfrep_def = Define`
  the_zfrep s = @bz. BIJ (FST bz) s (IMAGE SOME (explode (SND bz))) ∧
                     ∀x. x ∉ s ⇒ (FST bz x = NONE)`;

val the_zfrep_inj = Q.store_thm(
"the_zfrep_inj",
`∀s1 s2. IsSmall s1 ∧ IsSmall s2 ∧ (the_zfrep s1 = the_zfrep s2) ⇒ (s1 = s2)`,
simp_tac std_ss [the_zfrep_def,GSYM AND_IMP_INTRO] >>
rpt gen_tac >> ntac 2 strip_tac >>
imp_res_tac IsSmall_BIJ >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [FST,SND] >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [FST,SND] >>
Cases >> srw_tac [][EXTENSION] >>
srw_tac [][EQ_IMP_THM] >> spose_not_then strip_assume_tac >>
res_tac >> fsrw_tac [DNF_ss][BIJ_DEF,SURJ_DEF] >>
res_tac >> fsrw_tac [][]);

val _ = overload_on("zfbij",``λs. FST(the_zfrep s)``);
val _ = overload_on("zfrep",``λs. SND(the_zfrep s)``);

val zfbij_SOME = Q.store_thm(
"zfbij_SOME",
`∀s x. IsSmall s ⇒ (IS_SOME (zfbij s x) ⇔ x ∈ s)`,
rpt strip_tac >>
srw_tac [][the_zfrep_def] >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [FST,SND,IsSmall_BIJ] >>
Cases >> srw_tac [][] >>
Cases_on `x ∈ s` >> res_tac >> fsrw_tac [][] >>
fsrw_tac [DNF_ss][BIJ_DEF,SURJ_DEF] >>
res_tac >> fsrw_tac [][]);

val zfel_def = Define`
  zfel s x = THE (zfbij s x)`;

val elzf_def = Define`
  elzf s z = LINV (zfbij s) s (SOME z)`;

val In_zfrep_thm = Q.store_thm(
"In_zfrep_thm",
`∀s z. IsSmall s ⇒ (z In zfrep s ⇔ ∃x. x ∈ s ∧ (z = zfel s x))`,
srw_tac [][zfel_def] >>
srw_tac [][the_zfrep_def] >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [FST,SND,IsSmall_BIJ] >>
Cases >> srw_tac [][] >>
fsrw_tac [DNF_ss][BIJ_DEF,SURJ_DEF,INJ_DEF,explode_def] >>
EQ_TAC >- (
  strip_tac >> res_tac >>
  qexists_tac `y` >> srw_tac [][] ) >>
srw_tac [][] >>
qmatch_rename_tac `THE (b x) In z` [] >>
Cases_on `b x` >>
res_tac >> fsrw_tac [][] >> srw_tac [][]);

val elzf_zfel = Q.store_thm(
"elzf_zfel",
`∀s x. IsSmall s ∧ x ∈ s ⇒ (elzf s (zfel s x) = x)`,
srw_tac[][elzf_def,zfel_def] >>
imp_res_tac zfbij_SOME >>
Cases_on `zfbij s x` >> fsrw_tac [][] >>
pop_assum (assume_tac o SYM) >> fsrw_tac [][] >>
match_mp_tac (MP_CANON LINV_DEF) >>
srw_tac [][the_zfrep_def] >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [FST,SND,IsSmall_BIJ] >>
metis_tac [BIJ_DEF]);

val zfel_elzf = Q.store_thm(
"zfel_elzf",
`∀s z. IsSmall s ∧ z In zfrep s ⇒ (zfel s (elzf s z) = z)`,
srw_tac [][] >>
`∃x. x ∈ s ∧ (z = zfel s x)` by metis_tac[In_zfrep_thm] >>
srw_tac [][elzf_zfel]);

val _ = export_rewrites["elzf_zfel","zfel_elzf"];

val zfrep_empty = Q.store_thm(
"zfrep_empty",
`∀s. IsSmall s ⇒ ((zfrep s = {}) = (s = {}))`,
srw_tac [][EXTENSION,Extension_ax] >>
metis_tac [Empty_def,In_zfrep_thm]);
val _ = export_rewrites["zfrep_empty"];

val IsTypedFn_def = Define`
  IsTypedFn f = f.map In (f.dom -> f.cod)`;

val TypedGraphFn_def = Define`
  TypedGraphFn (X,Y) f = <|
    dom := X; cod := Y; map := GraphFn X f |>`;

val TypedGraphFn_components = Q.store_thm(
"TypedGraphFn_components",
`∀X Y f. ((TypedGraphFn (X,Y) f).dom = X) ∧
         ((TypedGraphFn (X,Y) f).cod = Y) ∧
         ((TypedGraphFn (X,Y) f).map = GraphFn X f)`,
srw_tac [][TypedGraphFn_def]);
val _ = export_rewrites["TypedGraphFn_components"];

val IsTypedFnTypedGraphFn = Q.store_thm(
"IsTypedFnTypedGraphFn",
`∀f X Y. IsTypedFn (TypedGraphFn (X,Y) f) = HasFnType f X Y`,
srw_tac [][IsTypedFn_def,TypedGraphFn_def,GraphFnType,EQ_IMP_THM] >>
srw_tac [][HasFnType_def] >> metis_tac [InFn,GraphFnAp]);
val _ = export_rewrites["IsTypedFnTypedGraphFn"];

val ComposeTypedFn_def = Define`
  ComposeTypedFn = compose (λf g. ComposeFn (f.dom,f.cod,g.cod) g.map f.map)`;

val _ = add_infix("|o|",800,RIGHT);
val _ = overload_on("|o|",``λg f. ComposeTypedFn f g``);

val ComposeTypedFn_components = Q.store_thm(
"ComposeTypedFn_components",
`∀f g. (f ≈> g) ⇒
       (((g |o| f).dom = f.dom) ∧
        ((g |o| f).cod = g.cod) ∧
        ((g |o| f).map = ComposeFn(f.dom,f.cod,g.cod) g.map f.map))`,
srw_tac [][ComposeTypedFn_def]);
val _ = export_rewrites["ComposeTypedFn_components"];

val pre_set_cat_def = Define`
 pre_set_cat =  <|
    obj := UNIV ;
    mor := {f | IsTypedFn f} ;
    id_map  := IdFn ;
    comp := λf g. (g |o| f).map |>`;

val pre_set_cat_obj_mor = Q.store_thm(
"pre_set_cat_obj_mor",
`(∀x. x ∈ pre_set_cat.obj) ∧
 (∀f. f ∈ pre_set_cat.mor = IsTypedFn f)`,
srw_tac [][pre_set_cat_def]);
val _ = export_rewrites["pre_set_cat_obj_mor"];

val pre_set_cat_id = Q.store_thm(
"pre_set_cat_id",
`∀x. (id x -:pre_set_cat) = TypedGraphFn (x,x) I`,
srw_tac [][id_in_def,restrict_def,pre_set_cat_def,TypedGraphFn_def,IdFn_eq_GraphFnI]);
val _ = export_rewrites["pre_set_cat_id"];

val pre_set_cat_maps_to_in = Q.store_thm(
"pre_set_cat_maps_to_in",
`∀f x y. f :- x → y -:pre_set_cat ⇔ IsTypedFn f ∧ f :- x → y`,
srw_tac [][maps_to_in_def,EQ_IMP_THM]);
val _ = export_rewrites["pre_set_cat_maps_to_in"];

val pre_set_cat_composable_in = Q.store_thm(
"pre_set_cat_composable_in",
`∀f g. f ≈> g -:pre_set_cat ⇔ IsTypedFn f ∧ IsTypedFn g ∧ f ≈> g`,
srw_tac [][composable_in_def]);
val _ = export_rewrites["pre_set_cat_composable_in"];

val pre_set_cat_compose_in = Q.store_thm(
"pre_set_cat_compose_in",
`∀f g. f ≈> g -:pre_set_cat ⇒ (g o f -:pre_set_cat = g |o| f)`,
srw_tac [][compose_in_def,restrict_def,pre_set_cat_def] >>
srw_tac [][morphism_component_equality]);
val _ = export_rewrites["pre_set_cat_compose_in"];

val set_cat_def = Define`
  set_cat = mk_cat pre_set_cat`;

val is_category_set_cat = Q.store_thm(
"is_category_set_cat",
`is_category set_cat`,
srw_tac [][set_cat_def] >>
srw_tac [][category_axioms_def] >- (
  srw_tac [][HasFnType_def] )
>- (
  qmatch_abbrev_tac `f o g -:pre_set_cat = f` >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `f |o| g` >>
  reverse conj_tac >- (
    srw_tac [][Abbr`g`,morphism_component_equality,GSYM IdFn_eq_GraphFnI] >>
    match_mp_tac ComposeFnId1 >> fsrw_tac [][IsTypedFn_def] ) >>
  match_mp_tac pre_set_cat_compose_in >>
  srw_tac [][Abbr`g`,IdFnType,HasFnType_def] )
>- (
  qmatch_abbrev_tac `g o f -:pre_set_cat = f` >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `g |o| f` >>
  reverse conj_tac >- (
    srw_tac [][Abbr`g`,morphism_component_equality,GSYM IdFn_eq_GraphFnI] >>
    match_mp_tac ComposeFnId2 >> fsrw_tac [][IsTypedFn_def] ) >>
  match_mp_tac pre_set_cat_compose_in >>
  srw_tac [][Abbr`g`,IdFnType,HasFnType_def] )
>- (
  qsuff_tac `f ≈> (h |o| g) -:pre_set_cat ∧ (g |o| f) ≈> h -:pre_set_cat` >- (
    srw_tac [][] >> srw_tac [][morphism_component_equality] >>
    match_mp_tac (GSYM ComposeFnAssoc) >> fsrw_tac [][IsTypedFn_def] ) >>
  srw_tac [][IsTypedFn_def] >>
  match_mp_tac ComposeFnType >>
  fsrw_tac [][IsTypedFn_def] ) >>
srw_tac [][IsTypedFn_def] >>
match_mp_tac ComposeFnType >>
fsrw_tac [][IsTypedFn_def])
val _ = export_rewrites["is_category_set_cat"];

val set_cat_obj = Q.store_thm(
"set_cat_obj",
`set_cat.obj = UNIV`,
srw_tac [][set_cat_def,pre_set_cat_def]);

val set_cat_mor = Q.store_thm(
"set_cat_mor",
`set_cat.mor = {f | IsTypedFn f}`,
srw_tac [][set_cat_def,pre_set_cat_def]);

val set_cat_id = Q.store_thm(
"set_cat_id",
`∀x. (id x -:set_cat) = TypedGraphFn (x,x) I`,
srw_tac [][set_cat_def]);

val set_cat_composable_in = Q.store_thm(
"set_cat_composable_in",
`∀f g. f ≈> g -:set_cat ⇔ IsTypedFn f ∧ IsTypedFn g ∧ f ≈> g`,
srw_tac [][set_cat_def]);

val set_cat_compose_in = Q.store_thm(
"set_cat_compose_in",
`∀f g. f ≈> g -:set_cat ⇒ (g o f -:set_cat = g |o| f)`,
srw_tac [][set_cat_def]);

val set_cat_maps_to_in = Q.store_thm(
"set_cat_maps_to_in",
`∀f x y. f :- x → y -:set_cat ⇔ IsTypedFn f ∧ f :- x → y`,
srw_tac [][set_cat_def]);

val _ = export_rewrites[
"set_cat_obj","set_cat_mor","set_cat_id",
"set_cat_composable_in","set_cat_compose_in",
"set_cat_maps_to_in"];

val has_binary_products_set_cat = Q.store_thm(
"has_binary_products_set_cat",
`has_binary_products set_cat`,
srw_tac [][has_binary_products_thm,is_binary_product_thm] >>
map_every qexists_tac [`TypedGraphFn (Prod a b, a) Fst`,`TypedGraphFn (Prod a b, b) Snd`] >>
fsrw_tac [][HasFnType_def] >>
conj_tac >- metis_tac [FstType] >>
conj_tac >- metis_tac [SndType] >>
rpt gen_tac >> strip_tac >>
fsrw_tac [][EXISTS_UNIQUE_THM] >>
`∀m. IsTypedFn m ∧ (m.dom = p1.dom) ∧ (m.cod = a # b) ⇒
  m ≈> TypedGraphFn (a # b,a) Fst -:set_cat ∧
  m ≈> TypedGraphFn (a # b,b) Snd -:set_cat` by (
  srw_tac [][HasFnType_def] >>
  metis_tac [InProd,FstType,SndType,IsTypedFn_def,InFn] ) >>
conj_tac >- (
  qexists_tac `TypedGraphFn (p1.dom, a # b) (λx. (Pair(p1.map ' x)(p2.map ' x)))` >>
  conj_asm1_tac >- (
    srw_tac [][HasFnType_def] >>
    metis_tac [InFn,IsTypedFn_def,InProd] ) >>
  conj_tac >> (
  qmatch_abbrev_tac `f o g -:set_cat = x` >>
  `g ≈> f -:set_cat` by metis_tac [] >>
  srw_tac [][] >>
  unabbrev_all_tac >>
  srw_tac [][morphism_component_equality] >>
  fsrw_tac [][ComposeGraphFns] >>
  qmatch_rename_tac `X = p.map` ["X"] >>
  match_mp_tac FnEqThm >>
  map_every qexists_tac [`p.dom`,`p.cod`] >>
  fsrw_tac [][GraphFnAp,HasFnType_def] >>
  conj_tac >- (
    match_mp_tac GraphFnType >>
    srw_tac [][HasFnType_def] ) >>
  fsrw_tac [][IsTypedFn_def] >>
  fsrw_tac [][Fst,Snd] )) >>
srw_tac [][] >>
qmatch_rename_tac `m1 = m2` [] >>
first_assum (qspec_then `m1` mp_tac) >>
first_x_assum (qspec_then `m2` mp_tac) >>
ntac 2 strip_tac >>
rpt (qpat_assum `f o g -:set_cat = h` mp_tac) >>
ntac 2 (pop_assum mp_tac) >>
fsrw_tac [][] >>
srw_tac [][morphism_component_equality] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`p1.dom`,`p1.cod # p2.cod`] >>
fsrw_tac [][IsTypedFn_def] >>
srw_tac [][] >>
`m1.map ' x In (p1.cod # p2.cod)` by metis_tac [InFn] >>
`m2.map ' x In (p1.cod # p2.cod)` by metis_tac [InFn] >>
fsrw_tac [][InProdEq] >>
qmatch_rename_tac `Pair x11 x21 = Pair x12 x22` [] >>
qmatch_assum_abbrev_tac `ComposeFn (X,Y,Z) (GraphFn (a#b) P) Q = R` >>
map_every qunabbrev_tac [`P`,`Q`,`R`,`Z`] >>
`(ComposeFn (X,Y,a) (GraphFn Y Fst) m1.map) ' x = p1.map ' x` by srw_tac [][] >>
`(ComposeFn (X,Y,b) (GraphFn Y Snd) m1.map) ' x = p2.map ' x` by srw_tac [][] >>
`(ComposeFn (X,Y,a) (GraphFn Y Fst) m2.map) ' x = p1.map ' x` by srw_tac [][] >>
`(ComposeFn (X,Y,b) (GraphFn Y Snd) m2.map) ' x = p2.map ' x` by srw_tac [][] >>
rpt (qpat_assum `ComposeFn (X,Y,Z) (GraphFn Y P) Q = R` (K ALL_TAC)) >>
ntac 4 (pop_assum mp_tac) >>
`GraphFn Y Fst In (Y -> a)` by metis_tac [GraphFnType] >>
`GraphFn Y Snd In (Y -> b)` by metis_tac [GraphFnType] >>
`Pair x11 x21 In Y` by metis_tac [InProd] >>
`Pair x12 x22 In Y` by metis_tac [InProd] >>
fsrw_tac [][ApComposeFn,GraphFnAp] >>
fsrw_tac [][Fst,Snd]);

val pre_set_to_ens_def = Define`
  pre_set_to_ens = <|
    dom := set_cat;
    cod := ens_cat {s | IsSmall s};
    map := λf. TypedGraphFun (explode f.dom,explode f.cod) (λx. f.map ' x) |>`;

val pre_set_to_ens_components = Q.store_thm(
"pre_set_to_ens_components",
`(pre_set_to_ens.dom = set_cat) ∧
 (pre_set_to_ens.cod = ens_cat {s | IsSmall s}) ∧
 (∀f. pre_set_to_ens##f = TypedGraphFun (explode f.dom,explode f.cod) (λx. f.map ' x))`,
srw_tac [][pre_set_to_ens_def,morf_def]);
val _ = export_rewrites["pre_set_to_ens_components"];

val pre_set_to_ens_objf = Q.store_thm(
"pre_set_to_ens_objf",
`∀x. pre_set_to_ens@@x = explode x`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  qexists_tac `explode x` >> srw_tac [][] >>
  srw_tac [][morphism_component_equality] >>
  srw_tac [][restrict_def,FUN_EQ_THM] >>
  srw_tac [][GraphFnAp,explode_def]) >>
pop_assum mp_tac >>
srw_tac [][EXTENSION,explode_def,morphism_component_equality]);
val _ = export_rewrites["pre_set_to_ens_objf"];

val set_to_ens_def = Define`
  set_to_ens = mk_functor pre_set_to_ens`;

val is_functor_set_to_ens = Q.store_thm(
"is_functor_set_to_ens",
`is_functor set_to_ens`,
srw_tac [][set_to_ens_def] >>
srw_tac [][functor_axioms_def] >- (
  fsrw_tac [][IsTypedFun_def,IsTypedFn_def,
              HasFunType_def,explode_def,extensional_def] >>
  metis_tac [InFn] )
>- (
  qexists_tac `explode x` >>
  srw_tac [][morphism_component_equality] >>
  srw_tac [][FUN_EQ_THM,restrict_def] >>
  srw_tac [][GraphFnAp,explode_def]) >>
qmatch_abbrev_tac `gf = pg o pf -:ens_cat u` >>
`pf ≈> pg -:ens_cat u` by (
  unabbrev_all_tac >> srw_tac [][] >>
  fsrw_tac [][explode_def,IsTypedFn_def,extensional_def] >>
  metis_tac [InFn] ) >>
unabbrev_all_tac >>
srw_tac [][morphism_component_equality] >>
srw_tac [][FUN_EQ_THM] >>
srw_tac [][pre_set_to_ens_def,morf_def,restrict_def,ComposeFun_def] >>
fsrw_tac [][IsTypedFn_def,explode_def] >>
metis_tac [InFn,ApComposeFn]);
val _ = export_rewrites["is_functor_set_to_ens"];

val set_to_ens_components = Q.store_thm(
"set_to_ens_components",
`(set_to_ens.dom = set_cat) ∧
 (set_to_ens.cod = ens_cat {s | IsSmall s}) ∧
 (∀f. IsTypedFn f ⇒ (set_to_ens##f = TypedGraphFun (explode f.dom,explode f.cod) (λx. f.map ' x)))`,
srw_tac [][set_to_ens_def])
val _ = export_rewrites["set_to_ens_components"];

val set_to_ens_objf = Q.store_thm(
"set_to_ens_objf",
`∀x. set_to_ens@@x = explode x`,
srw_tac [][set_to_ens_def]);
val _ = export_rewrites["set_to_ens_objf"];

val cat_iso_set_to_ens = Q.store_thm(
"cat_iso_set_to_ens",
`cat_iso set_to_ens`,
srw_tac [][cat_iso_bij] >- (
  srw_tac [][BIJ_DEF,INJ_DEF,SURJ_DEF,explode_inj] >>
  metis_tac [explode_implode] ) >>
srw_tac [][BIJ_DEF,INJ_DEF,SURJ_DEF] >- (
  fsrw_tac [][hom_def] >>
  fsrw_tac [][explode_def,IsTypedFn_def] >>
  metis_tac [InFn] )
>- (
  pop_assum mp_tac >>
  fsrw_tac [][hom_def] >>
  srw_tac [][TypedGraphFun_Ext,explode_def] >>
  srw_tac [][morphism_component_equality] >>
  fsrw_tac [][IsTypedFn_def] >>
  metis_tac [ExtFn] )
>- (
  fsrw_tac [][hom_def] >>
  fsrw_tac [][explode_def,IsTypedFn_def] >>
  metis_tac [InFn] ) >>
fsrw_tac [][hom_def] >>
fsrw_tac [][] >> srw_tac [][] >>
qexists_tac `TypedGraphFn (a,b) x.map` >>
conj_asm1_tac >- (
  fsrw_tac [][IsTypedFun_def,HasFunType_def,HasFnType_def] >>
  fsrw_tac [][explode_def]  ) >>
fsrw_tac [][] >>
srw_tac [][morphism_component_equality] >>
srw_tac [][FUN_EQ_THM] >>
fsrw_tac [][HasFnType_def,explode_def,restrict_def] >>
fsrw_tac [][IsTypedFun_def,HasFunType_def,extensional_def] >>
srw_tac [][GraphFnAp]);

val _ = overload_on("ens_to_set",``@f. cat_iso_pair set_to_ens f``);

val ens_to_set_dom_cod = Q.store_thm(
"ens_to_set_dom_cod",
`(ens_to_set.dom = ens_cat {s | IsSmall s}) ∧
 (ens_to_set.cod = set_cat)`,
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [cat_iso_set_to_ens,cat_iso_def] >>
metis_tac [cat_iso_pair_def,cat_iso_pair_sym,composable_def,set_to_ens_components]);
val _ = export_rewrites["ens_to_set_dom_cod"];

val is_functor_ens_to_set = Q.store_thm(
"is_functor_ens_to_set",
`is_functor ens_to_set`,
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [cat_iso_set_to_ens,cat_iso_def] >>
srw_tac [][cat_iso_pair_def]);
val _ = export_rewrites["is_functor_ens_to_set"];

val ens_to_set_morf = Q.store_thm(
"ens_to_set_morf",
`∀f. f ∈ (ens_cat {s | IsSmall s}).mor ⇒ (ens_to_set##f = TypedGraphFn (implode f.dom, implode f.cod) f.map)`,
srw_tac [][] >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [cat_iso_set_to_ens,cat_iso_def] >>
qx_gen_tac `ets` >> strip_tac >>
fsrw_tac [][cat_iso_pair_bij] >>
qpat_assum `X = ets.dom` (assume_tac o SYM) >>
fsrw_tac [][] >>
first_x_assum (qspecl_then [`implode f.dom`,`implode f.cod`] mp_tac) >>
fsrw_tac [][] >>
strip_tac >>
first_x_assum (qspec_then `f` (mp_tac o GSYM)) >>
`f ∈ ens_cat {s | IsSmall s}|f.dom→f.cod|` by (
  srw_tac [][hom_def] ) >>
srw_tac [][] >>
`∀s. IsSmall s ⇒ (ets@@s = implode s)` by (
  srw_tac [][] >>
  qsuff_tac `set_to_ens@@(LINV (objf set_to_ens) UNIV s)=set_to_ens@@(implode s)` >- (
    fsrw_tac [][BIJ_DEF,INJ_DEF] ) >>
  qmatch_abbrev_tac `q (LINV q u s) = q (implode s)` >>
  `q (implode s) = s` by srw_tac [][Abbr`q`] >>
  pop_assum mp_tac >> simp_tac (srw_ss()) [] >> strip_tac >>
  match_mp_tac (MP_CANON BIJ_LINV_INV) >>
  srw_tac [][Abbr`q`,Abbr`u`] >>
  qexists_tac `{s | IsSmall s}` >> srw_tac [][] ) >>
`ets##f :- implode f.dom → implode f.cod -:set_cat` by (
  match_mp_tac morf_maps_to >>
  map_every qexists_tac [`ets.dom`,`f.dom`,`f.cod`] >>
  fsrw_tac [][] ) >>
qmatch_abbrev_tac `a = b` >>
`a ∈ set_cat|implode f.dom→implode f.cod|` by (
  fsrw_tac [][hom_def] >>
  qpat_assum `ets##f = a` assume_tac >>
  fsrw_tac [][] ) >>
`b ∈ set_cat|implode f.dom→implode f.cod|` by (
  fsrw_tac [][Abbr`b`,hom_def] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def,HasFnType_def] ) >>
qsuff_tac `set_to_ens##a=set_to_ens##b` >- (
  fsrw_tac [][BIJ_DEF,INJ_DEF] ) >>
unabbrev_all_tac >>
qmatch_abbrev_tac `q (LINV q h f) = q z` >>
`q z = f` by (
  qunabbrev_tac `q` >>
  `IsTypedFn z` by (
    unabbrev_all_tac >>
    srw_tac [][] >>
    srw_tac [][HasFnType_def] >>
    fsrw_tac [][IsTypedFun_def,HasFunType_def] ) >>
  srw_tac [][Abbr`z`,morphism_component_equality] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def,extensional_def] >>
  srw_tac [][restrict_def,FUN_EQ_THM] >>
  srw_tac [][GraphFnAp] ) >>
fsrw_tac [][] >>
match_mp_tac (MP_CANON BIJ_LINV_INV) >>
unabbrev_all_tac >>
qexists_tac `ens_cat {s | IsSmall s}|f.dom→f.cod|` >>
srw_tac [][]);
val _ = export_rewrites["ens_to_set_morf"];

val ens_to_set_objf = Q.store_thm(
"ens_to_set_objf",
`∀s. IsSmall s ⇒ (ens_to_set@@s = implode s)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
conj_tac >- (
  qexists_tac `implode s` >>
  srw_tac [][morphism_component_equality] >>
  match_mp_tac GraphFnExt >>
  srw_tac [][restrict_def] ) >>
srw_tac [][morphism_component_equality]);
val _ = export_rewrites["ens_to_set_objf"];

val cat_iso_ens_to_set = Q.store_thm(
"cat_iso_ens_to_set",
`cat_iso ens_to_set`,
SELECT_ELIM_TAC >>
metis_tac [cat_iso_pair_sym,cat_iso_set_to_ens,cat_iso_def]);
val _ = export_rewrites["cat_iso_ens_to_set"];

val is_locally_small_def = Define`
  is_locally_small c = ∀s. s ∈ homs c ⇒ IsSmall s`;

val _ = overload_on("is_lscat",``λc.  is_category c ∧ is_locally_small c``);

val pre_rep_functor_def = Define`
  pre_rep_functor u = <|
    dom := ens_cat u ;
    cod := ens_cat {s | IsSmall s} ;
    map := λf. TypedGraphFun (explode (zfrep f.dom), explode (zfrep f.cod)) (λz. zfel f.cod (f.map (elzf f.dom z)))
    |>`;

val pre_rep_functor_components = Q.store_thm(
"pre_rep_functor_components",
`∀u. ((pre_rep_functor u).dom = ens_cat u) ∧
     ((pre_rep_functor u).cod = ens_cat {s | IsSmall s}) ∧
     (∀f. ((pre_rep_functor u)##f = TypedGraphFun (explode (zfrep f.dom), explode (zfrep f.cod)) (λz. zfel f.cod (f.map (elzf f.dom z)))))`,
srw_tac [][pre_rep_functor_def,morf_def]);
val _ = export_rewrites["pre_rep_functor_components"];

val pre_rep_functor_objf = Q.store_thm(
"pre_rep_functor_objf",
`∀u x. IsSmall x ∧ x ∈ u ⇒ ((pre_rep_functor u)@@x = explode (zfrep x))`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
conj_tac >- (
  qexists_tac `explode (zfrep x)` >>
  fsrw_tac [][] >>
  fsrw_tac [][TypedGraphFun_Ext] >>
  srw_tac [][restrict_def,explode_def,zfel_elzf] >>
  pop_assum mp_tac >> srw_tac [][In_zfrep_thm] >>
  metis_tac [elzf_zfel] ) >>
qx_gen_tac `s` >>
srw_tac [][] >>
pop_assum mp_tac >> srw_tac [][TypedGraphFun_Ext]);
val _ = export_rewrites["pre_rep_functor_objf"];

val rep_functor_def = Define`
  rep_functor u = mk_functor (pre_rep_functor u)`;

val is_functor_rep_functor = Q.store_thm(
"is_functor_rep_functor",
`∀u. (∀s. s ∈ u ⇒ IsSmall s) ⇒ is_functor (rep_functor u)`,
srw_tac [][rep_functor_def] >>
fsrw_tac [][functor_axioms_def] >>
conj_tac >- (
  fsrw_tac [][explode_def] >>
  fsrw_tac [DNF_ss][In_zfrep_thm] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
  metis_tac [] ) >>
conj_tac >- (
  qx_gen_tac `s` >> strip_tac >>
  qexists_tac `explode (zfrep s)` >>
  fsrw_tac [][TypedGraphFun_Ext] >>
  fsrw_tac [][explode_def] >>
  fsrw_tac [DNF_ss][In_zfrep_thm,restrict_def] ) >>
map_every qx_gen_tac [`f`,`g`] >> strip_tac >>
qmatch_abbrev_tac `ff = gg o hh -:ens_cat uu` >>
`hh ≈> gg -:ens_cat uu` by (
  unabbrev_all_tac >>
  fsrw_tac [][] >>
  fsrw_tac [DNF_ss][explode_def,In_zfrep_thm] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
  metis_tac [] >>
  metis_tac [] ) >>
srw_tac [][] >>
unabbrev_all_tac >>
fsrw_tac [][morphism_component_equality] >>
fsrw_tac [][ComposeFun_def] >>
fsrw_tac [][restrict_def,explode_def] >>
srw_tac [][FUN_EQ_THM] >>
fsrw_tac [][IsTypedFun_def,HasFunType_def,In_zfrep_thm] >>
srw_tac [][] >>
res_tac >>
fsrw_tac [][In_zfrep_thm]);

val rep_functor_dom_cod = Q.store_thm(
"rep_functor_dom_cod",
`∀u. ((rep_functor u).dom = ens_cat u) ∧
     ((rep_functor u).cod = ens_cat {s | IsSmall s})`,
srw_tac [][rep_functor_def])
val _ = export_rewrites["rep_functor_dom_cod"];

val rep_functor_morf = Q.store_thm(
"rep_functor_morf",
`∀u f. f ∈ (ens_cat u).mor ⇒ ((rep_functor u)##f =
TypedGraphFun (explode (zfrep f.dom), explode (zfrep f.cod)) (λz. zfel f.cod (f.map (elzf f.dom z))))`,
srw_tac [][rep_functor_def]);
val _ = export_rewrites["rep_functor_morf"];

val rep_functor_objf = Q.store_thm(
"rep_functor_objf",
`∀u x. IsSmall x ∧ x ∈ u ⇒ (rep_functor u@@x = explode (zfrep x))`,
srw_tac [][rep_functor_def]);
val _ = export_rewrites["rep_functor_objf"];

val rep_functor_embedding = Q.store_thm(
"rep_functor_embedding",
`∀u. (∀s. s ∈ u ⇒ IsSmall s) ⇒ embedding (rep_functor u)`,
srw_tac [][embedding_def,full_def,faithful_def] >- (
  qmatch_abbrev_tac `X` >>
  qpat_assum `a ∈ u` assume_tac >>
  qpat_assum `b ∈ u` assume_tac >>
  res_tac >> fsrw_tac [][] >>
  qpat_assum `IsTypedFun h` mp_tac >>
  asm_simp_tac (srw_ss()) [IsTypedFun_def] >>
  asm_simp_tac (srw_ss()++DNF_ss) [HasFunType_def,explode_def,In_zfrep_thm] >>
  srw_tac [][GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  qunabbrev_tac `X` >>
  qexists_tac `TypedGraphFun (a,b) f` >>
  fsrw_tac [][morphism_component_equality] >>
  srw_tac [][restrict_def] >>
  srw_tac [][FUN_EQ_THM] >>
  fsrw_tac [][extensional_def] >>
  fsrw_tac [][explode_def] >>
  fsrw_tac [][In_zfrep_thm] >>
  srw_tac [][] >> fsrw_tac [][] >>
  metis_tac [elzf_zfel] ) >>
`g ∈ (ens_cat u).mor ∧ h ∈ (ens_cat u).mor` by (
  fsrw_tac [][] ) >>
fsrw_tac [][TypedGraphFun_Ext,explode_def,IsTypedFun_def,HasFunType_def] >>
srw_tac [][] >>
srw_tac [][morphism_component_equality] >>
fsrw_tac [][extensional_def] >>
srw_tac [][FUN_EQ_THM] >>
reverse (Cases_on `x ∈ g.dom`) >- metis_tac [] >>
res_tac >> fsrw_tac [DNF_ss][In_zfrep_thm] >>
`zfel g.cod (g.map x) = zfel g.cod (h.map (elzf g.dom (zfel g.dom x)))` by metis_tac [] >>
qpat_assum  `IsSmall g.dom` assume_tac >>
qpat_assum `x ∈ g.dom` assume_tac >>
fsrw_tac [][elzf_zfel] >>
`elzf g.cod (zfel g.cod (g.map x)) = elzf g.cod (zfel g.cod (h.map x))` by metis_tac [] >>
qpat_assum  `IsSmall g.cod` assume_tac >>
`g.map x ∈ g.cod ∧ h.map x ∈ g.cod` by metis_tac [] >>
qpat_assum `g.map x ∈ g.cod` assume_tac >>
fsrw_tac [][elzf_zfel]);

(*
val rep_functor_inj_obj = Q.store_thm(
"rep_functor_inj_obj",
`∀u. (∀s. s ∈ u ⇒ IsSmall s) ⇒ inj_obj (rep_functor u)`,
srw_tac [][inj_obj_def] >>
pop_assum mp_tac >> srw_tac [][] >>
imp_res_tac explode_inj >>
match_mp_tac the_zfrep_inj >>
fsrw_tac [][PAIR_FST_SND_EQ] >>
srw_tac [][FUN_EQ_THM] >>
WOULD NEED zfrep TO BE INJECTIVE
*)

(*
val rep_functor_not_inj_obj = Q.store_thm(
"rep_functor_not_inj_obj",
`let u = POW (UNIV:zfset set) in
  (∀s. s ∈ u ⇒ IsSmall s) ∧
  ¬inj_obj (rep_functor u)`,
srw_tac [][LET_THM,IN_POW]
*)

val is_self_hom_def = Define`
  is_self_hom c h = ∃x. x ∈ c.obj ∧ (h = c|x→x|)`;

val hom_tag_def = Define`
  hom_tag c h = if is_self_hom c h then {{{}}} else ({{}}:zfset)`;

val the_hom_tag_def = Define`
  the_hom_tag c h = if is_self_hom c h then {{}} else Empty`;

val hom_tag_not_empty = Q.store_thm(
"hom_tag_not_empty",
`∀c x. hom_tag c x <> {}`,
srw_tac [][hom_tag_def] >>
metis_tac [NotEmpty,InSing]);
val _ = export_rewrites["hom_tag_not_empty"];

val the_hom_tag_in_hom_tag = Q.store_thm(
"the_hom_tag_in_hom_tag",
`∀c h. the_hom_tag c h In hom_tag c h`,
srw_tac [][hom_tag_def,the_hom_tag_def,InSing]);
val _ = export_rewrites["the_hom_tag_in_hom_tag"];

val In_hom_tag = Q.store_thm(
"In_hom_tag",
`∀x c h. x In hom_tag c h = (x = the_hom_tag c h)`,
srw_tac [][EQ_IMP_THM] >>
fsrw_tac [][hom_tag_def,the_hom_tag_def] >>
Cases_on `is_self_hom c h` >> fsrw_tac [][InSing]);
val _ = export_rewrites["In_hom_tag"];

val tagged_homset_def = Define`
  tagged_homset c h = (hom_tag c h) # (ens_to_set@@((rep_functor (homs c))@@h))`;

val tag_fun_def = Define`
  tag_fun c f x = Pair (the_hom_tag c f.cod)
                       ((ens_to_set##((rep_functor (homs c))##f)).map ' (Snd x))`;

val HasFnType_tag_fun = Q.store_thm(
"HasFnType_tag_fun",
`∀c f a b. f ∈ (ens_cat (homs c)).mor ∧ is_lscat c ∧ (a = tagged_homset c f.dom) ∧ (b = tagged_homset c f.cod) ⇒
  HasFnType (tag_fun c f) a b`,
srw_tac [][HasFnType_def] >>
srw_tac [][tagged_homset_def,InProdEq] >>
fsrw_tac [][tag_fun_def,PairEq] >>
`IsSmall f.cod` by ( fsrw_tac [][is_locally_small_def] ) >>
srw_tac [][In_zfrep_thm] >>
fsrw_tac [][tagged_homset_def,InProdEq,Snd] >>
`IsSmall f.dom` by ( fsrw_tac [][is_locally_small_def] ) >>
qpat_assum `x2 In X` mp_tac >>
srw_tac [][In_zfrep_thm] >>
qexists_tac `f.map x` >>
fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
qmatch_abbrev_tac `(ens_to_set##gg).map ' A = B` >>
`gg ∈ (ens_cat {s | IsSmall s}).mor` by (
  srw_tac [][Abbr`gg`] >>
  pop_assum mp_tac >>
  fsrw_tac [][explode_def,In_zfrep_thm] >>
  fsrw_tac [][is_locally_small_def] >>
  metis_tac [elzf_zfel] ) >>
srw_tac [][] >>
`A ∈ explode (zfrep f.dom)` by (
  srw_tac [][explode_def,In_zfrep_thm,Abbr`A`] >>
  metis_tac [] ) >>
`A In (implode gg.dom)` by (
  srw_tac [][In_implode,Abbr`gg`] ) >>
srw_tac [][GraphFnAp] >>
srw_tac [][Abbr`gg`,restrict_def] >>
srw_tac [][Abbr`A`,elzf_zfel]);

val tag_fun_comp = Q.store_thm(
"tag_fun_comp",
`∀c f g x. is_lscat c ∧ (f ≈> g -:(ens_cat (homs c))) ∧ (x In tagged_homset c f.dom)
⇒ (tag_fun c (g o f) x = tag_fun c g (tag_fun c f x))`,
srw_tac [][] >>
`IsSmall f.dom ∧ IsSmall f.cod ∧ IsSmall g.dom ∧ IsSmall g.cod` by (
  fsrw_tac [][is_locally_small_def] ) >>
full_simp_tac std_ss [tag_fun_def,PairEq,Snd,ComposeTypedFun_components,composable_def] >>
`ens_to_set##(rep_functor (homs c)##f) ≈> ens_to_set##(rep_functor (homs c)##g) -:ens_to_set.cod` by (
  match_mp_tac morf_composable >>
  srw_tac [][] >>
  pop_assum mp_tac >>
  srw_tac [][explode_def,In_zfrep_thm] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
  metis_tac [] ) >>
`(g o f) ∈ (ens_cat (homs c)).mor` by (
  srw_tac [][] >> fsrw_tac [][IsTypedFun_def] ) >>
qmatch_abbrev_tac `(ens_to_set##ff).map ' Snd x = (ens_to_set##gg).map ' ((ens_to_set##hh).map ' Snd x)` >>
`(ff.dom = hh.dom) ∧ (ff.cod = gg.cod)` by (
  unabbrev_all_tac >> srw_tac [][] ) >>
`ff ∈ (ens_cat {s | IsSmall s}).mor ∧
 hh ∈ (ens_cat {s | IsSmall s}).mor ∧
 gg ∈ (ens_cat {s | IsSmall s}).mor` by (
  unabbrev_all_tac >> fsrw_tac [][] >>
  srw_tac [][explode_def,In_zfrep_thm] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def,ComposeFun_def,restrict_def] >>
  metis_tac [elzf_zfel] ) >>
`Snd x ∈ explode (zfrep f.dom)` by (
  fsrw_tac [][tagged_homset_def,InProdEq,Snd] >>
  qpat_assum `f.dom ∈ homs c` assume_tac >>
  fsrw_tac [][] >>
  srw_tac [][explode_def] ) >>
`(ens_to_set##gg).map ' ((ens_to_set##hh).map ' Snd x) =
 ((ens_to_set##gg) |o| (ens_to_set##hh)).map ' Snd x` by (
   fsrw_tac [][composable_in_def] >>
   fsrw_tac [][ComposeGraphFns] >>
   `Snd x In (implode hh.dom)` by (
     srw_tac [][In_implode,Abbr`hh`] ) >>
   srw_tac [][GraphFnAp] >>
   `hh.map (Snd x) In (implode gg.dom)` by (
     fsrw_tac [][HasFnType_def] >>
     metis_tac [In_implode] ) >>
   fsrw_tac [][GraphFnAp] ) >>
full_simp_tac std_ss [] >>
AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
unabbrev_all_tac >>
qmatch_abbrev_tac `f1##(f2##gof) = (f1##(f2##g)) |o| (f1##(f2##f))` >>
`f1##(f2##gof) = (f1 ◎ f2)##gof` by (
  match_mp_tac (GSYM functor_comp_morf) >>
  unabbrev_all_tac >> srw_tac [][] ) >>
`f1##(f2##g) = (f1 ◎ f2)##g` by (
  match_mp_tac (GSYM functor_comp_morf) >>
  unabbrev_all_tac >> srw_tac [][] ) >>
`f1##(f2##f) = (f1 ◎ f2)##f` by (
  match_mp_tac (GSYM functor_comp_morf) >>
  unabbrev_all_tac >> srw_tac [][] ) >>
fsrw_tac [][Abbr`gof`] >>
Q.ISPECL_THEN [`f1 ◎ f2`,`(f1 ◎ f2).dom`,`(f1 ◎ f2).cod`,`f`,`g`] mp_tac morf_comp >>
fsrw_tac [][] >>
`is_functor (f1 ◎ f2)` by (
  unabbrev_all_tac >>
  match_mp_tac is_functor_comp >>
  srw_tac [][] >>
  fsrw_tac [][is_locally_small_def] >>
  match_mp_tac is_functor_rep_functor >>
  srw_tac [][] ) >>
fsrw_tac [][] >>
`f2 ≈> f1` by (
  unabbrev_all_tac >> srw_tac [][] ) >>
fsrw_tac [][] >>
`f ≈> g -:f2.dom` by (
  unabbrev_all_tac >> srw_tac [][] ) >>
fsrw_tac [][] >>
`g o f -:f2.dom = g o f` by (
  unabbrev_all_tac >> srw_tac [][] ) >>
fsrw_tac [][] >>
`f1.cod = set_cat` by srw_tac [][Abbr`f1`] >>
fsrw_tac [][]);

val pre_tag_functor_def = Define`
  pre_tag_functor c = <|
    dom := ens_cat (homs c);
    cod := set_cat ;
    map := λf. TypedGraphFn (tagged_homset c f.dom, tagged_homset c f.cod) (tag_fun c f) |>`;

val pre_tag_functor_dom_cod = Q.store_thm(
"pre_tag_functor_dom_cod",
`∀c. ((pre_tag_functor c).dom = ens_cat (homs c)) ∧
     ((pre_tag_functor c).cod = set_cat)`,
srw_tac [][pre_tag_functor_def]);
val _ = export_rewrites["pre_tag_functor_dom_cod"];

val pre_tag_functor_morf = Q.store_thm(
"pre_tag_functor_morf",
`∀c f. (pre_tag_functor c)##f = TypedGraphFn (tagged_homset c f.dom, tagged_homset c f.cod) (tag_fun c f)`,
srw_tac [][pre_tag_functor_def,morf_def]);
val _ = export_rewrites["pre_tag_functor_morf"];

val pre_tag_functor_objf = Q.store_thm(
"pre_tag_functor_objf",
`∀c x. is_lscat c ∧ x ∈ homs c ⇒ ((pre_tag_functor c)@@x = tagged_homset c x)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
conj_tac >- (
  qexists_tac `tagged_homset c x` >>
  srw_tac [][morphism_component_equality] >>
  match_mp_tac GraphFnExt >>
  fsrw_tac [DNF_ss][tag_fun_def,tagged_homset_def,InProdEq] >>
  rpt strip_tac >>
  fsrw_tac [][PairEq] >>
  fsrw_tac [][Snd] >>
  qmatch_abbrev_tac `(ens_to_set##f).map ' x2 = x2` >>
  `IsSmall x` by (
    fsrw_tac [][is_locally_small_def] ) >>
  `f ∈ (ens_cat {s | IsSmall s}).mor` by (
    srw_tac [][Abbr`f`] >>
    qpat_assum `IsSmall x` assume_tac >>
    fsrw_tac [][explode_def,In_zfrep_thm] >>
    srw_tac [][restrict_def] >>
    metis_tac [] ) >>
  srw_tac [][] >>
  qpat_assum `x ∈ homs c` assume_tac >>
  `x2 In implode f.dom` by (
    fsrw_tac [][Abbr`f`,explode_def] ) >>
  fsrw_tac [][GraphFnAp,Abbr`f`] >>
  srw_tac [][restrict_def] >>
  fsrw_tac [][In_zfrep_thm,explode_def] >>
  qpat_assum `x2 In zfrep x` mp_tac >>
  srw_tac [][In_zfrep_thm] >>
  metis_tac [elzf_zfel] ) >>
srw_tac [][morphism_component_equality]);
val _ = export_rewrites["pre_tag_functor_objf"];

val tag_functor_def = Define`
  tag_functor c = mk_functor (pre_tag_functor c)`;

val is_functor_tag_functor = Q.store_thm(
"is_functor_tag_functor",
`∀c. is_lscat c ⇒ is_functor (tag_functor c)`,
srw_tac [][tag_functor_def] >>
fsrw_tac [][functor_axioms_def] >>
conj_tac >- (
  srw_tac [][] >>
  match_mp_tac HasFnType_tag_fun >>
  srw_tac [][] ) >>
conj_tac >- (
  srw_tac [][morphism_component_equality] >>
  match_mp_tac GraphFnExt >>
  fsrw_tac [DNF_ss][tag_fun_def,tagged_homset_def,InProdEq] >>
  rpt strip_tac >>
  fsrw_tac [][PairEq] >>
  fsrw_tac [][Snd] >>
  qmatch_abbrev_tac `(ens_to_set##f).map ' x2 = x2` >>
  `IsSmall x` by (
    fsrw_tac [][is_locally_small_def] ) >>
  `f ∈ (ens_cat {s | IsSmall s}).mor` by (
    srw_tac [][Abbr`f`] >>
    qpat_assum `IsSmall x` assume_tac >>
    fsrw_tac [][explode_def,In_zfrep_thm] >>
    srw_tac [][restrict_def] >>
    metis_tac [] ) >>
  srw_tac [][] >>
  qpat_assum `x ∈ homs c` assume_tac >>
  `x2 In implode f.dom` by (
    fsrw_tac [][Abbr`f`,explode_def] ) >>
  fsrw_tac [][GraphFnAp,Abbr`f`] >>
  srw_tac [][restrict_def] >>
  fsrw_tac [][In_zfrep_thm,explode_def] >>
  qpat_assum `x2 In zfrep x` mp_tac >>
  srw_tac [][In_zfrep_thm] >>
  metis_tac [elzf_zfel] ) >>
srw_tac [][] >>
qmatch_abbrev_tac `ff = gg o hh -:set_cat` >>
`hh ≈> gg -:set_cat` by (
  srw_tac [][Abbr`hh`,Abbr`gg`] >>
  srw_tac [][HasFnType_tag_fun] ) >>
srw_tac [][Abbr`ff`,Abbr`gg`,Abbr`hh`,morphism_component_equality] >>
qmatch_abbrev_tac `ff = ComposeFn (X,Y,Z) (GraphFn Y gg) (GraphFn X hh)` >>
`HasFnType hh X Y ∧ HasFnType gg Y Z` by (
  srw_tac [][Abbr`gg`,Abbr`hh`,HasFnType_tag_fun] ) >>
srw_tac [][ComposeGraphFns,Abbr`ff`] >>
match_mp_tac GraphFnExt >>
srw_tac [][Abbr`gg`,Abbr`hh`] >>
match_mp_tac tag_fun_comp >>
unabbrev_all_tac >>
srw_tac [][]);
val _ = export_rewrites["is_functor_tag_functor"];

val tag_functor_dom_cod = Q.store_thm(
"tag_functor_dom_cod",
`∀c. ((tag_functor c).dom = ens_cat (homs c)) ∧
     ((tag_functor c).cod = set_cat)`,
srw_tac [][tag_functor_def]);
val _ = export_rewrites["tag_functor_dom_cod"];

val tag_functor_morf = Q.store_thm(
"tag_functor_morf",
`∀c f. f ∈ (ens_cat (homs c)).mor ⇒ ((tag_functor c)##f = TypedGraphFn (tagged_homset c f.dom, tagged_homset c f.cod) (tag_fun c f))`,
srw_tac [][tag_functor_def]);
val _ = export_rewrites["tag_functor_morf"];

val tag_functor_objf = Q.store_thm(
"tag_functor_objf",
`∀c x. is_lscat c ∧ x ∈ homs c ⇒ (tag_functor c@@x = tagged_homset c x)`,
srw_tac [][tag_functor_def]);
val _ = export_rewrites["tag_functor_objf"];

val tag_functor_embedding = Q.store_thm(
"tag_functor_embedding",
`∀c. is_lscat c ⇒ embedding (tag_functor c)`,
srw_tac [][] >>
`embedding (ens_to_set ◎ (rep_functor (homs c)))` by (
  match_mp_tac embedding_functor_comp >>
  fsrw_tac [][is_locally_small_def] >>
  conj_tac >- (
    match_mp_tac is_functor_rep_functor >>
    srw_tac [][] ) >>
  match_mp_tac rep_functor_embedding >>
  srw_tac [][]) >>
fsrw_tac [][embedding_def] >>
conj_tac >- (
  fsrw_tac [][full_def] >>
  map_every qx_gen_tac [`h`,`a`,`b`] >>
  strip_tac >>
  rpt (qpat_assum `X = tag_functor c@@Y` mp_tac) >>
  srw_tac [][] >>
  qabbrev_tac `hhdom = (ens_to_set ◎ rep_functor (homs c))@@a` >>
  qabbrev_tac `hhcod = (ens_to_set ◎ rep_functor (homs c))@@b` >>
  qabbrev_tac `hh = TypedGraphFn (hhdom,hhcod) (λx. Snd (h.map ' (Pair (the_hom_tag c a) x)))` >>
  `IsSmall a ∧ IsSmall b` by fsrw_tac [][is_locally_small_def] >>
  `is_functor (rep_functor (homs c))` by (
    match_mp_tac is_functor_rep_functor >>
    fsrw_tac [][is_locally_small_def] ) >>
  `IsTypedFn hh` by (
    srw_tac [][Abbr`hh`] >>
    rpt (qpat_assum `xxx = tagged_homset c yyy` mp_tac) >>
    fsrw_tac [][IsTypedFn_def,tagged_homset_def] >>
    fsrw_tac [][HasFnType_def,Abbr`hhdom`,Abbr`hhcod`] >>
    srw_tac [][] >>
    `h.map ' Pair (the_hom_tag c a) x In ((hom_tag c b) # (zfrep b))` by (
      match_mp_tac InFn >>
      qexists_tac `h.dom` >>
      fsrw_tac [][] >>
      srw_tac [][GSYM InProd] ) >>
    fsrw_tac [][InProdEq,Snd] ) >>
  first_x_assum (qspecl_then [`hh`,`a`,`b`] mp_tac) >>
  fsrw_tac [][Abbr`hh`] >>
  strip_tac >>
  qexists_tac `g` >>
  srw_tac [][morphism_component_equality] >>
  pop_assum mp_tac >> srw_tac [][] >>
  qmatch_assum_abbrev_tac `(ens_to_set##ff=yy)` >>
  `ff ∈ (ens_cat {s | IsSmall s}).mor` by (
    srw_tac [][Abbr`ff`] >>
    fsrw_tac [][explode_def,Abbr`hhdom`,Abbr`hhcod`] >>
    pop_assum mp_tac >>
    srw_tac [][In_zfrep_thm] >>
    fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
    metis_tac [] ) >>
  fsrw_tac [][] >>
  unabbrev_all_tac >>
  fsrw_tac [][morphism_component_equality] >>
  match_mp_tac FnEqThm >>
  map_every qexists_tac [`h.dom`,`h.cod`] >>
  fsrw_tac [][IsTypedFn_def] >>
  conj_tac >- (
    match_mp_tac GraphFnType >>
    match_mp_tac HasFnType_tag_fun >>
    fsrw_tac [][] ) >>
  srw_tac [][tagged_homset_def,GraphFnAp] >>
  srw_tac [][tag_fun_def] >>
  `h.map ' x In tagged_homset c g.cod` by (
    match_mp_tac InFn >>
    fsrw_tac [][tagged_homset_def] >>
    metis_tac [] ) >>
  pop_assum mp_tac >>
  srw_tac [][InProdEq,tagged_homset_def] >>
  fsrw_tac [][PairEq] >>
  fsrw_tac [][InProdEq,Snd] >>
  srw_tac [][GraphFnAp,Snd] ) >>
fsrw_tac [][faithful_def] >>
srw_tac [][] >>
first_x_assum match_mp_tac >>
srw_tac [][] >>
qmatch_abbrev_tac `ens_to_set##f1 = ens_to_set##f2` >>
`IsSmall g.dom ∧ IsSmall g.cod` by fsrw_tac [][is_locally_small_def] >>
`f1 ∈ (ens_cat {s | IsSmall s}).mor` by (
  srw_tac [][Abbr`f1`] >>
  rpt (qpat_assum `IsSmall X` mp_tac) >>
  rpt strip_tac >>
  fsrw_tac [][explode_def,In_zfrep_thm] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
  metis_tac [] ) >>
`f2 ∈ (ens_cat {s | IsSmall s}).mor` by (
  srw_tac [][Abbr`f2`] >>
  rpt (qpat_assum `IsSmall X` mp_tac) >>
  rpt strip_tac >>
  fsrw_tac [][explode_def,In_zfrep_thm] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
  metis_tac [] ) >>
srw_tac [][] >>
srw_tac [][Abbr`f1`,Abbr`f2`,morphism_component_equality] >>
match_mp_tac GraphFnExt >>
srw_tac [][In_zfrep_thm] >>
srw_tac [][restrict_def] >>
`g ∈ (ens_cat (homs c)).mor` by srw_tac [][] >>
`h ∈ (ens_cat (homs c)).mor` by srw_tac [][] >>
fsrw_tac [][morphism_component_equality] >>
qmatch_rename_tac `zfel g.cod (g.map z) = zfel g.cod (h.map z)` [] >>
`GraphFn (tagged_homset c g.dom) (tag_fun c g) ' (Pair (the_hom_tag c g.dom) (zfel g.dom z)) =
 GraphFn (tagged_homset c h.dom) (tag_fun c h) ' (Pair (the_hom_tag c h.dom) (zfel h.dom z))`
by metis_tac [] >>
qpat_assum `GraphFn X Y = Z` (K ALL_TAC) >>
qmatch_assum_abbrev_tac `GraphFn X f1 ' p1 = GraphFn X2 f2 ' p2` >>
`p1 In X` by (
  unabbrev_all_tac >>
  srw_tac [][tagged_homset_def,InProdEq,In_zfrep_thm,PairEq] >>
  metis_tac [] ) >>
`p2 In X2` by (
  unabbrev_all_tac >>
  srw_tac [][tagged_homset_def,InProdEq,In_zfrep_thm,PairEq] >>
  metis_tac [] ) >>
fsrw_tac [][GraphFnAp] >>
unabbrev_all_tac >>
fsrw_tac [][tag_fun_def,PairEq,Snd] >>
qpat_assum `X ' w = Y ' w2` mp_tac >>
fsrw_tac [][] >>
`zfel g.dom z In zfrep g.dom` by (
  fsrw_tac [][explode_def,In_zfrep_thm] ) >>
fsrw_tac [][GraphFnAp,restrict_def])
val _ = export_rewrites["tag_functor_embedding"];

val zYfunctor_def = Define`
  zYfunctor c = (postcomp_functor (c°) (tag_functor c)) ◎ Yfunctor c`

val is_functor_zYfunctor = Q.store_thm(
"is_functor_zYfunctor",
`∀c. is_lscat c ⇒ is_functor (zYfunctor c)`,
srw_tac [][] >>
fsrw_tac [][zYfunctor_def] >>
match_mp_tac is_functor_comp >>
conj_tac >- srw_tac [][is_functor_Yfunctor] >>
conj_tac >- (
  match_mp_tac is_functor_postcomp_functor >>
  srw_tac [][] ) >>
srw_tac [][]);
val _ = export_rewrites["is_functor_zYfunctor"];

val zYfunctor_dom_cod = Q.store_thm(
"zYfunctor_dom_cod",
`∀c. ((zYfunctor c).dom = c) ∧
     ((zYfunctor c).cod = [(c°)→set_cat])`,
srw_tac [][zYfunctor_def]);
val _ = export_rewrites["zYfunctor_dom_cod"];

val zYfunctorEmbedding = Q.store_thm(
"zYfunctorEmbedding",
`∀c. is_lscat c ⇒ embedding (zYfunctor c)`,
srw_tac [][zYfunctor_def] >>
match_mp_tac embedding_functor_comp >>
fsrw_tac [][is_functor_Yfunctor,YonedaEmbedding] >>
match_mp_tac embedding_functor_cats >>
srw_tac [][]);

val zYfunctorInjObj = Q.store_thm(
"zYfunctorInjObj",
`∀c. is_lscat c ⇒ inj_obj (zYfunctor c)`,
srw_tac [][zYfunctor_def] >>
srw_tac [][inj_obj_def] >>
qmatch_assum_abbrev_tac `(f ◎ g)@@a = (f ◎ g)@@b` >>
`is_functor f ∧ is_functor g ∧ (g ≈> f) ∧ a ∈ g.dom.obj ∧ b ∈ g.dom.obj` by (
  unabbrev_all_tac >> fsrw_tac [][is_functor_Yfunctor] ) >>
qpat_assum `is_category c` assume_tac >>
fsrw_tac [][Abbr`g`,Yfunctor_objf] >>
`(c|_→a|) ∈ [(c°)→(tag_functor c).dom].obj` by (
  srw_tac [][] ) >>
`(c|_→b|) ∈ [(c°)→(tag_functor c).dom].obj` by (
  srw_tac [][] ) >>
`is_functor (tag_functor c)` by srw_tac [][] >>
full_simp_tac std_ss [Abbr`f`,is_category_op_cat,postcomp_functor_objf] >>
`(tag_functor c ◎ (c|_→a|))@@a = (tag_functor c ◎ (c|_→b|))@@a` by metis_tac [] >>
qpat_assum `tag_functor c ◎ X = Y` (K ALL_TAC) >>
pop_assum mp_tac >> srw_tac [][tagged_homset_def,ProdEq] >- (
  fsrw_tac [][ProdEmpty] >>
  rpt (qpat_assum `X = {}` mp_tac) >>
  `IsSmall (c|a→a|) ∧ (c|a→a|) ∈ homs c` by (
    fsrw_tac [][homs_def,is_locally_small_def,LET_THM] >>
    metis_tac [] ) >>
  fsrw_tac [][hom_def,EXTENSION] >>
  metis_tac [id_maps_to] ) >>
qpat_assum `hom_tag c X = Y` mp_tac >>
fsrw_tac [][hom_tag_def] >>
`is_self_hom c (c|a→a|)` by (
  srw_tac [][is_self_hom_def] >>
  metis_tac [] ) >>
`{{{}}} <> {Empty}` by (
  srw_tac [][Extension_ax,InSing,Empty_def] >>
  metis_tac [Empty_def] ) >>
srw_tac [][] >>
fsrw_tac [][is_self_hom_def] >>
fsrw_tac [][hom_def,EXTENSION] >>
qmatch_assum_rename_tac `!x. x :- a → b -:c = x :- z → z -:c` [] >>
`id z -: c :- z → z -:c` by metis_tac [id_maps_to] >>
`id z -: c :- a → b -:c` by metis_tac [] >>
fsrw_tac [][maps_to_in_def]);

val _ = export_theory ();
