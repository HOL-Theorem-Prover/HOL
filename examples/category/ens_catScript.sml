open HolKernel Parse boolLib boolSimps bossLib SatisfySimps categoryTheory functorTheory pred_setTheory limitTheory lcsymtacs;

val _ = new_theory "ens_cat";

val HasFunType_def = Define`
  HasFunType f X Y = extensional f X ∧ ∀x. x ∈ X ⇒ f x ∈ Y`;

val IsTypedFun_def = Define`
  IsTypedFun f = HasFunType f.map f.dom f.cod`;

val TypedFun_ext = Q.store_thm(
"TypedFun_ext",
`∀f g. IsTypedFun f ∧ IsTypedFun g ⇒
  ((f = g) = ((f.dom = g.dom) ∧ (f.cod = g.cod) ∧ (∀x. x ∈ f.dom ⇒ (f.map x = g.map x))))`,
srw_tac [][morphism_component_equality,IsTypedFun_def,HasFunType_def,extensional_def] >>
srw_tac [][EQ_IMP_THM] >>
srw_tac [][FUN_EQ_THM] >>
Cases_on `x ∈ f.dom` >> srw_tac [][] >>
pop_assum mp_tac >> srw_tac [][]);

val TypedGraphFun_def = Define`
  TypedGraphFun (X,Y) f = <|
    dom := X; cod := Y; map := restrict f X |>`;

val TypedGraphFun_components = Q.store_thm(
"TypedGraphFun_components",
`∀X Y f. ((TypedGraphFun (X,Y) f).dom = X) ∧
         ((TypedGraphFun (X,Y) f).cod = Y) ∧
         ((TypedGraphFun (X,Y) f).map = restrict f X)`,
srw_tac [][TypedGraphFun_def]);
val _ = export_rewrites["TypedGraphFun_components"];

val IsTypedFunTypedGraphFun = Q.store_thm(
"IsTypedFunTypedGraphFun",
`∀f X Y. IsTypedFun (TypedGraphFun (X,Y) f) = ∀x. x ∈ X ⇒ f x ∈ Y`,
srw_tac [][EQ_IMP_THM,IsTypedFun_def,TypedGraphFun_def,HasFunType_def,restrict_def,extensional_def]);
val _ = export_rewrites["IsTypedFunTypedGraphFun"];

val TypedGraphFun_Ext = Q.store_thm(
"TypedGraphFun_Ext",
`∀X Y f X' Y' f'. (TypedGraphFun (X,Y) f = TypedGraphFun (X',Y') f') ⇔ ((X = X') ∧ (Y = Y') ∧ ∀x. x ∈ X ⇒ (f x = f' x))`,
srw_tac [][TypedGraphFun_def,restrict_def,EQ_IMP_THM] >> metis_tac []);

val ComposeFun_def = Define`
  ComposeFun (X,Y) g f = restrict ((restrict g Y) o f) X`;

val ComposeTypedFun_def = Define`
  ComposeTypedFun = compose (λf g. ComposeFun (f.dom,g.dom) g.map f.map)`;

val _ = overload_on("o",``λg f. ComposeTypedFun f g``);
val _ = overload_on("o",``λg f. (combin$o) g f``);

val ComposeTypedFun_components = Q.store_thm(
"ComposeTypedFun_components",
`∀f g. (f ≈> g) ⇒
((g o f).dom = f.dom) ∧
((g o f).cod = g.cod) ∧
((g o f).map = ComposeFun(f.dom,g.dom) g.map f.map)`,
srw_tac [][ComposeTypedFun_def]);
val _ = export_rewrites["ComposeTypedFun_components"];

val IdFun_def = Define`
  IdFun s = restrict I s`;

val IdFunAp = Q.store_thm(
"IdFunAp",
`∀x s. x ∈ s ⇒ (IdFun s x = x)`,
srw_tac [][IdFun_def,restrict_def]);
val _ = export_rewrites["IdFunAp"];

val IdFunType = Q.store_thm(
"IdFunType",
`∀s. HasFunType (IdFun s) s s`,
srw_tac [][HasFunType_def,IdFun_def]);
val _ = export_rewrites["IdFunType"];

val ComposeFunId = Q.store_thm(
"ComposeFunId",
`∀X Y f. HasFunType f X Y ⇒
(ComposeFun (X,X) f (IdFun X) = f) ∧
(ComposeFun (X,Y) (IdFun Y) f = f)`,
srw_tac [][ComposeFun_def,IdFun_def,FUN_EQ_THM,HasFunType_def] >>
fsrw_tac [][restrict_def,extensional_def] >>
metis_tac []);
val _ = export_rewrites["ComposeFunId"];

val ComposeFunAssoc = Q.store_thm(
"ComposeFunAssoc",
`∀a f b g c h ab bc ac.
  HasFunType f a b ∧ HasFunType g b c ∧
  (ab = (a,b)) ∧ (bc = (b,c)) ∧ (ac = (a,c)) ⇒
  (ComposeFun ac h (ComposeFun ab g f) = ComposeFun ab (ComposeFun bc h g) f)`,
srw_tac [][ComposeFun_def,FUN_EQ_THM] >>
fsrw_tac [][HasFunType_def,extensional_def,restrict_def]);
val _ = export_rewrites["ComposeFunAssoc"];

val ComposeFunType = Q.store_thm(
"ComposeFunType",
`∀X f Y g XY Z. HasFunType f X Y ∧ HasFunType g Y Z ∧ (XY = (X,Y)) ⇒ HasFunType (ComposeFun XY g f) X Z`,
srw_tac [][HasFunType_def,ComposeFun_def] >>
fsrw_tac [][extensional_def,restrict_def]);
val _ = export_rewrites["ComposeFunType"];

val _ = overload_on("IsTypedFunIn",``λU f. f.dom ∈ U ∧ f.cod ∈ U ∧ IsTypedFun f``);

val ens_cat_def = Define`
  ens_cat U = mk_cat <|
    obj := U ;
    mor := {f | IsTypedFunIn U f} ;
    id_map := IdFun ;
    comp := λf g. (g o f).map |>`;

val is_category_ens_cat = Q.store_thm(
"is_category_ens_cat",
`∀U. is_category (ens_cat U)`,
srw_tac [][ens_cat_def] >>
srw_tac [][category_axioms_def] >- (
  srw_tac [][maps_to_in_def,id_in_def,IsTypedFun_def,restrict_def] )
>- (
  srw_tac [][id_in_def,restrict_def] >>
  srw_tac [][compose_in_def,restrict_def] >>
  fsrw_tac [SATISFY_ss][IsTypedFun_def,morphism_component_equality] >>
  fsrw_tac [][composable_in_def] >> fsrw_tac [][])
>- (
  srw_tac [][id_in_def,restrict_def] >>
  srw_tac [][compose_in_def,restrict_def] >>
  fsrw_tac [SATISFY_ss][IsTypedFun_def,morphism_component_equality] >>
  fsrw_tac [][composable_in_def] >> fsrw_tac [][])
>- (
  fsrw_tac [][compose_in_def,restrict_def] >>
  fsrw_tac [][composable_in_def] >>
  fsrw_tac [][compose_def,restrict_def] >>
  fsrw_tac [][IsTypedFun_def]) >>
fsrw_tac [][maps_to_in_def] >>
fsrw_tac [][compose_in_def,restrict_def,composable_in_def] >>
fsrw_tac [][IsTypedFun_def]);
val _ = export_rewrites["is_category_ens_cat"];

val ens_cat_obj = Q.store_thm(
"ens_cat_obj",
`∀U. (ens_cat U).obj = U`,
srw_tac [][ens_cat_def]);

val ens_cat_mor = Q.store_thm(
"ens_cat_mor",
`∀U f. f ∈ (ens_cat U).mor ⇔ IsTypedFunIn U f`,
srw_tac [][ens_cat_def]);

val ens_cat_id = Q.store_thm(
"ens_cat_id",
`∀U x. x ∈ U ⇒ ((id x -:(ens_cat U)) = TypedGraphFun (x,x) (IdFun x))`,
srw_tac [][id_in_def,ens_cat_def,mk_cat_def,restrict_def,TypedGraphFun_def,IdFun_def]);

val ens_cat_composable_in = Q.store_thm(
"ens_cat_composable_in",
`∀U f g. f ≈> g -:(ens_cat U) ⇔ IsTypedFunIn U f ∧ IsTypedFunIn U g ∧ f ≈> g`,
srw_tac [][composable_in_def,ens_cat_mor]);

val ens_cat_comp = Q.store_thm(
"ens_cat_comp",
`∀U f g. f ≈> g -:(ens_cat U) ⇒ ((ens_cat U).comp f g = ComposeFun(f.dom,g.dom) g.map f.map)`,
srw_tac [][ens_cat_def,mk_cat_def,restrict_def,composable_in_def]);

val ens_cat_compose_in = Q.store_thm(
"ens_cat_compose_in",
`∀U f g. f ≈> g -:(ens_cat U) ⇒ (g o f -:(ens_cat U) = g o f)`,
srw_tac [][compose_in_def,morphism_component_equality,ens_cat_comp,ens_cat_composable_in,restrict_def]>>
metis_tac []);

val ens_cat_maps_to_in = Q.store_thm(
"ens_cat_maps_to_in",
`∀U f x y. f :- x → y -:(ens_cat U) ⇔ IsTypedFunIn U f ∧ f :- x → y`,
srw_tac [][maps_to_in_def,EQ_IMP_THM,ens_cat_mor]);

val _ = export_rewrites[
"ens_cat_obj","ens_cat_mor","ens_cat_id",
"ens_cat_composable_in","ens_cat_comp",
"ens_cat_compose_in","ens_cat_maps_to_in"];

val ens_cat_empty_terminal = Q.store_thm(
"ens_cat_empty_terminal",
`∀U. is_terminal (ens_cat U) ∅ = ∅ ∈ U ∧ ∀x. x ∈ U ⇒ (x = ∅)`,
srw_tac [][is_terminal_def,EQ_IMP_THM,EXISTS_UNIQUE_THM] >- (
  first_x_assum (qspec_then `x` mp_tac) >>
  srw_tac [][] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def,EXTENSION] )
>- (
  qexists_tac `TypedGraphFun (∅,∅) ARB` >>
  srw_tac [][] ) >>
srw_tac [][TypedFun_ext]);

val ens_cat_terminal_objects = Q.store_thm(
"ens_cat_terminal_objects",
`∀U t. (∃s. s ∈ U ∧ s ≠ ∅) ⇒
  (is_terminal (ens_cat U) t = ∃x. (t = {x}) ∧ t ∈ U)`,
srw_tac [][is_terminal_def,EQ_IMP_THM,EXISTS_UNIQUE_THM] >>
srw_tac [][] >- (
  srw_tac [][EXTENSION] >>
  Cases_on `t = {}` >- (
    first_x_assum (qspec_then `s` mp_tac) >>
    srw_tac [][] >>
    disj1_tac >>
    srw_tac [][] >>
    Cases_on `f.dom = s` >> srw_tac [][] >>
    Cases_on `f.cod = ∅` >> srw_tac [][] >>
    srw_tac [][IsTypedFun_def,HasFunType_def,MEMBER_NOT_EMPTY] ) >>
  qexists_tac `CHOICE t` >>
  srw_tac [][EQ_IMP_THM,CHOICE_DEF] >>
  first_x_assum (qspec_then `t` mp_tac) >>
  srw_tac [][] >>
  qmatch_assum_rename_tac `x ∈ f.cod` [] >>
  first_x_assum (qspecl_then [`TypedGraphFun (f.dom,f.cod) (K x)`,`TypedGraphFun (f.dom,f.cod) (K (CHOICE f.cod))`] mp_tac) >>
  srw_tac [][CHOICE_DEF] >>
  fsrw_tac [][morphism_component_equality,restrict_def] >>
  qmatch_assum_abbrev_tac `ff = gg` >>
  `ff x = gg x` by srw_tac [][] >>
  pop_assum mp_tac >>
  unabbrev_all_tac >>
  qpat_assum `x ∈ f.cod` mp_tac >>
  simp_tac std_ss [] )
>- (
  qmatch_assum_rename_tac `y ∈ U` [] >>
  qexists_tac `TypedGraphFun (y,{x}) (K x)` >>
  srw_tac [][] ) >>
srw_tac [][TypedFun_ext] >>
rpt (qpat_assum `IsTypedFun X` mp_tac) >>
fsrw_tac [][IsTypedFun_def,HasFunType_def]);

(*
val ens_cat_has_binary_products = Q.store_thm(
"ens_cat_has_binary_products",
`∀U J. (INJ J {{(x,y) | x ∈ a ∧ y ∈ b} | a ∈ U ∧ b ∈ U} U) ⇒ has_binary_products (ens_cat U)`,
srw_tac [][has_binary_products_thm,is_binary_product_thm] >>
`J {(x,y) | x ∈ a ∧ y ∈ b} ∈ U` by fsrw_tac [DNF_ss][INJ_DEF] >>
qmatch_assum_abbrev_tac `J axb ∈ U` >>
qmatch_assum_abbrev_tac `INJ J UU U` >>
qexists_tac `TypedGraphFun (J axb, a) (λp. (LINV J UU axb)` >>
LINV_DEF
srw_tac [][]
``TypedGraphFun ((J:('a # 'a set -> 'a set)) (a,b), a)``
``(LINV (J:(('a # 'a) set -> 'a set)) UU)``
type_of it
*)

val pre_inclusion_functor_def = Define`
  pre_inclusion_functor u1 u2 = <|
    dom := ens_cat u1;
    cod := ens_cat u2;
    map := I|>`;

val pre_inclusion_functor_components = Q.store_thm(
"pre_inclusion_functor_components",
`∀u1 u2. ((pre_inclusion_functor u1 u2).dom = ens_cat u1) ∧
         ((pre_inclusion_functor u1 u2).cod = ens_cat u2) ∧
         (∀f. f ∈ (ens_cat u1).mor ⇒ ((pre_inclusion_functor u1 u2)##f = f)) ∧
         (∀x. x ∈ u1 ∧ x ∈ u2 ⇒ ((pre_inclusion_functor u1 u2)@@x = x))`,
srw_tac [][pre_inclusion_functor_def,morf_def,objf_def] >>
SELECT_ELIM_TAC >>
conj_tac >- ( qexists_tac `x` >> srw_tac [][] ) >>
srw_tac [][] >>
pop_assum mp_tac >>
fsrw_tac [][morphism_component_equality]);
val _ = export_rewrites["pre_inclusion_functor_components"];

val inclusion_functor_def = Define`
  inclusion_functor u1 u2 = mk_functor (pre_inclusion_functor u1 u2)`;

val inclusion_functor_components = Q.store_thm(
"inclusion_functor_components",
`∀u1 u2. ((inclusion_functor u1 u2).dom = ens_cat u1) ∧
         ((inclusion_functor u1 u2).cod = ens_cat u2) ∧
         (∀f. f ∈ (ens_cat u1).mor ⇒ ((inclusion_functor u1 u2)##f = f)) ∧
         (∀x. x ∈ u1 ∧ x ∈ u2 ⇒ ((inclusion_functor u1 u2)@@x = x))`,
srw_tac [][inclusion_functor_def]);
val _ = export_rewrites["inclusion_functor_components"];

val is_functor_inclusion_functor = Q.store_thm(
"is_functor_inclusion_functor",
`∀u1 u2. u1 ⊆ u2 ⇒ is_functor (inclusion_functor u1 u2)`,
srw_tac [][inclusion_functor_def] >>
srw_tac [][functor_axioms_def] >>
fsrw_tac [][SUBSET_DEF] >- (
  qexists_tac `x` >> srw_tac [][] ) >>
`(g o f) ∈ (ens_cat u1).mor` by (
  srw_tac [][] >> fsrw_tac [][IsTypedFun_def] ) >>
srw_tac [][]);
val _ = export_rewrites["is_functor_inclusion_functor"];

val _ = export_theory();
