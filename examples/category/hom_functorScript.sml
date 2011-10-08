open HolKernel Parse boolLib boolSimps bossLib pred_setTheory categoryTheory functorTheory ens_catTheory lcsymtacs;

val _ = new_theory "hom_functor";

val dom_homs_def = Define`
  dom_homs c x = IMAGE (λy. c|x→y|) c.obj`;

val cod_homs_def = Define`
  cod_homs c x = IMAGE (λy. c|y→x|) c.obj`;

val homs_def = Define`
  homs c = let ob = c.obj in {(c|x→y|)| x ∈ ob ∧ y ∈ ob}`;

val dom_homs_subset_homs = Q.store_thm(
"dom_homs_subset_homs",
`∀c x. x ∈ c.obj ⇒ dom_homs c x ⊆ homs c`,
srw_tac [][dom_homs_def,homs_def,SUBSET_DEF] >>
srw_tac [][] >> metis_tac []);
val _ = export_rewrites["dom_homs_subset_homs"];

val hom_in_dom_homs = Q.store_thm(
"hom_in_dom_homs",
`∀c x y. y ∈ c.obj ⇒ (c|x→y|) ∈ dom_homs c x`,
srw_tac [][dom_homs_def] >> metis_tac []);
val _ = export_rewrites["hom_in_dom_homs"];

val hom_in_homs = Q.store_thm(
"hom_in_homs",
`∀c x y. x ∈ c.obj ∧ y ∈ c.obj ⇒ (c|x→y|) ∈ homs c`,
srw_tac [][homs_def] >>
srw_tac [][] >> metis_tac []);
val _ = export_rewrites["hom_in_homs"];

val pre_hom_functor_def = Define`
  (pre_hom_functor c x : (α,β,(α,β) mor set, (α,β) mor -> (α,β) mor) functor) = <|
    dom := c ; cod := ens_cat (dom_homs c x) ;
    map := λf. TypedGraphFun ((c|x→f.dom|),(c|x→f.cod|)) (λg. f o g -:c)
  |>`;

val pre_hom_functor_dom = Q.store_thm(
"pre_hom_functor_dom",
`∀c x. (pre_hom_functor c x).dom = c`,
srw_tac [][pre_hom_functor_def]);

val pre_hom_functor_cod = Q.store_thm(
"pre_hom_functor_cod",
`∀c x. (pre_hom_functor c x).cod = ens_cat (dom_homs c x)`,
srw_tac [][pre_hom_functor_def]);

val _ = export_rewrites["pre_hom_functor_cod","pre_hom_functor_dom"];

val pre_hom_functor_morf_dom_cod = Q.store_thm(
"pre_hom_functor_morf_dom_cod",
`∀c x f. (((pre_hom_functor c x)##f).dom = c|x→f.dom|) ∧
         (((pre_hom_functor c x)##f).cod = c|x→f.cod|)`,
srw_tac [][pre_hom_functor_def,morf_def,TypedGraphFun_def]);
val _ = export_rewrites ["pre_hom_functor_morf_dom_cod"];

val pre_hom_functor_morf = Q.store_thm(
"pre_hom_functor_morf",
`∀c x f. (pre_hom_functor c x)##f =
  TypedGraphFun ((c|x→f.dom|), c|x→f.cod|) (λg. f o g -:c)`,
srw_tac [][pre_hom_functor_def,morf_def]);
val _ = export_rewrites["pre_hom_functor_morf"];

val pre_hom_functor_objf = Q.store_thm(
"pre_hom_functor_objf",
`∀c x y. is_category c ∧ x ∈ c.obj ∧ y ∈ c.obj
  ⇒ ((pre_hom_functor c x)@@y = c|x→y|)`,
srw_tac [][objf_def,pre_hom_functor_def] >>
imp_res_tac id_dom_cod >>
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  qexists_tac `c|x→y|` >>
  fsrw_tac [][morphism_component_equality,TypedGraphFun_def] >>
  srw_tac [][restrict_def,FUN_EQ_THM] >> srw_tac [][] >>
  fsrw_tac [][hom_def,maps_to_in_def] ) >>
pop_assum mp_tac >>
fsrw_tac [][TypedGraphFun_def]);
val _ = export_rewrites ["pre_hom_functor_objf"];

val _ = add_rule{
  term_name = "hom_functor",
  fixity=Suffix 620,
  pp_elements=[TOK"|",TM,TOK"\226\134\146_|"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val hom_functor_def = Define`
  c|x→_| = inclusion_functor (dom_homs c x) (homs c) ◎
           mk_functor (pre_hom_functor c x)`;

val functor_axioms_pre_hom_functor = Q.store_thm(
"functor_axioms_pre_hom_functor",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ functor_axioms (pre_hom_functor c x)`,
srw_tac [][functor_axioms_def]
>- (
  match_mp_tac hom_in_dom_homs >>
  fsrw_tac [][maps_to_in_def] )
>- (
  match_mp_tac hom_in_dom_homs >>
  fsrw_tac [][maps_to_in_def] )
>- (
  srw_tac [][hom_def] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `f.dom` >>
  fsrw_tac [][hom_def,maps_to_in_def] )
>- (
  imp_res_tac maps_to_obj >>
  fsrw_tac [][maps_to_in_def] )
>- (
  imp_res_tac maps_to_obj >>
  fsrw_tac [][maps_to_in_def] )
>- (
  qmatch_assum_rename_tac `y ∈ c.obj` [] >>
  qexists_tac `c|x→y|` >>
  srw_tac [][TypedGraphFun_def] >>
  srw_tac [][FUN_EQ_THM,restrict_def] >>
  srw_tac [][] >>
  fsrw_tac [][hom_def,maps_to_in_def] ) >>
qmatch_abbrev_tac `hh = gg o ff -:(ens_cat U)` >>
`ff ≈> gg -:(ens_cat U)` by (
  fsrw_tac [][Abbr`ff`,Abbr`gg`,Abbr`U`,TypedGraphFun_def] >>
  imp_res_tac composable_in_def >> fsrw_tac [][] >>
  fsrw_tac [][hom_def] >>
  metis_tac [maps_to_comp,maps_to_in_dom_cod] ) >>
srw_tac [][] >>
`(ff ≈> gg) ∧ f ≈> g` by (
  imp_res_tac composable_in_def >>
  srw_tac [][] ) >>
srw_tac [][Abbr`ff`,Abbr`gg`,Abbr`hh`] >>
srw_tac [][morphism_component_equality] >>
TRY ( srw_tac [][hom_def,compose_in_def,restrict_def] >> NO_TAC) >>
srw_tac [][ComposeFun_def] >>
srw_tac [][restrict_def,FUN_EQ_THM] >>
srw_tac [][] >- (
  match_mp_tac comp_assoc >>
  fsrw_tac [][hom_def,composable_in_def,maps_to_in_def] ) >>
qsuff_tac `F` >- srw_tac [][] >>
qpat_assum `X ∉ Y` mp_tac >> srw_tac [][] >>
fsrw_tac [][hom_def,comp_mor_dom_cod] >>
pop_assum mp_tac >> srw_tac [][comp_mor_dom_cod]);
val _ = export_rewrites["functor_axioms_pre_hom_functor"];

val is_functor_hom_functor = Q.store_thm(
"is_functor_hom_functor",
`∀c x. is_category c ∧ x ∈ c.obj ⇒ is_functor (c|x→_|)`,
srw_tac [][hom_functor_def]);
val _ = export_rewrites["is_functor_hom_functor"];

val hom_functor_objf = Q.store_thm(
"hom_functor_objf",
`∀c x y. is_category c ∧ x ∈ c.obj ∧ y ∈ c.obj
  ⇒ (objf (hom_functor c x) y = c|x→y|)`,
srw_tac [][hom_functor_def] >>
`(c|x→y|) ∈ dom_homs c x` by (
  srw_tac [][dom_homs_def] ) >>
imp_res_tac dom_homs_subset_homs >>
fsrw_tac [][SUBSET_DEF]);

val hom_functor_morf = Q.store_thm(
"hom_functor_morf",
`∀c x f. is_category c ∧ f ∈ c.mor ⇒
((c|x→_|)##f =
  TypedGraphFun ((c|x→f.dom|), c|x→f.cod|) (λg. f o g -:c))`,
srw_tac [][hom_functor_def] >>
qmatch_abbrev_tac `inclusion_functor u1 u2##z = X` >>
`z ∈ (ens_cat u1).mor` by (
  unabbrev_all_tac >>
  srw_tac [][hom_in_dom_homs,mor_obj] >>
  fsrw_tac [][hom_def] >>
  match_mp_tac maps_to_comp >>
  metis_tac [maps_to_in_def,maps_to_def] ) >>
srw_tac [][]);

val _ = export_rewrites["hom_functor_objf","hom_functor_morf"];

val hom_functor_dom = Q.store_thm(
"hom_functor_dom",
`∀c x. (hom_functor c x).dom = c`,
srw_tac [][hom_functor_def]);

val hom_functor_cod = Q.store_thm(
"hom_functor_cod",
`∀c x. (hom_functor c x).cod = (ens_cat (homs c))`,
srw_tac [][hom_functor_def]);

val _ = export_rewrites["hom_functor_cod","hom_functor_dom"];

val hom_op_cat = Q.store_thm(
"hom_op_cat",
`∀c x y. (c° |x→y|) = IMAGE op_mor (c|y→x|)`,
srw_tac [][hom_def,EXTENSION] >>
metis_tac [op_cat_maps_to_in,op_mor_map,op_mor_idem]);
val _ = export_rewrites["hom_op_cat"];

(*
val contra_functor_def = Define`
  contra_functor G = <| dom := G.dom°; cod := G.cod; map := G.map o op_mor |>`;

val contra_functor_components = Q.store_thm(
"contra_functor_components",
`∀G. ((contra_functor G).dom = G.dom°) ∧
     ((contra_functor G).cod = G.cod) ∧
     ((contra_functor G).map = G.map o op_mor)`,
srw_tac [][contra_functor_def]);
val _ = export_rewrites["contra_functor_components"];

val contra_functor_morf = Q.store_thm(
"contra_functor_morf",
`∀G f. (contra_functor G)##f = G##(f°)`,
srw_tac [][contra_functor_def,morf_def]);

val contra_functor_objf = Q.store_thm(
"contra_functor_objf",
`∀G x. is_category G.dom ∧ x ∈ G.dom.obj ⇒ ((contra_functor G)@@x = G@@x)`,
srw_tac [][objf_def,contra_functor_def]);

val _ = export_rewrites["contra_functor_morf","contra_functor_objf"];

val extensional_functor_contra_functor = Q.store_thm(
"extensional_functor_contra_functor",
`∀G. extensional_functor (contra_functor G) ⇔ extensional_functor G`,
srw_tac [DNF_ss][extensional_functor_def,extensional_def,EQ_IMP_THM] >- (
  first_x_assum (qspec_then `e°` mp_tac) >>
  srw_tac [][] ) >>
first_x_assum match_mp_tac >>
first_x_assum (qspec_then `e°` mp_tac) >>
srw_tac [][] );

val functor_axioms_contra_functor = Q.store_thm(
"functor_axioms_contra_functor",
`∀G. functor_axioms (contra_functor G) ⇔ functor_axioms G`,
srw_tac [][functor_axioms_def] >> EQ_TAC >> strip_tac >> fsrw_tac [][] >- (
  conj_tac >- (
    srw_tac [][] >>
    first_x_assum (qspecl_then [`f°`,`x`,`y`] mp_tac) >>
    imp_res_tac maps_to_obj >>
    srw_tac [][]

val is_functor_contra_functor = Q.store_thm(
"is_functor_contra_functor",
`∀G. is_functor (contra_functor G) ⇔ is_functor G`,
srw_tac [][is_functor_def,extensional_functor_contra_functor,functor_axioms_contra_functor]);
val _ = export_rewrites["is_functor_contra_functor"];
*)

val pre_op_mor_functor_def = Define`
  pre_op_mor_functor u1 u2 = <| dom := ens_cat u1; cod := ens_cat u2;
    map := λf. TypedGraphFun
                (IMAGE op_mor f.dom, IMAGE op_mor f.cod)
                (op_mor o f.map o op_mor) |>`;

val pre_op_mor_functor_components = Q.store_thm(
"pre_op_mor_functor_components",
`∀u1 u2.
     ((pre_op_mor_functor u1 u2).dom = ens_cat u1) ∧
     ((pre_op_mor_functor u1 u2).cod = ens_cat u2) ∧
     ((pre_op_mor_functor u1 u2).map = λf. TypedGraphFun
                (IMAGE op_mor f.dom, IMAGE op_mor f.cod)
                (op_mor o f.map o op_mor))`,
srw_tac [][pre_op_mor_functor_def]);
val _ = export_rewrites["pre_op_mor_functor_components"];

val pre_op_mor_functor_morf = Q.store_thm(
"pre_op_mor_functor_morf",
`∀u1 u2 f. (pre_op_mor_functor u1 u2)##f =
  TypedGraphFun (IMAGE op_mor f.dom, IMAGE op_mor f.cod) (op_mor o f.map o op_mor)`,
srw_tac [][morf_def]);
val _ = export_rewrites["pre_op_mor_functor_morf"];

val pre_op_mor_functor_objf = Q.store_thm(
"pre_op_mor_functor_objf",
`∀u1 u2 x. x ∈ u1 ∧ IMAGE op_mor x ∈ u2 ⇒ ((pre_op_mor_functor u1 u2)@@x = IMAGE op_mor x)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >>
conj_tac >- (
  qexists_tac `IMAGE op_mor x` >>
  srw_tac [][] >>
  srw_tac [][morphism_component_equality] >>
  srw_tac [][restrict_def,FUN_EQ_THM] >>
  srw_tac [][] >> fsrw_tac [][] ) >>
srw_tac [][] >>
fsrw_tac [][morphism_component_equality]);
val _ = export_rewrites["pre_op_mor_functor_objf"];

val op_mor_functor_def = Define`
  op_mor_functor u1 u2 = mk_functor (pre_op_mor_functor u1 u2)`;

val is_functor_op_mor_functor = Q.store_thm(
"is_functor_op_mor_functor",
`∀u1 u2. (∀x. x ∈ u1 ⇒ IMAGE op_mor x ∈ u2) ⇒ is_functor (op_mor_functor u1 u2)`,
srw_tac [][op_mor_functor_def] >>
srw_tac [][functor_axioms_def] >>
srw_tac [][] >- fsrw_tac [][IsTypedFun_def,HasFunType_def]
>- (
  qexists_tac `IMAGE op_mor x` >>
  srw_tac [][morphism_component_equality] >>
  srw_tac [][restrict_def,FUN_EQ_THM] >>
  srw_tac [][] >> fsrw_tac [][] ) >>
qmatch_abbrev_tac `hh = gg o ff -: ens_cat u2` >>
`ff ≈> gg -:ens_cat u2` by (
  srw_tac [][Abbr`ff`,Abbr`gg`] >>
  fsrw_tac [][IsTypedFun_def,HasFunType_def] ) >>
srw_tac [][] >>
srw_tac [][Abbr`gg`,Abbr`ff`,Abbr`hh`,morphism_component_equality] >>
srw_tac [][ComposeFun_def] >>
srw_tac [][restrict_def,FUN_EQ_THM] >>
srw_tac [][] >>
fsrw_tac [][IsTypedFun_def,HasFunType_def] >>
metis_tac []);
val _ = export_rewrites["is_functor_op_mor_functor"];

val op_mor_functor_dom_cod = Q.store_thm(
"op_mor_functor_dom_cod",
`∀u1 u2. ((op_mor_functor u1 u2).dom = ens_cat u1) ∧
         ((op_mor_functor u1 u2).cod = ens_cat u2)`,
srw_tac [][op_mor_functor_def]);
val _ = export_rewrites["op_mor_functor_dom_cod"];

val op_mor_functor_morf = Q.store_thm(
"op_mor_functor_morf",
`∀u1 u2 f. IsTypedFunIn u1 f ⇒ ((op_mor_functor u1 u2)##f =
  TypedGraphFun (IMAGE op_mor f.dom, IMAGE op_mor f.cod) (op_mor o f.map o op_mor))`,
srw_tac [][op_mor_functor_def,mk_functor_def,morphism_component_equality,morf_def,
           restrict_def]);
val _ = export_rewrites["op_mor_functor_morf"];

val op_mor_functor_objf = Q.store_thm(
"op_mor_functor_objf",
`∀u1 u2 x. x ∈ u1 ∧ IMAGE op_mor x ∈ u2 ⇒ ((op_mor_functor u1 u2)@@x = IMAGE op_mor x)`,
srw_tac [][op_mor_functor_def]);
val _ = export_rewrites["op_mor_functor_objf"];

val _ = add_rule{
  term_name = "contra_hom_functor",
  fixity=Suffix 620,
  pp_elements=[TOK"|_\226\134\146",TM,TOK"|"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val _ = overload_on("contra_hom_functor",``λc x. (op_mor_functor (homs c°) (homs c)) ◎ (hom_functor c° x)``);

val IMAGE_op_mor_idem = Q.store_thm(
"IMAGE_op_mor_idem",
`∀s. IMAGE op_mor (IMAGE op_mor s) = s`,
srw_tac [DNF_ss][EXTENSION]);
val _ = export_rewrites["IMAGE_op_mor_idem"];

val is_functor_contra_hom_functor_lemma = Q.store_thm(
"is_functor_contra_hom_functor_lemma",
`∀c. is_functor (op_mor_functor (homs c°) (homs c))`,
srw_tac [][] >>
match_mp_tac is_functor_op_mor_functor >>
srw_tac [DNF_ss][homs_def,LET_THM] >>
metis_tac []);
val _ = export_rewrites["is_functor_contra_hom_functor_lemma"];

val contra_hom_functor_objf = Q.store_thm(
"contra_hom_functor_objf",
`∀c x y. is_category c ∧ x ∈ c.obj ∧ y ∈ c.obj ⇒ ((c|_→y|)@@x = (c|x→y|))`,
srw_tac [][] >>
`IMAGE op_mor (c|x→y|) ∈ homs c°` by (
  srw_tac [][homs_def] >>
  srw_tac [][] >> metis_tac [] ) >>
`IMAGE op_mor (IMAGE op_mor (c|x→y|)) ∈ (homs c)` by (
  srw_tac [DNF_ss][homs_def,EXTENSION] >>
  srw_tac [][] >> metis_tac [] ) >>
srw_tac [][] >> srw_tac [DNF_ss][EXTENSION]);

val contra_hom_functor_morf = Q.store_thm(
"contra_hom_functor_morf",
`∀c x f. is_category c ∧ f° ∈ c.mor ∧ x ∈ c.obj ⇒
  ((c|_→x|)##f = TypedGraphFun ((c|f.dom→x|), (c|f.cod→x|)) (λg. g o f° -:c))`,
srw_tac [][] >>
qabbrev_tac `ff = f° °` >>
`f = ff` by srw_tac [][Abbr`ff`] >>
`ff ∈ c°.mor` by (
  srw_tac [][Abbr`ff`] >>
  qexists_tac `f°` >> srw_tac [][] ) >>
fsrw_tac [][] >> srw_tac [][] >>
qmatch_abbrev_tac `(op_mor_functor u1 u2)##f = g` >>
`IsTypedFun f` by (
  srw_tac [][Abbr`f`,Abbr`g`] >>
  qmatch_assum_rename_tac `f ∈ (c|g.cod→x|)` [] >>
  qexists_tac `f° ° o g° ° -:c` >>
  `g° ° ≈> f° ° -:c` by (
    match_mp_tac maps_to_composable >>
    srw_tac [][] >> fsrw_tac [][hom_def,maps_to_in_def] ) >>
  conj_tac >- (
    match_mp_tac op_cat_compose_in >>
    srw_tac [][] ) >>
  imp_res_tac composable_maps_to >>
  fsrw_tac [][hom_def] >>
  fsrw_tac [][maps_to_in_def] ) >>
`IsTypedFunIn u1 f` by (
  fsrw_tac [][Abbr`f`,Abbr`u1`,Abbr`u2`,homs_def] >>
  fsrw_tac [][LET_THM] >>
  metis_tac [mor_obj] ) >>
srw_tac [][Abbr`g`,Abbr`f`,morphism_component_equality] >>
TRY (srw_tac [DNF_ss][EXTENSION] >> NO_TAC) >>
srw_tac [][restrict_def,FUN_EQ_THM] >>
srw_tac [][] >> fsrw_tac [DNF_ss][] >- (
  qmatch_rename_tac `(g° o f° -:c°)° = f o g -:c` [] >>
  qspecl_then [`f`,`g`,`c°`] mp_tac op_cat_compose_in >>
  srw_tac [][] >> pop_assum (match_mp_tac o GSYM) >>
  match_mp_tac maps_to_composable >>
  fsrw_tac [][hom_def,maps_to_in_def] ) >>
metis_tac [op_mor_idem]);
val _ = export_rewrites["contra_hom_functor_objf","contra_hom_functor_morf"];

val _ = export_theory();
