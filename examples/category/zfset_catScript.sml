open HolKernel boolLib bossLib categoryTheory functorTheory nat_transTheory zfsetTheory lcsymtacs pred_setTheory pairTheory zfset_axiomsTheory boolSimps;

val _ = new_theory "set_cat";

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
fsrw_tac [][zfset_axiomsTheory.Extension_ax]);
val _ = export_rewrites["implode_explode"];

val IsSmall_def = Define`
  IsSmall s = ∃f z. INJ f s (explode z)`;

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
`∀f g. ((g |o| f).dom = f.dom) ∧
       ((g |o| f).cod = g.cod) ∧
       ((g |o| f).map = ComposeFn(f.dom,f.cod,g.cod) g.map f.map)`,
srw_tac [][ComposeTypedFn_def]);
val _ = export_rewrites["ComposeTypedFn_components"];

val set_cat_def = Define`
  set_cat = mk_cat <|
    obj := UNIV ;
    mor := {f | IsTypedFn f} ;
    id  := λx. <| dom := x; cod := x; map := IdFn x |> ;
    comp := λf g. (g |o| f).map |>`;

val is_category_set_cat = Q.store_thm(
"is_category_set_cat",
`is_category set_cat`,
srw_tac [][set_cat_def] >>
srw_tac [][category_axioms_def] >- (
  srw_tac [][maps_to_in_def,IsTypedFn_def,IdFnType] )
>- (
  srw_tac [][compose_in_def,morphism_component_equality] >>
  fsrw_tac [][IsTypedFn_def,ComposeFnId1] )
>- (
  srw_tac [][compose_in_def,morphism_component_equality] >>
  fsrw_tac [][IsTypedFn_def,ComposeFnId2] )
>- (
  srw_tac [][compose_in_def,morphism_component_equality] >>
  fsrw_tac [][composable_in_def] >>
  match_mp_tac ComposeFnAssoc >>
  fsrw_tac [][IsTypedFn_def] ) >>
fsrw_tac [][maps_to_in_def] >>
fsrw_tac [][IsTypedFn_def] >>
srw_tac [][compose_in_def] >>
srw_tac [][ComposeFnType]);
val _ = export_rewrites["is_category_set_cat"];

val set_cat_obj = Q.store_thm(
"set_cat_obj",
`∀x. x ∈ set_cat.obj`,
srw_tac [][set_cat_def]);

val set_cat_mor = Q.store_thm(
"set_cat_mor",
`∀f. f ∈ set_cat.mor ⇔ IsTypedFn f`,
srw_tac [][set_cat_def]);

val set_cat_id = Q.store_thm(
"set_cat_id",
`∀x. (set_cat.id x) = TypedGraphFn (x,x) I`,
srw_tac [][set_cat_def,TypedGraphFn_def,IdFn_eq_GraphFnI]);

val set_cat_composable_in = Q.store_thm(
"set_cat_composable_in",
`∀f g. f ≈> g -:set_cat ⇔ IsTypedFn f ∧ IsTypedFn g ∧ f ≈> g`,
srw_tac [][composable_in_def,set_cat_mor]);

val set_cat_comp = Q.store_thm(
"set_cat_comp",
`∀f g. f ≈> g -:set_cat ⇒ (set_cat.comp f g = ComposeFn(f.dom,g.dom,g.cod) g.map f.map)`,
srw_tac [][set_cat_def,mk_cat_def,restrict_def,composable_in_def]);

val set_cat_compose_in = Q.store_thm(
"set_cat_compose_in",
`∀f g. f ≈> g -:set_cat ⇒ (g o f -:set_cat = g |o| f)`,
srw_tac [][compose_in_def,morphism_component_equality,set_cat_comp,set_cat_composable_in]);

val set_cat_maps_to_in = Q.store_thm(
"set_cat_maps_to_in",
`∀f x y. f :- x → y -:set_cat ⇔ IsTypedFn f ∧ f :- x → y`,
srw_tac [][maps_to_in_def,EQ_IMP_THM,set_cat_mor]);

val _ = export_rewrites[
"set_cat_obj","set_cat_mor","set_cat_id",
"set_cat_composable_in","set_cat_comp",
"set_cat_compose_in","set_cat_maps_to_in"];

val is_locally_small_def = Define`
  is_locally_small c = ∀x y. x ∈ c.obj ∧ y ∈ c.obj ⇒ IsSmall (c|x→y|)`;

val is_lscat_def = Define`
  is_lscat c = is_category c ∧ is_locally_small c`;

val is_lscat_is_category = Q.store_thm(
"is_lscat_is_category",
`∀c. is_lscat c ⇒ is_category c`,
srw_tac [][is_lscat_def]);
val _ = export_rewrites["is_lscat_is_category"];

val _ = overload_on("hom_syntax",``λc x y. zfrep(c|x→y|)``);
val _ = overload_on("hom_syntax",``λc x y. hom c x y``);

val mrep_def = Define`
  mrep c f = zfel (c|f.dom→f.cod|) f`;

val _ = add_rule{
  term_name="mrep_syntax",
  fixity=TruePrefix 625,
  pp_elements=[TOK"|",TM,TOK"|-:"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val _ = overload_on("mrep_syntax",``λf c. mrep c f``);

val mrep_In_homset = Q.store_thm(
"mrep_In_homset",
`∀c f x y. is_lscat c ∧ f :- x → y -:c ⇒ (|f|-:c) In (c|x→y|)`,
srw_tac [][] >>
`IsSmall (c|x→y|)` by (
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  fsrw_tac [][is_lscat_def,is_locally_small_def] ) >>
srw_tac [][In_zfrep_thm] >>
qexists_tac `f` >>
fsrw_tac [][mrep_def,maps_to_in_def,hom_def] >>
qexists_tac `f` >> srw_tac [][]);

val In_homset_mrep = Q.store_thm(
"In_homset_mrep",
`∀c z x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧ z In (c|x→y|) ⇒
  ∃f. f :- x → y -:c ∧ (z = |f|-:c)`,
srw_tac [][mrep_def] >>
`IsSmall (c|x→y|)` by (
  fsrw_tac [][is_locally_small_def,is_lscat_def] ) >>
`∃m. m ∈ (c|x→y|) ∧ (z = zfel (c|x→y|) m)` by (
  metis_tac[In_zfrep_thm] ) >>
fsrw_tac [][hom_def,maps_to_in_def] >>
qexists_tac `m` >> srw_tac [][]);

val _ = export_rewrites["In_homset_mrep","mrep_In_homset"];

val mrep_inj = Q.store_thm(
"mrep_inj",
`∀f g x y c. is_lscat c ∧ f :- x → y -:c ∧ g :- x → y -:c ∧ (|f|-:c = |g|-:c) ⇒ (f = g)`,
srw_tac [][mrep_def,hom_def,maps_to_in_def,is_lscat_def,is_locally_small_def] >>
first_x_assum (qspecl_then [`g.dom`,`g.cod`] mp_tac) >>
srw_tac [][mor_obj] >>
qmatch_assum_abbrev_tac `IsSmall s` >>
`f ∈ s` by (srw_tac [][Abbr`s`] >> metis_tac []) >>
`g ∈ s` by (srw_tac [][Abbr`s`] >> metis_tac []) >>
imp_res_tac elzf_zfel >>
srw_tac [][morphism_component_equality] >>
metis_tac []);

val HS = HardSpace 1;

val _ = add_rule{
  term_name="mabs_syntax",
  fixity=TruePrefix 625,
  pp_elements=[TOK"\226\134\145",TM,HS,
               TOK ":-",HS,TM,HS,TOK"\226\134\146",HS,TM,HS,TOK "-:"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val mabs_def = Define`
  mabs c x y z = elzf (c|x→y|) z`;

val _ = overload_on("mabs_syntax",``λz x y c. mabs c x y z``);

val mabs_dom_cod = Q.store_thm(
"mabs_dom_cod",
`∀z x y c. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧ z In (c|x→y|) ⇒
((↑z :- x → y -:c).dom = x) ∧ ((↑z :- x → y -:c).cod = y)`,
srw_tac [][mabs_def] >>
`IsSmall (c|x→y|)` by fsrw_tac [][is_lscat_def,is_locally_small_def] >>
fsrw_tac [][In_zfrep_thm] >>
fsrw_tac [][hom_def,maps_to_in_def]);
val _ = export_rewrites["mabs_dom_cod"];

val mabs_mrep = Q.store_thm(
"mabs_mrep",
`∀c f x y. is_lscat c ∧ f :- x → y -:c ⇒ (↑(|f|-:c) :- x → y -:c = f)`,
srw_tac [][] >>
imp_res_tac maps_to_in_def >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
srw_tac [][mabs_def,mrep_def] >>
fsrw_tac [][] >>
match_mp_tac elzf_zfel >>
fsrw_tac [][is_lscat_def,is_locally_small_def] >>
srw_tac [][hom_def,maps_to_in_def] >> metis_tac []);

val mrep_mabs = Q.store_thm(
"mrep_mabs",
`∀c z x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧
         z In (c|x→y|) ⇒ (|(↑z :- x → y -:c)|-:c = z)`,
srw_tac [][] >>
`IsSmall (c|x→y|)` by (
  fsrw_tac [][is_lscat_def,is_locally_small_def] ) >>
imp_res_tac zfel_elzf >>
srw_tac [][mabs_def,mrep_def]);

val _ = export_rewrites["mabs_mrep","mrep_mabs"];

val In_homset_mabs = Q.store_thm(
"In_homset_mabs",
`∀c z x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧ z In (c|x→y|)
  ⇒ (↑z :- x → y -:c) :- x → y -:c`,
srw_tac [][] >>
imp_res_tac In_homset_mrep >>
srw_tac [][]);

val pre_hom_functor_def = Define`
  pre_hom_functor c x = <|
    dom := c ; cod := set_cat ;
    map := λg. TypedGraphFn ((c|x→g.dom|):zfset,(c|x→g.cod|):zfset)
                 (λz. |g o (↑z :- x → g.dom -:c) -:c|-:c)
  |>`;

val pre_hom_functor_dom = Q.store_thm(
"pre_hom_functor_dom",
`∀c x. (pre_hom_functor c x).dom = c`,
srw_tac [][pre_hom_functor_def]);

val pre_hom_functor_cod = Q.store_thm(
"pre_hom_functor_cod",
`∀c x. (pre_hom_functor c x).cod = set_cat`,
srw_tac [][pre_hom_functor_def]);

val _ = export_rewrites["pre_hom_functor_cod","pre_hom_functor_dom"];

val pre_hom_functor_morf_dom_cod = Q.store_thm(
"pre_hom_functor_morf_dom_cod",
`∀c x f. (((pre_hom_functor c x)##f).dom = c|x→f.dom|) ∧
         (((pre_hom_functor c x)##f).cod = c|x→f.cod|)`,
srw_tac [][pre_hom_functor_def,morf_def,TypedGraphFn_def]);
val _ = export_rewrites ["pre_hom_functor_morf_dom_cod"];

val pre_hom_functor_morf = Q.store_thm(
"pre_hom_functor_morf",
`∀c x g. (pre_hom_functor c x)##g =
  TypedGraphFn ((c|x→g.dom|), c|x→g.cod|)
    (λz. |g o ↑z :- x → g.dom -:c -:c|-:c)`,
srw_tac [][pre_hom_functor_def,morf_def]);
val _ = export_rewrites["pre_hom_functor_morf"];

val pre_hom_functor_objf = Q.store_thm(
"pre_hom_functor_objf",
`∀c x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj
  ⇒ ((pre_hom_functor c x)@@y = c|x→y|)`,
srw_tac [][objf_def,pre_hom_functor_def] >>
imp_res_tac is_lscat_is_category >>
imp_res_tac id_dom_cod >>
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  qexists_tac `c|x→y|` >>
  srw_tac [][morphism_component_equality,TypedGraphFn_def] >>
  match_mp_tac GraphFnExt >>
  srw_tac [][] >>
  qmatch_assum_rename_tac `f In c|x→y|` [] >>
  `↑f :- x → y -:c :- x → y -:c` by
    imp_res_tac In_homset_mabs >>
  fsrw_tac [][maps_to_in_def] ) >>
fsrw_tac [][TypedGraphFn_def,set_cat_def]);
val _ = export_rewrites ["pre_hom_functor_objf"];

val _ = add_rule{
  term_name = "hom_functor",
  fixity=Suffix 620,
  pp_elements=[TOK"|",TM,TOK"\226\134\146_|"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val hom_functor_def = Define`
  c|x→_| = mk_functor (pre_hom_functor c x)`;

val hom_functor_objf = Q.store_thm(
"hom_functor_objf",
`∀c x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj
  ⇒ (objf (hom_functor c x) y = c|x→y|)`,
srw_tac [][hom_functor_def]);

val hom_functor_morf = Q.store_thm(
"hom_functor_morf",
`∀c x f. f ∈ c.mor ⇒
((c|x→_|)##f =
  TypedGraphFn ((c|x→f.dom|), c|x→f.cod|)
    (λg. |(f o (↑g :- x → f.dom -:c) -:c)|-:c))`,
srw_tac [][hom_functor_def,pre_hom_functor_def,mk_functor_def,restrict_def,morf_def]);

val _ = export_rewrites["hom_functor_objf","hom_functor_morf"];

val is_functor_hom_functor = Q.store_thm(
"is_functor_hom_functor",
`∀c x. is_lscat c ∧ x ∈ c.obj ⇒ is_functor (c|x→_|)`,
srw_tac [][hom_functor_def] >>
srw_tac [][functor_axioms_def]
>- (
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_In_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `f.dom` >>
  imp_res_tac maps_to_in_def >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  srw_tac [][] >>
  match_mp_tac In_homset_mabs >>
  fsrw_tac [][] )
>- (
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  srw_tac [][TypedGraphFn_def] >>
  fsrw_tac [][maps_to_in_def] )
>- (
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  srw_tac [][TypedGraphFn_def] >>
  fsrw_tac [][maps_to_in_def] )
>- (
  srw_tac [][TypedGraphFn_def] >>
  match_mp_tac GraphFnExt >>
  srw_tac [][] >>
  qmatch_assum_rename_tac `f In c|x→y|`[] >>
  qspecl_then [`c`,`f`,`x`,`y`] mp_tac In_homset_mrep >>
  full_simp_tac std_ss [] >> strip_tac >> srw_tac [][] >>
  qmatch_assum_rename_tac `f :- x → y -:c`[] >>
  qspecl_then [`c`,`|f|-:c`,`x`,`y`] mp_tac In_homset_mabs >>
  full_simp_tac std_ss [] >> strip_tac >> srw_tac [][] >>
  fsrw_tac [][maps_to_in_def] ) >>
qmatch_abbrev_tac `hh = gg o ff -:set_cat` >>
`ff ≈> gg -:set_cat` by (
  srw_tac [][Abbr`ff`,Abbr`gg`,HasFnType_def,TypedGraphFn_def] >>
  imp_res_tac composable_in_def >> fsrw_tac [][] >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac composable_obj >>
  match_mp_tac mrep_In_homset >> fsrw_tac [][] >>
  qmatch_assum_rename_tac `h In c|x→Z|`["Z"] >>
  qmatch_assum_abbrev_tac `h In c|x→Z|` >>
  qspecl_then [`c`,`h`,`x`,`Z`] mp_tac In_homset_mabs >>
  srw_tac [][Abbr`Z`] >>
  metis_tac [maps_to_comp,maps_to_in_dom_cod] ) >>
srw_tac [][Abbr`ff`,Abbr`gg`,Abbr`hh`] >>
imp_res_tac is_lscat_is_category >>
qspecl_then [`c`,`f`,`g`] mp_tac composable_maps_to >>
fsrw_tac [][] >> strip_tac >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >>
srw_tac [][ComposeTypedFn_def,morphism_component_equality,TypedGraphFn_def] >>
qmatch_abbrev_tac `A = ComposeFn(X,Y,Z)(GraphFn Y ff)(GraphFn X gg)` >>
qspecl_then [`X`,`Y`,`Z`,`gg`,`ff`] mp_tac ComposeGraphFns >>
`f ≈> g` by imp_res_tac composable_in_def >>
unabbrev_all_tac >>
fsrw_tac [][HasFnType_def] >>
srw_tac [][] >>
match_mp_tac GraphFnExt >>
srw_tac [][] >>
qmatch_assum_rename_tac `e In X` ["X"] >>
AP_TERM_TAC >>
`(↑e :- x → f.dom -:c) ≈> f -: c` by (
  match_mp_tac maps_to_composable >>
  map_every qexists_tac [`x`,`f.dom`,`f.cod`] >>
  srw_tac [][] >- (
    imp_res_tac composable_obj >>
    match_mp_tac In_homset_mabs >>
    srw_tac [][] ) >>
  fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
imp_res_tac composable_maps_to >>
`(↑e :- x → f.dom -:c) :- x → f.dom -:c` by (
  match_mp_tac In_homset_mabs >>
  imp_res_tac composable_obj >>
  fsrw_tac [][] ) >>
fsrw_tac [][maps_to_in_def] >>
match_mp_tac (GSYM comp_assoc) >>
srw_tac [][]);
val _ = export_rewrites["is_functor_hom_functor"];

val hom_functor_dom = Q.store_thm(
"hom_functor_dom",
`∀c x. (hom_functor c x).dom = c`,
srw_tac [][hom_functor_def])

val hom_functor_cod = Q.store_thm(
"hom_functor_cod",
`∀c x. (hom_functor c x).cod = set_cat`,
srw_tac [][hom_functor_def])

val _ = export_rewrites["hom_functor_cod","hom_functor_dom"]

val hom_op_cat = Q.store_thm(
"hom_op_cat",
`∀c x y. (c° |x→y|) = IMAGE op_mor (c|y→x|)`,
srw_tac [][hom_def,EXTENSION] >>
metis_tac [op_cat_maps_to_in,op_mor_map,op_mor_idem]);
val _ = export_rewrites["hom_op_cat"];

val is_lscat_op_cat = Q.store_thm(
"is_lscat_op_cat",
`∀c. is_lscat c ⇒ is_lscat c°`,
srw_tac [][is_lscat_def,is_locally_small_def]);
val _ = export_rewrites ["is_lscat_op_cat"];

val zfel_IMAGE = Q.store_thm(
"zfel_IMAGE",
`∀s f x. IsSmall s ∧ BIJ f s (IMAGE f s) ∧ x ∈ (IMAGE f s) ⇒ (zfel (IMAGE f s) x = zfel s ((LINV f s) x))`,
srw_tac [][zfel_def,the_zfrep_def] >>
`IsSmall (IMAGE f s)` by srw_tac [][] >>
SELECT_ELIM_TAC >>
conj_tac >- (
  imp_res_tac IsSmall_BIJ >>
  qexists_tac `(b,z)` >> srw_tac [][] ) >>
Cases >> srw_tac [][] >>
SELECT_ELIM_TAC >>
conj_tac >- metis_tac [IsSmall_BIJ,FST,SND] >>
Cases >> srw_tac [][] >>
qmatch_rename_tac `THE (h (f x)) = THE (g (LINV f s (f x)))` [] >>
`LINV f s (f x) = x` by (
  match_mp_tac (MP_CANON LINV_DEF) >>
  metis_tac [BIJ_DEF] ) >>
fsrw_tac [][] >>
Cases_on `g x` >- (
  fsrw_tac [DNF_ss][BIJ_DEF,SURJ_DEF] >>
  res_tac >> fsrw_tac [][] ) >>
srw_tac [][] >>
Cases_on `h (f x)` >- (
  fsrw_tac [DNF_ss][BIJ_DEF,SURJ_DEF] >>
  res_tac >> fsrw_tac [][] ) >>
srw_tac [][]
the_zfrep_def
imp_res_tac BIJ_DEF >>
imp_res_tac LINV_DEF
srw_tac [][LINV_DEF]
fsrw_tac [DNF_ss][BIJ_DEF,INJ_DEF,SURJ_DEF]
DB.match [] ``LINV``

val op_lscat_mrep = Q.store_thm(
"op_lscat_mrep",
`∀c f. is_lscat c ∧ f° ∈ c.mor ⇒ (|f|-:c° = | f° |-:c)`,
srw_tac [][mrep_def] >>
imp_res_tac is_lscat_def
imp_res_tac mor_obj >>
imp_res_tac is_locally_small_def >>
srw_tac [][the_zfrep_def] >>
SELECT_ELIM_TAC >>
conj_tac >- fsrw_tac [][IsSmall_BIJ]
SELECT_ELIM_TAC
val _ = export_rewrites["op_lscat_mrep"];

val op_lscat_mabs = Q.store_thm(
"op_lscat_mabs",
`∀c z x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧ z In (c|y→x|) ⇒
(↑z :- x → y -:c° = (↑z :- y → x -:c)°)`,
srw_tac [][mabs_def,morphism_component_equality]);
val _ = export_rewrites["op_lscat_mabs"];

val _ = add_rule{
  term_name = "contra_hom_functor",
  fixity=Suffix 620,
  pp_elements=[TOK"|_\226\134\146",TM,TOK"|"],
  paren_style=OnlyIfNecessary,
  block_style=(AroundEachPhrase,(PP.INCONSISTENT,0))};

val _ = overload_on("contra_hom_functor",``λc x. hom_functor c° x``);

val contra_hom_functor_objf = Q.store_thm(
"contra_hom_functor_objf",
`∀c x y. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ⇒ ((c|_→y|)@@x = c|x→y|)`,
srw_tac [][]);

val contra_hom_functor_morf = Q.store_thm(
"contra_hom_functor_morf",
`∀c x f. is_lscat c ∧ f° ∈ c.mor ∧ x ∈ c.obj ⇒
  ((c|_→x|)##f = TypedGraphFn ((c|f.dom→x|), c|f.cod→x|)
                   (λg. |((↑g :- f.dom → x -:c) o f° -:c)|-:c))`,
srw_tac [][] >>
qabbrev_tac `ff = f° °` >>
`f = ff` by srw_tac [][Abbr`ff`] >>
`ff ∈ c°.mor` by (
  srw_tac [][Abbr`ff`] >>
  qexists_tac `f°` >> srw_tac [][] ) >>
fsrw_tac [][] >>
srw_tac [][TypedGraphFn_def,morphism_component_equality] >>
match_mp_tac GraphFnExt >>
srw_tac [][] >>
srw_tac [][op_cat_compose_in] >>
AP_TERM_TAC >>
AP_TERM_TAC >>
imp_res_tac maps_to_in_dom_cod >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
fsrw_tac [][]);
val _ = export_rewrites["contra_hom_functor_objf","contra_hom_functor_morf"];

val YfunctorNT_def = Define`
  YfunctorNT c f = mk_nt <|
    dom := c|_→f.dom|; cod := c|_→f.cod|;
    map := λx. c|x→_|##f |>`

val YfunctorNT_dom_cod = Q.store_thm(
"YfunctorNT_dom_cod",
`∀c f. ((YfunctorNT c f).dom = c|_→f.dom|) ∧
       ((YfunctorNT c f).cod = c|_→f.cod|)`,
srw_tac [][YfunctorNT_def]);
val _ = export_rewrites["YfunctorNT_dom_cod"];

val ntdom_YfunctorNT = Q.store_thm(
"ntdom_YfunctorNT",
`∀c f. ntdom (YfunctorNT c f) = c°`,
srw_tac [][YfunctorNT_def,mk_nt_def])

val ntcod_YfunctorNT = Q.store_thm(
"ntcod_YfunctorNT",
`∀c f. ntcod (YfunctorNT c f) = set_cat`,
srw_tac [][YfunctorNT_def,mk_nt_def])

val YfunctorNT_at = Q.store_thm(
"YfunctorNT_at",
`∀c f x. x ∈ c.obj ⇒
  ((YfunctorNT c f)@+x = c|x→_|##f)`,
srw_tac [][YfunctorNT_def,mk_nt_def,restrict_def])

val _ = export_rewrites ["ntdom_YfunctorNT","ntcod_YfunctorNT","YfunctorNT_at"]

val is_nat_trans_YfunctorNT = Q.store_thm(
"is_nat_trans_YfunctorNT",
`∀c f. is_lscat c ∧ f ∈ c.mor ⇒ is_nat_trans (YfunctorNT c f)`,
srw_tac [][YfunctorNT_def] >>
imp_res_tac is_lscat_is_category >>
srw_tac [][nat_trans_axioms_def,mor_obj] >- (
  imp_res_tac mor_obj >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_In_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  metis_tac [In_homset_mabs,maps_to_in_def,maps_to_def] ) >>
qmatch_assum_rename_tac `g° :- y → x -:c` [] >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >> srw_tac [][] >>
imp_res_tac mor_obj >> srw_tac [][] >>
qmatch_abbrev_tac
  `(TypedGraphFn (t2,t3) f2) o (TypedGraphFn (t1,t2) f1) -:set_cat =
   (TypedGraphFn (t4,t3) f3) o (TypedGraphFn (t1,t4) f4) -:set_cat` >>
`HasFnType f1 t1 t2 ∧
 HasFnType f3 t4 t3 ∧
 HasFnType f2 t2 t3 ∧
 HasFnType f4 t1 t4` by (
  unabbrev_all_tac >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_In_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  metis_tac [In_homset_mabs,maps_to_obj,maps_to_def,
             op_cat_obj,is_category_op_cat] ) >>
qmatch_abbrev_tac `x o w -:set_cat = v o u -:set_cat` >>
`IsTypedFn u ∧ IsTypedFn v ∧ IsTypedFn w ∧ IsTypedFn x` by
  metis_tac [IsTypedFnTypedGraphFn] >>
`u ∈ set_cat.mor ∧ v ∈ set_cat.mor ∧ w ∈ set_cat.mor ∧ x ∈ set_cat.mor` by
  metis_tac [set_cat_mor] >>
`u ≈> v -:set_cat` by (
  srw_tac [][composable_def,Abbr`v`,Abbr`u`]) >>
`w ≈> x -:set_cat` by (
  srw_tac [][composable_def,Abbr`x`,Abbr`w`]) >>
srw_tac [][] >>
map_every qunabbrev_tac [`u`,`v`,`w`,`x`] >>
srw_tac [][ComposeTypedFn_def,TypedGraphFn_def] >>
srw_tac [][ComposeGraphFns] >>
match_mp_tac GraphFnExt >>
srw_tac [][Abbr`t1`,Abbr`f1`,Abbr`f2`,Abbr`f3`,Abbr`f4`] >>
`↑x :- g.dom → f.dom -:c :- g.dom → f.dom -:c` by (
  match_mp_tac In_homset_mabs >> fsrw_tac [][] ) >>
fsrw_tac [][] >> srw_tac [][] >>
`↑x :- g.dom → f.dom -:c ≈> f -:c ∧ g° ≈> ↑x :- g.dom → f.dom -:c -:c` by (
  fsrw_tac [][composable_in_def,maps_to_in_def] ) >>
imp_res_tac composable_maps_to >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >>
AP_TERM_TAC >>
match_mp_tac comp_assoc >>
srw_tac [][]);
val _ = export_rewrites["is_nat_trans_YfunctorNT"];

val YfunctorNT_maps_to = Q.store_thm(
"YfunctorNT_maps_to",
`∀c f. is_lscat c ∧ f ∈ c.mor ⇒
    (YfunctorNT c f) :- (c|_→f.dom|) → (c|_→f.cod|) -:[(c°)→set_cat]`,
srw_tac [][maps_to_in_def]);
val _ = export_rewrites["YfunctorNT_maps_to"];

val YfunctorNT_composable = Q.store_thm(
"YfunctorNT_composable",
`∀c f g. is_lscat c ∧ f ≈> g -:c ⇒
  (YfunctorNT c f) ≈> (YfunctorNT c g) -:[(c°)→set_cat]`,
srw_tac [][composable_nts_def] >> fsrw_tac [][composable_in_def]);
val _ = export_rewrites["YfunctorNT_composable"];

val is_category_presheaf_cat = Q.store_thm(
"is_category_presheaf_cat",
`∀c. is_lscat c ⇒ is_category [(c°)→set_cat]`,
metis_tac [is_category_functor_cat,is_category_set_cat,
           is_category_op_cat,is_lscat_is_category])
val _ = export_rewrites["is_category_presheaf_cat"];

val pre_Yfunctor_def = Define`
  pre_Yfunctor c = <|
    dom := c; cod := [(c°)→set_cat];
    map := λf. YfunctorNT c f |>`;

val pre_Yfunctor_components = Q.store_thm(
"pre_Yfunctor_components",
`∀c. ((pre_Yfunctor c).dom = c) ∧
     ((pre_Yfunctor c).cod = [(c°)→set_cat]) ∧
     ((pre_Yfunctor c).map = λf. YfunctorNT c f)`,
srw_tac [][pre_Yfunctor_def]);
val _ = export_rewrites["pre_Yfunctor_components"];

val pre_Yfunctor_objf = Q.store_thm(
"pre_Yfunctor_objf",
`∀c x. is_lscat c ∧ x ∈ c.obj
  ⇒ ((pre_Yfunctor c)@@x = c|_→x|)`,
srw_tac [][objf_def] >>
SELECT_ELIM_TAC >> srw_tac [][] >- (
  qexists_tac `c|_→x|` >> srw_tac [][] >>
  match_mp_tac nt_eq_thm >>
  srw_tac [][id_mor] >>
  srw_tac [][TypedGraphFn_def,set_cat_def,IdFn_eq_GraphFnI] >>
  match_mp_tac GraphFnExt >> srw_tac [][] >>
  imp_res_tac is_lscat_is_category >>
  metis_tac [maps_to_in_def,maps_to_def,id_comp2,maps_to_obj,mrep_mabs,In_homset_mabs]) >>
match_mp_tac functor_eq_thm >>
srw_tac [][] >>
qmatch_assum_rename_tac `is_functor z` [] >>
`[c° →set_cat].id z = id_nt z` by (
  match_mp_tac functor_cat_id >>
  srw_tac [][]) >>
qpat_assum `YfunctorNT c (c.id x) = X` mp_tac >>
srw_tac [][morphism_component_equality]);
val _ = export_rewrites["pre_Yfunctor_objf"];

val Yfunctor_def = Define`
  Yfunctor c = mk_functor (pre_Yfunctor c)`;

val is_functor_Yfunctor = Q.store_thm(
"is_functor_Yfunctor",
`∀c. is_lscat c ⇒ is_functor (Yfunctor c)`,
srw_tac [][Yfunctor_def] >>
imp_res_tac is_lscat_is_category >>
srw_tac [][functor_axioms_def,morf_def]
>- (imp_res_tac maps_to_obj >> fsrw_tac [][morf_def,maps_to_in_def])
>- (imp_res_tac maps_to_obj >> fsrw_tac [][morf_def,maps_to_in_def])
>- fsrw_tac [][maps_to_in_def]
>- (
  qexists_tac `c|_→x|` >>
  srw_tac [][] >>
  match_mp_tac nt_eq_thm >>
  imp_res_tac id_mor >>
  imp_res_tac YfunctorNT_maps_to >>
  fsrw_tac [][maps_to_in_def] >>
  srw_tac [][TypedGraphFn_def] >>
  match_mp_tac GraphFnExt >> srw_tac [][] >>
  metis_tac [maps_to_in_def,maps_to_def,id_comp2,maps_to_obj,mrep_mabs,In_homset_mabs]) >>
imp_res_tac composable_maps_to >>
imp_res_tac maps_to_in_def >>
imp_res_tac YfunctorNT_composable >>
match_mp_tac nt_eq_thm >> fsrw_tac [][] >>
conj_tac >- ( srw_tac [][nt_comp_def,YfunctorNT_def] ) >>
conj_tac >- ( srw_tac [][nt_comp_def,YfunctorNT_def] ) >>
`f ∈ c.mor ∧ g ∈ c.mor` by (
  imp_res_tac composable_in_def >> srw_tac [][]) >>
srw_tac [][] >>
qmatch_abbrev_tac
  `h = TypedGraphFn (i,j) k o TypedGraphFn (l,m) n -:set_cat` >>
`HasFnType k i j ∧ HasFnType n l m` by (
  unabbrev_all_tac >>
  srw_tac [][HasFnType_def] >>
  metis_tac [mrep_In_homset,maps_to_comp,is_lscat_is_category,
             mor_obj,In_homset_mabs,maps_to_in_def,maps_to_def] ) >>
imp_res_tac IsTypedFnTypedGraphFn >>
imp_res_tac set_cat_mor >>
`m = i` by (
  fsrw_tac [][composable_in_def,Abbr`m`,Abbr`i`] ) >>
`(TypedGraphFn (l,m) n) ≈> (TypedGraphFn (i,j) k) -:set_cat` by (
  srw_tac [][]) >>
srw_tac [][Abbr`h`] >>
srw_tac [][TypedGraphFn_def,ComposeTypedFn_def] >>
srw_tac [][ComposeGraphFns] >>
match_mp_tac GraphFnExt >>
srw_tac [][] >>
unabbrev_all_tac >>
fsrw_tac [][] >>
AP_TERM_TAC >>
qmatch_assum_rename_tac `e In X` ["X"] >>
`↑e :- x → f.dom -:c ≈> f -:c` by (
  match_mp_tac maps_to_composable >> srw_tac [][] >>
  map_every qexists_tac [`x`,`f.dom`,`f.cod`] >>
  srw_tac [][] >>
  metis_tac [is_lscat_is_category,composable_obj,In_homset_mabs]) >>
imp_res_tac composable_maps_to >>
`g.dom = f.cod` by (
  fsrw_tac [][composable_in_def] ) >>
fsrw_tac [][] >>
match_mp_tac (GSYM comp_assoc) >> srw_tac [][]);

val Yfunctor_dom = Q.store_thm(
"Yfunctor_dom",
`∀c. (Yfunctor c).dom = c`,
srw_tac [][Yfunctor_def]);

val Yfunctor_cod = Q.store_thm(
"Yfunctor_cod",
`∀c. (Yfunctor c).cod = [(c°)→set_cat]`,
srw_tac [][Yfunctor_def]);

val Yfunctor_objf = Q.store_thm(
"Yfunctor_objf",
`∀c x. is_lscat c ∧ x ∈ c.obj ⇒
 ((Yfunctor c)@@x = c|_→x|)`,
srw_tac [][Yfunctor_def,mk_functor_objf,is_lscat_is_category]);

val Yfunctor_morf = Q.store_thm(
"Yfunctor_morf",
`∀c f. is_lscat c ∧ f ∈ c.mor ⇒
  ((Yfunctor c)##f = YfunctorNT c f)`,
srw_tac [][Yfunctor_def,morf_def]);

val _ = export_rewrites["Yfunctor_dom","Yfunctor_cod","Yfunctor_objf","Yfunctor_morf"];

val YMap_def = Define`
  YMap c x n = (n@+x).map ' |c.id x|-:(c°)`;

val YMapImage = Q.store_thm(
"YMapImage",
`∀c x n f. is_lscat c ∧ is_functor f ∧ is_nat_trans n ∧
           (f :- c° → set_cat) ∧ x ∈ c.obj ∧
           (n :- ((Yfunctor c)@@x) → f) ⇒
             (YMap c x n) In (f@@x)`,
srw_tac [][YMap_def] >>
`(n @+ x) :- (n.dom @@ x) → (n.cod @@ x) -: n.dom.cod` by (
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
pop_assum mp_tac >> srw_tac [][] >>
ntac 4 (pop_assum mp_tac) >> srw_tac [][] >>
fsrw_tac [][IsTypedFn_def] >>
match_mp_tac InFn >>
qexists_tac `c|x→x|` >>
srw_tac [][] >>
match_mp_tac mrep_In_homset >>
srw_tac [][id_maps_to]);

val YMapInv_def = Define`
  YMapInv c x f y = mk_nt <|
    dom := (Yfunctor c)@@x;
    cod := f;
    map := λz. TypedGraphFn ((c|z→x|), f@@z)
               (λg. (f##((↑g:- z → x -:c)°)).map ' y) |>`;

val YMapInv_at = Q.store_thm(
"YMapInv_at",
`∀c x f y z. is_lscat c ∧ x ∈ c.obj ∧ z ∈ c.obj ⇒
    ((YMapInv c x f y) @+ z =
     TypedGraphFn ((c|z→x|), f@@z)
       (λg. (f##(↑g:- z → x -:c)°).map ' y))`,
srw_tac [][YMapInv_def,mk_nt_def,restrict_def]);
val _ = export_rewrites["YMapInv_at"];

val is_nat_trans_YMapInv = Q.store_thm(
"is_nat_trans_YMapInv",
`∀c x f y. is_lscat c ∧ is_functor f ∧ (f :- c° → set_cat) ∧
           x ∈ c.obj ∧ y In (f@@x)
 ⇒ is_nat_trans (YMapInv c x f y)`,
srw_tac [][YMapInv_def] >>
srw_tac [][nat_trans_axioms_def]
>- (
  srw_tac [][HasFnType_def] >>
  match_mp_tac InFn >>
  qexists_tac `f@@x` >>
  qmatch_assum_rename_tac `g In c|u→x|` [] >>
  `(↑g :- u → x -:c)° :- x → u -:(c°)` by (
    srw_tac [][] >>
    match_mp_tac In_homset_mabs >>
    srw_tac [][] ) >>
  `f##(↑g :- u → x -:c)° :- (f@@x) → (f@@u) -:set_cat` by (
    fsrw_tac [][is_functor_def,functor_axioms_def] >>
    first_x_assum match_mp_tac >>
    fsrw_tac [][]) >>
  `IsTypedFn (f##(↑g :- u → x -:c)°)` by fsrw_tac [][] >>
  fsrw_tac [][maps_to_in_def] >>
  metis_tac [IsTypedFn_def] ) >>
qmatch_assum_rename_tac `g° :- u → v -:c` [] >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >>
qmatch_abbrev_tac
`(TypedGraphFn (i,j) k) o (TypedGraphFn (l,i) n) -:set_cat =
 q o (TypedGraphFn (l,s) h) -:set_cat` >>
`HasFnType k i j ∧ HasFnType h l s` by (
 unabbrev_all_tac >> srw_tac [][HasFnType_def] >>
 match_mp_tac InFn >>
 qexists_tac `f@@x` >>
 qmatch_assum_abbrev_tac `z In (c|q→x|)` >>
 srw_tac [][] >>
 `↑z :- q → x -:c :- q → x -:c` by
   metis_tac [In_homset_mabs,maps_to_obj,op_cat_obj,
              is_lscat_is_category,is_category_op_cat] >>
  `f##(↑z :- q → x-:c)° :- f@@x → f@@q -:set_cat` by (
    fsrw_tac [][is_functor_def,functor_axioms_def] >>
    first_x_assum match_mp_tac >> srw_tac [][] ) >>
  fsrw_tac [][maps_to_in_def,IsTypedFn_def] >>
  metis_tac [] ) >>
`HasFnType n l i` by (
  srw_tac [][HasFnType_def,Abbr`n`,Abbr`i`,Abbr`l`] >>
  match_mp_tac mrep_In_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `g.dom` >>
  imp_res_tac is_lscat_is_category >>
  conj_tac >- srw_tac [][] >>
  conj_asm1_tac >- srw_tac [][] >>
  imp_res_tac maps_to_obj >>
  imp_res_tac maps_to_in_def >>
  metis_tac [In_homset_mabs] ) >>
`q :- s → j -:set_cat` by (
  fsrw_tac [][is_functor_def,functor_axioms_def,Abbr`q`,Abbr`s`,Abbr`j`] >>
  first_x_assum match_mp_tac >> srw_tac [][] ) >>
`IsTypedFn q` by fsrw_tac [][maps_to_in_def] >>
imp_res_tac maps_to_in_def >>
srw_tac [][] >>
imp_res_tac IsTypedFnTypedGraphFn >>
`TypedGraphFn (l,s) h ≈> q -: set_cat` by (
  fsrw_tac [][Abbr`q`,Abbr`s`,maps_to_in_def] ) >>
srw_tac [][] >>
srw_tac [][ComposeTypedFn_def] >- (
  fsrw_tac [][Abbr`j`,Abbr`q`,maps_to_in_def] ) >>
srw_tac [][ComposeGraphFns] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`l`,`q.cod`] >>
conj_tac >- (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] ) >>
`GraphFn l h In (l -> q.dom)` by (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] >>
  srw_tac [][]) >>
conj_tac >- (
  match_mp_tac ComposeFnType >>
  fsrw_tac [][IsTypedFn_def] >>
  srw_tac [][]) >>
srw_tac [][GraphFnAp] >>
qmatch_assum_rename_tac `z In l` [] >>
`ComposeFn (l,q.dom,q.cod) q.map (GraphFn l h) ' z = q.map ' (GraphFn l h ' z)`
  by fsrw_tac [][IsTypedFn_def,ApComposeFn] >>
srw_tac [][GraphFnAp,Abbr`k`,Abbr`l`,Abbr`n`,Abbr`h`] >>
`↑z :- g.dom → x -:c :- g.dom → x -:c` by (
  match_mp_tac In_homset_mabs >>
  imp_res_tac is_lscat_is_category >>
  imp_res_tac maps_to_obj >>
  fsrw_tac [][] ) >>
`g° ≈> ↑z :- g.dom → x-:c -:c` by (
  srw_tac [][composable_in_def] >>
  fsrw_tac [][maps_to_in_def] ) >>
imp_res_tac is_lscat_is_category >>
imp_res_tac composable_maps_to >>
fsrw_tac [][] >> srw_tac [][] >>
Q.ISPECL_THEN [`f`,`f.dom`,`f.cod`,`(↑z :- g.dom → x -:c)°`,`g`] mp_tac morf_comp >>
srw_tac [][op_cat_compose_in] >>
unabbrev_all_tac >>
`f##(↑z :- g.dom → x -:c)°  :- (f@@x) → (f@@g.dom) -:set_cat` by (
  fsrw_tac [][is_functor_def,functor_axioms_def] >>
  first_x_assum match_mp_tac >>
  srw_tac [][] ) >>
`f##(↑z :- g.dom → x -:c)° ≈> f##g -:set_cat` by (
  fsrw_tac [][] >>
  Q.ISPECL_THEN [`f`,`f.dom`,`f.cod`,`g`,`g.dom`,`g.cod`] mp_tac morf_maps_to >>
  fsrw_tac [][] ) >>
srw_tac [][] >>
fsrw_tac [][maps_to_in_def] >>
srw_tac [][GraphFnAp] >>
match_mp_tac (MP_CANON ApComposeFn) >>
fsrw_tac [][maps_to_in_def] >>
fsrw_tac [][IsTypedFn_def] >>
metis_tac []);
val _ = export_rewrites["is_nat_trans_YMapInv"];

val YMapInvImage = Q.store_thm(
"YMapInvImage",
`∀c x f y. is_lscat c ∧ is_functor f ∧ (f :- c° → set_cat) ∧
           x ∈ c.obj ∧ y In (f@@x) ⇒
           is_nat_trans (YMapInv c x f y) ∧
           ((YMapInv c x f y) :- (Yfunctor c)@@x → f)`,
srw_tac [][YMapInv_def]);

val YMap1 = Q.store_thm(
"YMap1",
`∀c f x n. is_lscat c ∧ is_functor f ∧ (f :- c° → set_cat) ∧
           x ∈ c.obj ∧ is_nat_trans n ∧ (n :- ((Yfunctor c)@@x) → f) ⇒
             (YMapInv c x f (YMap c x n) = n)`,
rpt strip_tac >>
match_mp_tac nt_eq_thm >>
imp_res_tac YMapImage >>
imp_res_tac is_nat_trans_YMapInv >>
srw_tac [][]
>- fsrw_tac [][YMapInv_def]
>- fsrw_tac [][YMapInv_def] >>
qmatch_rename_tac `X = n @+ z` ["X"] >>
`z ∈ c.obj` by (
  pop_assum mp_tac >> srw_tac [][YMapInv_def] ) >>
srw_tac [][] >>
fsrw_tac [][] >>
qpat_assum `X = (Yfunctor c)@@x` mp_tac >> srw_tac [][] >>
`∀z. z ∈ c.obj ⇒ n @+ z :- c|z→x| → (n.cod@@z) -:n.cod.cod` by (
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
  metis_tac [contra_hom_functor_objf] ) >>
first_assum (qspec_then `z` mp_tac) >>
first_x_assum (qspec_then `x` mp_tac) >>
srw_tac [][] >>
srw_tac [][TypedGraphFn_def,morphism_component_equality] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`(n@+z).dom`,`(n@+z).cod`] >>
conj_tac >- (
  srw_tac [][] >>
  match_mp_tac GraphFnType >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac InFn >>
  qexists_tac `n.cod@@x` >>
  srw_tac [][] >>
  `↑g :- z → x -:c :- z → x -:c` by imp_res_tac In_homset_mabs >>
  Q.ISPECL_THEN [`n.cod`,`c°`,`set_cat`,`(↑g :- z → x -:c)°`,`x`,`z`]
    mp_tac morf_maps_to >>
  srw_tac [][] >>
  fsrw_tac [][IsTypedFn_def] ) >>
conj_tac >- fsrw_tac [][IsTypedFn_def] >>
qx_gen_tac `f` >>
srw_tac [][GraphFnAp] >>
srw_tac [][YMap_def] >>
Q.ISPECL_THEN [`n`,`c|_→x|`,`n.cod`,`set_cat`,
               `(↑f :- z → x -:c)°`,`x`,`z`]
  mp_tac naturality >>
`↑f :- z → x -:c :- z → x -:c` by imp_res_tac In_homset_mabs >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][] >>
qmatch_abbrev_tac `(f1 o f2 -:set_cat = f3 o f4 -:set_cat) ⇒ X` >>
`IsTypedFn f2` by (
  srw_tac [][Abbr`f2`] >>
  srw_tac [][HasFnType_def] >>
  match_mp_tac mrep_In_homset >>
  srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `x` >>
  srw_tac [][] >>
  imp_res_tac In_homset_mabs ) >>
`f2 ≈> f1 -:set_cat` by (srw_tac [][Abbr`f2`]) >>
Q.ISPECL_THEN [`n.cod`,`(↑f :- z → x -:c)°`] mp_tac maps_to_morf >>
fsrw_tac [][] >>
asm_simp_tac (srw_ss()) [ComposeTypedFn_def] >>
`f1.map In (f2.cod -> (n.cod@@z))` by (
  fsrw_tac [][IsTypedFn_def,Abbr`f2`,TypedGraphFn_def] >>
  metis_tac [] ) >>
`f2.map In (f2.dom -> f2.cod)` by metis_tac[IsTypedFn_def] >>
`ComposeFn (f2.dom,f2.cod,n.cod@@z) f1.map f2.map In
 (f2.dom -> n.cod@@z)` by srw_tac [][ComposeFnType] >>
ntac 3 (pop_assum mp_tac) >> srw_tac [][] >>
`f3.map In (f4.cod -> f3.cod)` by (
  fsrw_tac [][IsTypedFn_def] ) >>
`f4.map In (f4.dom -> f4.cod)` by fsrw_tac [][IsTypedFn_def] >>
`ComposeFn (f4.dom,f4.cod,f3.cod) f3.map f4.map In
  (f4.dom -> f3.cod)` by srw_tac [][ComposeFnType] >>
`f4.dom = f2.dom` by (
  qpat_assum `n.cod.cod = set_cat` assume_tac >>
  fsrw_tac [][Abbr`f2`]) >>
`f3.cod = n.cod @@z` by ( fsrw_tac [][maps_to_in_def] ) >>
`|c.id x|-:c In f2.dom` by (
  srw_tac [][Abbr`f2`,TypedGraphFn_def] >>
  match_mp_tac mrep_In_homset >>
  srw_tac [][id_maps_to] ) >>
ntac 6 (pop_assum mp_tac) >> srw_tac [][] >>
qunabbrev_tac `X` >>
qspecl_then [`f2.dom`,`f4.cod`,`n.cod@@z`,`f3.map`,`f4.map`] mp_tac (GSYM ApComposeFn) >>
srw_tac [][] >> pop_assum (K ALL_TAC) >>
qspecl_then [`f2.dom`,`f1.dom`,`n.cod@@z`,`f1.map`,`f2.map`] mp_tac (GSYM ApComposeFn) >>
fsrw_tac [][] >>
strip_tac >> pop_assum (qspec_then `|c.id x|-:c` mp_tac) >>
qsuff_tac `f = (f2.map ' |c.id x|-:c)` >- srw_tac [][] >>
srw_tac [][Abbr`f2`,TypedGraphFn_def] >>
srw_tac [][GraphFnAp] >>
srw_tac [][id_maps_to]);

val YMap2 = Q.store_thm(
"YMap2",
`∀c x f y. is_lscat c ∧ is_functor f ∧ (f :- c° → set_cat) ∧
           x ∈ c.obj ∧ y In (f@@x) ⇒
             (YMap c x (YMapInv c x f y) = y)`,
srw_tac [][YMap_def] >>
imp_res_tac is_lscat_is_category >>
`|c.id x|-:c In c|x→x|` by (
  match_mp_tac mrep_In_homset >>
  srw_tac [][id_maps_to] ) >>
srw_tac [][GraphFnAp] >>
srw_tac [][mabs_mrep,id_maps_to] >>
`f##((c°).id x) = set_cat.id (f@@x)` by srw_tac [][morf_id] >>
fsrw_tac [][] >>
srw_tac [][GraphFnAp]);

val YfunctorNT_YMapInv = Q.store_thm(
"YfunctorNT_YMapInv",
`∀c f x y. is_lscat c ∧ f :- x → y -:c ⇒
    (YfunctorNT c f = YMapInv c x (c|_→y|) (|f|-:c))`,
srw_tac [][] >>
match_mp_tac nt_eq_thm >>
imp_res_tac maps_to_in_def >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
fsrw_tac [][] >>
conj_tac >- srw_tac [][YfunctorNT_def,YMapInv_def] >>
conj_tac >- srw_tac [][YfunctorNT_def,YMapInv_def] >>
srw_tac [][TypedGraphFn_def] >>
match_mp_tac GraphFnExt >> srw_tac [][] >>
qmatch_assum_rename_tac `g In (c|z→f.dom|)` [] >>
`↑g :- z → f.dom -:c :- z → f.dom -:c` by imp_res_tac In_homset_mabs >>
imp_res_tac maps_to_in_def >>
srw_tac [][] >>
imp_res_tac mrep_In_homset >>
srw_tac [][GraphFnAp]);

val YMapYoneda = Q.store_thm(
"YMapYoneda",
`∀c f x y. is_lscat c ∧ f :- x → y -:c ⇒
  ((Yfunctor c)##f = YMapInv c x ((Yfunctor c)@@y) (|f|-:c))`,
srw_tac [][] >>
imp_res_tac maps_to_in_def >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
srw_tac [][YfunctorNT_YMapInv]);

val YonedaFull = Q.store_thm(
"YonedaFull",
`∀c x y n. is_lscat c ∧ x ∈ c.obj ∧ y ∈ c.obj ∧
           is_nat_trans n ∧ (n :- ((Yfunctor c)@@x) → ((Yfunctor c)@@y)) ⇒
           (↑(YMap c x n):- x → y -:c :- x → y -:c) ∧
           ((Yfunctor c)##(↑(YMap c x n):- x → y -:c) = n)`,
rpt gen_tac >> strip_tac >>
`YMap c x n In (c|_→y|)@@x` by (
  match_mp_tac YMapImage >>
  imp_res_tac Yfunctor_objf >>
  fsrw_tac [][] ) >>
`YMap c x n In c|x→y|` by metis_tac [contra_hom_functor_objf] >>
conj_asm1_tac >- srw_tac [][In_homset_mabs] >>
imp_res_tac YMapYoneda >>
srw_tac [][] >>
match_mp_tac YMap1 >>
fsrw_tac [][]);

val YonedaFaithful = Q.store_thm(
"YonedaFaithful",
`∀c f g x y. is_lscat c ∧ f :- x → y -:c ∧ g :- x → y -:c ∧
             ((Yfunctor c)##f = (Yfunctor c)##g) ⇒
               (f = g)`,
srw_tac [][] >>
imp_res_tac maps_to_in_def >>
imp_res_tac Yfunctor_morf >>
imp_res_tac YfunctorNT_YMapInv >>
fsrw_tac [][] >>
`YMap c x (YMapInv c x (c|_→y|) (|f|-:c)) =
 YMap c x (YMapInv c x (c|_→y|) (|g|-:c))`
 by metis_tac [] >>
imp_res_tac is_lscat_is_category >>
imp_res_tac maps_to_obj >>
`is_functor (c|_→y|)` by srw_tac [][] >>
`(c|_→y|) :- c° → set_cat` by (
  srw_tac [][] ) >>
`|f|-:c In (c|_→y|)@@x` by srw_tac [][] >>
`|g|-:c In (c|_→y|)@@x` by srw_tac [][] >>
imp_res_tac YMap2 >>
fsrw_tac [][] >>
metis_tac [mrep_inj]);

val YonedaEmbedding = Q.store_thm(
"YonedaEmbedding",
`∀c a b. is_lscat c ∧ a ∈ c.obj ∧ b ∈ c.obj ∧
         ((Yfunctor c)@@a = (Yfunctor c)@@b) ⇒
           (a = b)`,
srw_tac [][] >> pop_assum mp_tac >> srw_tac [][] >>
`(c|_→a|)##(c.id a) = (c|_→b|)##(c.id a)` by srw_tac [][] >>
pop_assum mp_tac >>
pop_assum (K ALL_TAC) >>
imp_res_tac is_lscat_is_category >>
imp_res_tac id_mor >>
srw_tac [][] >>
fsrw_tac [][TypedGraphFn_def] >>
`|(c.id a)|-:c In c|a→a|` by (
  match_mp_tac mrep_In_homset >>
  srw_tac [][id_maps_to] ) >>
`|(c.id a)|-:c In c|a→b|` by metis_tac [] >>
qmatch_assum_abbrev_tac `GraphFn s1 f1 = GraphFn s2 f2` >>
`f1 (|c.id a|-:c) = f2 (|c.id a|-:c)` by (
  `GraphFn s1 f1 ' (|c.id a|-:c) = f1 (|c.id a|-:c)` by (
    match_mp_tac GraphFnAp >> srw_tac [][] ) >>
  `GraphFn s2 f2 ' (|c.id a|-:c) = f2 (|c.id a|-:c)` by (
    match_mp_tac GraphFnAp >> srw_tac [][] ) >>
  ntac 2 (pop_assum mp_tac) >>
  unabbrev_all_tac >>
  srw_tac [][] ) >>
unabbrev_all_tac >>
fsrw_tac [][]
mrep_inj
YonedaFaithful
mrep_def
mabs_mrep
mrep_mabs
qspecl_then [`c|a→a|`,GraphFnAp
qsuff_tac `(c|a→b|)=(c|a→a|)` >- (
  srw_tac [][] >>
  `(c.id a).map ∈ (c|a→a|)` by (
    srw_tac [][hom_def] >>
    qexists_tac `c.id a` >>
    srw_tac [][id_maps_to] ) >>
  `(c.id a).map ∈ 
fsrw_tac [][is_lscat_def,is_locally_small_def] >>
res_tac >>
fsrw_tac [][In_zfrep_thm] >>
the_zfrep_inj
zfel_def
mrep_def
mrep_inj
fsrw_tac [][the_zfrep_def]
`↑ (|c.id a|-:c) :- a → b -:c :- a → b -:c` by (
  match_mp_tac In_homset_mabs >> srw_tac [][] ) >>
pop_assum mp_tac >> srw_tac [][] >>
fsrw_tac [][maps_to_def])

val _ = export_theory ()
