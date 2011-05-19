open HolKernel Parse boolLib bossLib lcsymtacs categoryTheory functorTheory;

val _ = new_theory "nat_trans";

val _ = type_abbrev("nat_trans",
``:(('a1,'b1,'a2,'b2) functor,('a1,'b1,'a2,'b2) functor,
    'a1 -> ('a2,'b2) mor) morphism``);

val _ = overload_on("ntdom", ``λn. n.dom.dom``);
val _ = overload_on("ntcod", ``λn. n.cod.cod``);
val _ = set_fixity "@+" (Infixl 2000);
val _ = overload_on("@+", ``λ(n:('a,'b,'c,'d) nat_trans) x. n.map x``);

val extensional_nat_trans_def = Define`
  extensional_nat_trans n = extensional n.map (ntdom n).obj`;

val nat_trans_axioms_def = Define`
  nat_trans_axioms n =
    is_functor n.dom ∧
    is_functor n.cod ∧
    (n.dom.dom = n.cod.dom) ∧
    (n.dom.cod = n.cod.cod) ∧
    (∀x. x ∈ (ntdom n).obj ⇒
           (n@+x) :- (n.dom@@x) → (n.cod@@x) -:(ntcod n)) ∧
    (∀f x y. f :- x → y -:(ntdom n) ⇒
      (n@+y o (n.dom##f) -:(ntcod n) = (n.cod##f) o n@+x -:(ntcod n)))`;

val is_nat_trans_def = Define`
  is_nat_trans n = extensional_nat_trans n ∧ nat_trans_axioms n`;

val mk_nt_def = Define`
  mk_nt n = <| dom := n.dom; cod := n.cod; map := restrict n.map (ntdom n).obj |>`;

val mk_nt_dom = Q.store_thm(
"mk_nt_dom",
`∀n. (mk_nt n).dom = n.dom`,
srw_tac [][mk_nt_def]);

val mk_nt_cod = Q.store_thm(
"mk_nt_cod",
`∀n. (mk_nt n).cod = n.cod`,
srw_tac [][mk_nt_def]);

val _ = export_rewrites ["mk_nt_dom","mk_nt_cod"];

val is_nat_trans_mk_nt = Q.store_thm(
"is_nat_trans_mk_nt",
`∀n. is_nat_trans (mk_nt n) ⇔ nat_trans_axioms n`,
gen_tac >> EQ_TAC >- (
  srw_tac [][is_nat_trans_def,nat_trans_axioms_def,mk_nt_def,restrict_def] >>
  `f :- x → y -:n.dom.dom` by metis_tac [] >>
  res_tac >>
  imp_res_tac is_functor_is_category >>
  imp_res_tac maps_to_obj >>
  fsrw_tac [][]) >>
srw_tac [][mk_nt_def,is_nat_trans_def,extensional_nat_trans_def] >>
fsrw_tac [][nat_trans_axioms_def] >>
srw_tac [][restrict_def] >>
imp_res_tac is_functor_is_category >>
imp_res_tac maps_to_obj);
val _ = export_rewrites["is_nat_trans_mk_nt"];

val naturality = Q.store_thm(
"naturality",
`∀n f g c k x y. is_nat_trans n ∧
  (n :- f → g) ∧ (c = ntcod n) ∧ k :- x → y -:(ntdom n) ⇒
  (n@+y o f##k -:c = (g##k) o n@+x -:c)`,
srw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
first_assum match_mp_tac >> first_assum ACCEPT_TAC);

val nt_at_maps_to = Q.store_thm(
"nt_at_maps_to",
`∀n f g x a b c. is_nat_trans n ∧ (n :- f → g) ∧ x ∈ f.dom.obj ∧ (a = f@@x) ∧ (b = g@@x) ∧ (c = g.cod) ⇒
   n@+x :- a → b -:c`,
srw_tac [][is_nat_trans_def,nat_trans_axioms_def] >> res_tac);

val nt_eq_thm = Q.store_thm(
"nt_eq_thm",
`∀n1 n2. is_nat_trans n1 ∧ is_nat_trans n2 ∧
    (n1.dom = n2.dom) ∧ (n1.cod = n2.cod) ∧
    (∀x. x ∈ (ntdom n1).obj ⇒ (n1@+x = n2@+x)) ⇒
      (n1 = n2)`,
srw_tac [][morphism_component_equality,is_nat_trans_def,
     extensional_nat_trans_def,extensional_def,FUN_EQ_THM] >>
metis_tac []);

val id_nt_def = Define`
  id_nt f = mk_nt <| dom := f; cod := f; map := λx. id (f@@x) -:f.cod |>`;

val id_nt_dom = Q.store_thm(
"id_nt_dom",
`∀f. (id_nt f).dom = f`,
srw_tac [][id_nt_def]);

val id_nt_cod = Q.store_thm(
"id_nt_cod",
`∀f. (id_nt f).cod = f`,
srw_tac [][id_nt_def]);

val id_nt_at = Q.store_thm(
"id_nt_at",
`∀f x. x ∈ f.dom.obj ⇒ ((id_nt f)@+x = id (f@@x) -:f.cod)`,
srw_tac [][id_nt_def,mk_nt_def,restrict_def]);

val _ = export_rewrites ["id_nt_dom","id_nt_cod","id_nt_at"];

val is_nat_trans_id_nt = Q.store_thm(
"is_nat_trans_id_nt",
`∀f. is_functor f ⇒ is_nat_trans (id_nt f)`,
srw_tac [][id_nt_def] >>
srw_tac [][nat_trans_axioms_def] >- (
  metis_tac [maps_to_morf,id_mor,morf_id,maps_to_def,
             is_functor_is_category,id_dom_cod] ) >>
imp_res_tac is_functor_is_category >>
qmatch_assum_rename_tac `g :- x → y -:f.dom` [] >>
`id (f@@y) -:f.cod = f##(id y -:f.dom)` by (
  match_mp_tac (GSYM morf_id) >> srw_tac [][] >>
  imp_res_tac maps_to_obj ) >>
`id (f@@x) -:f.cod = f##(id x -:f.dom)` by (
  match_mp_tac (GSYM morf_id) >> srw_tac [][] >>
  imp_res_tac maps_to_obj ) >>
srw_tac [][] >>
qspecl_then [`f`,`f.dom`,`f.cod`,`g`,`id y -:f.dom`] mp_tac (GSYM morf_comp) >>
`g ≈> (id y -:f.dom) -:f.dom` by (
  match_mp_tac maps_to_composable >>
  metis_tac [id_maps_to,maps_to_obj] ) >>
srw_tac [][] >>
qspecl_then [`f`,`f.dom`,`f.cod`,`id x -:f.dom`,`g`] mp_tac (GSYM morf_comp) >>
`id x -:f.dom ≈> g -:f.dom` by (
  match_mp_tac maps_to_composable >>
  metis_tac [id_maps_to,maps_to_obj] ) >>
srw_tac [][] >>
fsrw_tac [][composable_in_def] >>
metis_tac [id_comp1,id_comp2,id_dom_cod,maps_to_obj]);
val _ = export_rewrites["is_nat_trans_id_nt"];

val composable_nts_def = Define`
  composable_nts f g = is_nat_trans f ∧ is_nat_trans g ∧
    (ntdom f = ntdom g) ∧ (ntcod f = ntcod g) ∧ f ≈> g`;

val _ = add_infix("\226\137\136\226\137\136>",450,NONASSOC);
val _ = overload_on("≈≈>",``composable_nts``);

val nt_comp_def = Define`
  nt_comp n m = mk_nt (compose (λn m x. m@+x o n@+x -:(ntcod n)) m n)`;

val _ = overload_on("\226\151\142",``nt_comp``);

val nt_comp_at = Q.store_thm(
"nt_comp_at",
`∀f g x. (f ≈> g) ∧ x ∈ (ntdom f).obj ⇒ ((g ◎ f) @+ x = g@+x o f@+x -:(ntcod f))`,
srw_tac [][nt_comp_def,mk_nt_def,restrict_def]);
val _ = export_rewrites["nt_comp_at"];

val is_nat_trans_is_functor = Q.store_thm(
"is_nat_trans_is_functor",
`∀n. is_nat_trans n ⇒ is_functor n.dom ∧ is_functor n.cod`,
srw_tac [][is_nat_trans_def,nat_trans_axioms_def]);

val is_nat_trans_is_category = Q.store_thm(
"is_nat_trans_is_category",
`∀n. is_nat_trans n ⇒ is_category (ntdom n) ∧ is_category (ntcod n)`,
metis_tac [is_nat_trans_is_functor,is_functor_is_category]);

val is_nat_trans_nt_comp = Q.store_thm(
"is_nat_trans_nt_comp",
`∀n m. n ≈≈> m ⇒ is_nat_trans (m ◎ n)`,
srw_tac [][nt_comp_def] >>
srw_tac [][nat_trans_axioms_def]
>- fsrw_tac [][composable_nts_def,is_nat_trans_is_functor]
>- fsrw_tac [][composable_nts_def,is_nat_trans_is_functor]
>- (fsrw_tac [][composable_nts_def,is_nat_trans_def] >>
    metis_tac [nat_trans_axioms_def])
>- (fsrw_tac [][composable_nts_def,is_nat_trans_def] >>
    metis_tac [nat_trans_axioms_def])
>- (
  fsrw_tac [][composable_nts_def,compose_def,restrict_def] >>
  pop_assum mp_tac >> srw_tac [][] >>
  match_mp_tac maps_to_comp >>
  qexists_tac `n.cod@@x` >>
  imp_res_tac is_nat_trans_is_category >>
  metis_tac [is_nat_trans_def,nat_trans_axioms_def]) >>
imp_res_tac composable_nts_def >>
fsrw_tac [][compose_def,restrict_def] >>
qabbrev_tac `E = n.dom` >> qabbrev_tac `G = n.cod` >> qabbrev_tac `H = m.cod` >>
qabbrev_tac `C1 = E.dom` >> qabbrev_tac `C2 = E.cod` >>
`(G.dom = C1) ∧ (G.cod = C2) ∧ (H.dom = C1) ∧ (H.cod = C2) ∧
 (n@+x :- E@@x → G@@x -:C2) ∧ (n@+y :- E@@y → G@@y -:C2) ∧
 (m@+x :- G@@x → H@@x -:C2) ∧ (m@+y :- G@@y → H@@y -:C2) ∧
 (E##f :- E@@x → E@@y -:C2) ∧ (m.dom = n.cod) ∧
 (G##f :- G@@x → G@@y -:C2) ∧
 (H##f :- H@@x → H@@y -:C2)` by (
  fsrw_tac [][composable_nts_def,is_nat_trans_def,nat_trans_axioms_def,
              is_functor_def,functor_axioms_def] >>
  metis_tac [nt_at_maps_to,maps_to_obj] ) >>
fsrw_tac [][] >>
imp_res_tac is_nat_trans_is_category >>
imp_res_tac is_nat_trans_def >>
metis_tac [comp_assoc,maps_to_composable,nat_trans_axioms_def]);
val _ = export_rewrites["is_nat_trans_nt_comp"];

val id_nt_comp = Q.store_thm(
"id_nt_comp",
`∀f. is_nat_trans f ⇒
  (f ◎ (id_nt f.dom) = f) ∧
  ((id_nt f.cod) ◎ f = f)`,
srw_tac [][id_nt_def,nt_comp_def,mk_nt_def,morphism_component_equality] >- (
  srw_tac [][restrict_def,FUN_EQ_THM] >> srw_tac [][] >- (
    `f.dom.cod = f.cod.cod` by (
      fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
    srw_tac [][] >>
    match_mp_tac id_comp1 >>
    fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def,
                maps_to_in_def,is_functor_is_category] ) >>
  fsrw_tac [][is_nat_trans_def,extensional_nat_trans_def,extensional_def] ) >>
srw_tac [][restrict_def,FUN_EQ_THM] >> srw_tac [][] >- (
  match_mp_tac id_comp2 >>
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def,
              maps_to_in_def,is_functor_is_category] )
>- metis_tac [is_nat_trans_def,nat_trans_axioms_def] >>
fsrw_tac [][is_nat_trans_def,extensional_nat_trans_def,extensional_def]);
val _ = export_rewrites["id_nt_comp"];

val composable_nts_composable = Q.store_thm(
"composable_nts_composable",
`∀n m x. n ≈≈> m ∧ x ∈ (ntdom n).obj ⇒ n@+x ≈> m@+x -:(ntcod n)`,
srw_tac [][] >>
match_mp_tac maps_to_composable >>
map_every qexists_tac [`n.dom @@ x`,`n.cod @@ x`,`m.cod @@ x`] >>
imp_res_tac composable_nts_def >>
imp_res_tac is_nat_trans_def >>
imp_res_tac nat_trans_axioms_def >>
fsrw_tac [][]);

val nt_comp_assoc = Q.store_thm(
"nt_comp_assoc",
`∀f g h. f ≈≈> g ∧ g ≈≈> h ⇒ ((h ◎ g) ◎ f = h ◎ g ◎ f)`,
srw_tac [][] >>
imp_res_tac composable_nts_def >>
fsrw_tac [][nt_comp_def,mk_nt_def,restrict_def,FUN_EQ_THM,compose_def] >>
srw_tac [][] >>
match_mp_tac comp_assoc >>
fsrw_tac [][is_nat_trans_is_category] >>
metis_tac [composable_nts_composable]);

val nt_comp_dom_cod = Q.store_thm(
"nt_comp_dom_cod",
`∀f g. (f ≈> g) ⇒ (((g ◎ f).dom = f.dom) ∧ ((g ◎ f).cod = g.cod))`,
srw_tac [][nt_comp_def]);
val _ = export_rewrites["nt_comp_dom_cod"];

val pre_functor_cat_def = Define`
  pre_functor_cat c1 c2 =
    <| obj := {f | is_functor f ∧ f :- c1 → c2};
       mor := {n | is_nat_trans n ∧ (ntdom n = c1) ∧ (ntcod n = c2)};
       id_map := λx. (id_nt x).map;
       comp := (λn m. (nt_comp m n).map) |>`;

val pre_functor_cat_obj = Q.store_thm(
"pre_functor_cat_obj",
`∀c1 c2. (pre_functor_cat c1 c2).obj = {f | is_functor f ∧ f :- c1 → c2}`,
srw_tac [][pre_functor_cat_def]);

val pre_functor_cat_mor = Q.store_thm(
"pre_functor_cat_mor",
`∀c1 c2. (pre_functor_cat c1 c2).mor = {n | is_nat_trans n ∧ (ntdom n = c1) ∧ (ntcod n = c2)}`,
srw_tac [][pre_functor_cat_def]);

val pre_functor_cat_id = Q.store_thm(
"pre_functor_cat_id",
`∀c1 c2 x. is_functor x ∧ (x :- c1 → c2) ⇒ (id x -:(pre_functor_cat c1 c2) = id_nt x)`,
srw_tac [][pre_functor_cat_def,id_in_def,morphism_component_equality,restrict_def]);

val pre_functor_cat_comp = Q.store_thm(
"pre_functor_cat_comp",
`∀c1 c2 n m. (pre_functor_cat c1 c2).comp n m = (nt_comp m n).map`,
srw_tac [][pre_functor_cat_def]);

val pre_functor_cat_composable_in = Q.store_thm(
"pre_functor_cat_composable_in",
`∀c1 c2 f g. f ≈> g -:(pre_functor_cat c1 c2) = f ≈≈> g ∧ (ntdom g = c1) ∧ (ntcod g = c2)`,
srw_tac [][composable_nts_def,composable_in_def,pre_functor_cat_mor] >> metis_tac []);

val pre_functor_cat_compose_in = Q.store_thm(
"pre_functor_cat_compose_in",
`∀c1 c2 f g. g ≈> f -:(pre_functor_cat c1 c2) ⇒ (f o g -:(pre_functor_cat c1 c2) = nt_comp f g)`,
srw_tac [][compose_in_thm,morphism_component_equality,nt_comp_def] >>
srw_tac [][compose_def,restrict_def,pre_functor_cat_comp,nt_comp_def] >>
fsrw_tac [][composable_in_def]);

val pre_functor_cat_maps_to = Q.store_thm(
"pre_functor_cat_maps_to",
`∀c1 c2 f g x y. f :- x → y -:(pre_functor_cat c1 c2) = (f :- x → y)
  ∧ is_nat_trans f ∧ (ntdom f = c1) ∧ (ntcod f = c2)`,
srw_tac [][maps_to_in_def,pre_functor_cat_mor] >> metis_tac []);

val _ = export_rewrites
["pre_functor_cat_obj","pre_functor_cat_mor",
 "pre_functor_cat_id","pre_functor_cat_comp","pre_functor_cat_maps_to",
 "pre_functor_cat_compose_in","pre_functor_cat_composable_in"];

val _ = add_rule {
  term_name = "functor_cat",
  fixity = Closefix,
  pp_elements = [TOK"[",TM,TOK"\226\134\146",TM,TOK"]"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT,0))};

val functor_cat_def = Define`
  [c1→c2] = mk_cat (pre_functor_cat c1 c2)`;

val is_category_functor_cat = Q.store_thm(
"is_category_functor_cat",
`∀c1 c2. is_category c1 ∧ is_category c2 ⇒ is_category [c1→c2]`,
srw_tac [][functor_cat_def] >>
fsrw_tac [][category_axioms_def] >>
conj_tac >- srw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
conj_tac >- PROVE_TAC [is_nat_trans_def,nat_trans_axioms_def] >>
conj_tac >- (
  srw_tac [][] >>
  imp_res_tac is_nat_trans_def >>
  imp_res_tac nat_trans_axioms_def >>
  qmatch_abbrev_tac `f o g -:c = f` >>
  `g ≈> f -:c` by (
    srw_tac [][composable_nts_def,Abbr`c`,Abbr`g`] ) >>
  srw_tac [][Abbr`c`,Abbr`g`]) >>
conj_tac >- (
  srw_tac [][] >>
  imp_res_tac is_nat_trans_def >>
  imp_res_tac nat_trans_axioms_def >>
  qmatch_abbrev_tac `g o f -:c = f` >>
  `f ≈> g -:c` by (
    srw_tac [][composable_nts_def,Abbr`c`,Abbr`g`] ) >>
  srw_tac [][Abbr`c`,Abbr`g`]) >>
conj_tac >- (
  srw_tac [][] >>
  qmatch_abbrev_tac `X = h o g ◎ f -:c` >>
  qunabbrev_tac `X` >>
  `(g ◎ f ≈> h -:c) ∧ (f ≈> (h ◎ g) -:c)` by (
    imp_res_tac composable_nts_def >>
    fsrw_tac [][Abbr`c`,composable_nts_def] ) >>
  srw_tac [][nt_comp_assoc,Abbr`c`] ) >>
rpt gen_tac >> rpt DISCH_TAC >>
`f ≈> g -:pre_functor_cat c1 c2` by (
  srw_tac [][composable_nts_def] ) >>
srw_tac [][composable_nts_def]);

val functor_cat_obj = Q.store_thm(
"functor_cat_obj",
`∀c1 c2. [c1→c2].obj = {f | is_functor f ∧ f :- c1 → c2}`,
srw_tac [][functor_cat_def]);

val functor_cat_mor = Q.store_thm(
"functor_cat_mor",
`∀c1 c2. [c1→c2].mor = {n | is_nat_trans n ∧ (ntdom n = c1) ∧ (ntcod n = c2)}`,
srw_tac [][functor_cat_def]);

val functor_cat_id = Q.store_thm(
"functor_cat_id",
`∀c1 c2 x. x ∈ [c1→c2].obj ⇒ (id x -:[c1→c2] = id_nt x)`,
srw_tac [][functor_cat_def]);

val functor_cat_comp = Q.store_thm(
"functor_cat_comp",
`∀c1 c2 n m. n ≈≈> m ∧ (ntdom m = c1) ∧ (ntcod m = c2) ⇒ ([c1→c2].comp n m = (nt_comp m n).map)`,
srw_tac [][functor_cat_def,mk_cat_def,restrict_def]);

val functor_cat_compose_in = Q.store_thm(
"functor_cat_compose_in",
`∀c1 c2 n m. n ≈≈> m ∧ (ntdom m = c1) ∧ (ntcod m = c2) ⇒ (m o n -:[c1→c2] = nt_comp m n)`,
srw_tac [][functor_cat_def,composable_nts_def]);

val functor_cat_composable_in = Q.store_thm(
"functor_cat_composable_in",
`∀c1 c2 f g. f ≈> g -:[c1→c2] = f ≈≈> g ∧ (ntdom g = c1) ∧ (ntcod g = c2)`,
srw_tac [][functor_cat_def]);

val functor_cat_maps_to = Q.store_thm(
"functor_cat_maps_to",
`∀c1 c2 f g x y. f :- x → y -:[c1→c2] = (f :- x → y)
  ∧ is_nat_trans f ∧ (ntdom f = c1) ∧ (ntcod f = c2)`,
srw_tac [][functor_cat_def]);

val functor_cat_mor_is_nat_trans = Q.store_thm(
"functor_cat_mor_is_nat_trans",
`∀c1 c2 f. f ∈ [c1→c2].mor ⇒ is_nat_trans f`,
srw_tac [][functor_cat_def]);

val functor_cat_dist = Q.store_thm(
"functor_cat_dist",
`∀c1 c2 f g x. f ≈> g -:[c1→c2] ∧ x ∈ c1.obj ⇒
   ((g o f -:[c1→c2])@+x = (g@+x) o (f@+x) -:c2)`,
srw_tac [][] >>
imp_res_tac functor_cat_composable_in >>
srw_tac [][functor_cat_compose_in] >>
imp_res_tac composable_nts_def >>
srw_tac [][nt_comp_at]);

val _ = export_rewrites[
"is_category_functor_cat","functor_cat_obj","functor_cat_mor",
"functor_cat_id","functor_cat_comp","functor_cat_compose_in",
"functor_cat_composable_in","functor_cat_maps_to","functor_cat_dist",
"functor_cat_mor_is_nat_trans"];

val functor_cat_iso_pair = Q.store_thm(
"functor_cat_iso_pair",
`∀n1 n2 c1 c2. n1 <≃> n2 -:[c1→c2] = n1 ≈> n2 -:[c1→c2] ∧ n2 ≈> n1 -:[c1→c2] ∧ (∀x. x ∈ c1.obj ⇒ n1@+x <≃> n2@+x -:c2)`,
srw_tac [][iso_pair_def] >> EQ_TAC >> strip_tac >> fsrw_tac [][] >- (
  conj_asm1_tac >- (
    fsrw_tac [][composable_nts_def] >>
    `(n2 o n1 -:[c1→c2]).cod = (id n1.dom -:[c1→c2]).cod` by srw_tac [][] >>
    qpat_assum `X = id n1.dom -:C` (K ALL_TAC) >>
    pop_assum mp_tac >> fsrw_tac [][composable_nts_def] >>
    `n1.dom ∈ [c1→c2].obj` by (
      fsrw_tac [][composable_nts_def,is_nat_trans_is_functor] >>
      fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
    srw_tac [][] ) >>
  qx_gen_tac `x` >> strip_tac >>
  conj_tac >- (
    match_mp_tac maps_to_composable >>
    map_every qexists_tac [`n1.dom@@x`,`n1.cod@@x`,`n2.cod@@x`] >>
    conj_tac >- (
      match_mp_tac nt_at_maps_to >>
      map_every qexists_tac [`n1.dom`,`n1.cod`] >>
      fsrw_tac [][composable_nts_def] ) >>
    match_mp_tac nt_at_maps_to >>
    map_every qexists_tac [`n2.dom`,`n2.cod`] >>
    fsrw_tac [][composable_nts_def] ) >>
  reverse conj_tac >- (
    `(n2 o n1 -:[c1→c2]) @+ x = (id n1.dom -:[c1→c2]) @+ x` by metis_tac [] >>
    qpat_assum `n2 o n1 -:[c1→c2] = X` (K ALL_TAC) >>
    pop_assum mp_tac >> fsrw_tac [][] >> strip_tac >>
    `n1.dom ∈ [c1→c2].obj` by (
      fsrw_tac [][composable_nts_def,is_nat_trans_is_functor] >>
      fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
    fsrw_tac [][] >>
    `n1 @+ x :- n1.dom@@x → n1.cod@@x -:c2` by (
      match_mp_tac nt_at_maps_to >>
      map_every qexists_tac [`n1.dom`,`n1.cod`] >>
      fsrw_tac [][composable_nts_def] ) >>
    fsrw_tac [][maps_to_in_def] ) >>
  `(n1 o n2 -:[c1→c2]) @+ x = (id n2.dom -:[c1→c2]) @+ x` by metis_tac [] >>
  qpat_assum `n1 o n2 -:[c1→c2] = X` (K ALL_TAC) >>
  pop_assum mp_tac >> fsrw_tac [][] >> strip_tac >>
  `n2.dom ∈ [c1→c2].obj` by(
    fsrw_tac [][composable_nts_def,is_nat_trans_is_functor] >>
    fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
  fsrw_tac [][] >>
  `n2 @+ x :- n2.dom@@x → n2.cod@@x -:c2` by (
    match_mp_tac nt_at_maps_to >>
    map_every qexists_tac [`n2.dom`,`n2.cod`] >>
    fsrw_tac [][composable_nts_def] ) >>
  fsrw_tac [][maps_to_in_def] ) >>
`n1.dom ∈ [c1→c2].obj ∧ n2.dom ∈ [c1→c2].obj` by (
  fsrw_tac [][composable_nts_def,is_nat_trans_is_functor] >>
  fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] ) >>
fsrw_tac [][] >>
srw_tac [][] >>
match_mp_tac nt_eq_thm >>
srw_tac [][] >>
fsrw_tac [][composable_nts_def] >>
pop_assum mp_tac >> srw_tac [][] >>
`n1 @+ x :- n1.dom@@x → n1.cod@@x -:n1.dom.cod` by (
  match_mp_tac nt_at_maps_to >>
  map_every qexists_tac [`n1.dom`,`n1.cod`] >>
  fsrw_tac [][] ) >>
`n2 @+ x :- n2.dom@@x → n2.cod@@x -:n2.dom.cod` by (
  match_mp_tac nt_at_maps_to >>
  map_every qexists_tac [`n2.dom`,`n2.cod`] >>
  fsrw_tac [][] ) >>
fsrw_tac [][maps_to_in_def]);

(*
val functor_cat_iso_objs = Q.store_thm(
"functor_cat_iso_objs",
`∀c1 c2 f g. f ≅ g -:[c1→c2] = (∀h. h ∈ c1.mor ⇒ f##h <≃> g##h -:c2)`,
srw_tac [][iso_objs_def,iso_pair_between_objs_def,functor_cat_iso_pair] >>
EQ_TAC >> strip_tac >- (
  qx_gen_tac `k` >>
  strip_tac >>
  simp_tac (srw_ss()) [iso_pair_def] >>
  conj_tac >- (
    match_mp_tac maps_to_composable >>
    map_every qexists_tac [`f@@k.dom`,`f@@k.cod`,`g@@k.cod`] >>
    conj_tac >- (
      match_mp_tac morf_maps_to >>
      map_every qexists_tac [`c1`,`k.dom`,`k.cod`] >>
      fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
      metis_tac [] ) >>
    match_mp_tac morf_maps_to >>
    map_every qexists_tac [`c1`,`k.dom`,`k.cod`] >>
    fsrw_tac [][is_nat_trans_def,nat_trans_axioms_def] >>
    conj_tac >- metis_tac [] >>
    conj_tac >- metis_tac [] >>
    metis_tac []
*)

val pre_eval_functor_def = Define`
  pre_eval_functor c v p = <|
    dom := [c→v]; cod := v;
    map := λn. n @+ p |>`;

val pre_eval_functor_components = Q.store_thm(
"pre_eval_functor_components",
`∀c v p. ((pre_eval_functor c v p).dom = [c→v]) ∧
         ((pre_eval_functor c v p).cod = v) ∧
         (∀n. (pre_eval_functor c v p)##n = n @+ p)`,
srw_tac [][pre_eval_functor_def,morf_def]);
val _ = export_rewrites["pre_eval_functor_components"];

val pre_eval_functor_objf = Q.store_thm(
"pre_eval_functor_objf",
`∀c v x p. is_category c ∧ is_category v ∧ p ∈ [c→v].obj ∧ x ∈ c.obj ⇒
  ((pre_eval_functor c v x)@@p = p@@x)`,
srw_tac [][Once objf_def] >>
SELECT_ELIM_TAC >>
metis_tac [objf_in_obj,id_inj]);

val eval_functor_def = Define`
  eval_functor c v p = mk_functor (pre_eval_functor c v p)`;

val is_functor_eval_functor = Q.store_thm(
"is_functor_eval_functor",
`∀c v p. is_category c ∧ is_category v ∧ p ∈ c.obj ⇒
  is_functor (eval_functor c v p)`,
srw_tac [][eval_functor_def] >>
srw_tac [][functor_axioms_def] >- (
  fsrw_tac [][pre_eval_functor_objf] >>
  match_mp_tac nt_at_maps_to >>
  metis_tac [maps_to_def] )
>- metis_tac [objf_in_obj] >>
fsrw_tac [][composable_nts_def]);
val _ = export_rewrites["is_functor_eval_functor"];

val eval_functor_dom_cod = Q.store_thm(
"eval_functor_dom_cod",
`∀c v p. ((eval_functor c v p).dom = [c→v]) ∧
         ((eval_functor c v p).cod = v)`,
srw_tac [][eval_functor_def]);
val _ = export_rewrites["eval_functor_dom_cod"];

val eval_functor_morf_objf = Q.store_thm(
"eval_functor_morf_objf",
`∀c v p. is_category c ∧ is_category v ∧ p ∈ c.obj ⇒
  (∀x. x ∈ [c→v].obj ⇒ ((eval_functor c v p)@@x = x@@p)) ∧
  (∀f. f ∈ [c→v].mor ⇒ ((eval_functor c v p)##f = f @+ p))`,
srw_tac [][eval_functor_def,pre_eval_functor_objf]);
val _ = export_rewrites["eval_functor_morf_objf"];

val id_nt_inj = Q.store_thm(
"id_nt_inj",
`∀f g. is_functor f ∧ is_functor g ∧ (id_nt f = id_nt g) ⇒ (f = g)`,
srw_tac [][] >>
Q.ISPEC_THEN `[f.dom→f.cod]` assume_tac id_inj >>
pop_assum match_mp_tac >>
imp_res_tac is_functor_is_category >>
imp_res_tac is_category_functor_cat >>
srw_tac [][] >> fsrw_tac [][id_nt_def,mk_nt_def]);

val K_nt_def = Define`
  K_nt j c f = mk_nt <| dom := K_functor j c f.dom; cod := K_functor j c f.cod; map := K f |>`;

val is_nat_trans_K_nt = Q.store_thm(
"is_nat_trans_K_nt",
`∀j c f. is_category j ∧ is_category c ∧ f ∈ c.mor ⇒ is_nat_trans (K_nt j c f)`,
srw_tac [][K_nt_def] >>
`f.dom ∈ c.obj ∧ f.cod ∈ c.obj` by metis_tac [mor_obj] >>
srw_tac [][nat_trans_axioms_def] >>
fsrw_tac [][maps_to_in_def]);

val K_nt_dom = Q.store_thm(
"K_nt_dom",
`∀j c f. (K_nt j c f).dom = K_functor j c f.dom`,
srw_tac [][K_nt_def]);

val K_nt_cod = Q.store_thm(
"K_nt_cod",
`∀j c f. (K_nt j c f).cod = K_functor j c f.cod`,
srw_tac [][K_nt_def]);

val K_nt_at = Q.store_thm(
"K_nt_at",
`∀c j f x. x ∈ j.obj ⇒ ((K_nt j c f)@+x = f)`,
srw_tac [][K_nt_def,mk_nt_def,restrict_def]);

val K_nt_id = Q.store_thm(
"K_nt_id",
`∀j c x. is_category j ∧ is_category c ∧ x ∈ c.obj ⇒ (K_nt j c (id x -:c) = id_nt (K_functor j c x))`,
srw_tac [][] >>
match_mp_tac nt_eq_thm >>
imp_res_tac id_mor >>
srw_tac [][id_dom_cod,K_nt_dom,
           K_nt_cod,K_nt_dom,K_nt_at,is_nat_trans_K_nt] >>
srw_tac [][id_nt_at]);

val K_nt_maps_to = Q.store_thm(
"K_nt_maps_to",
`∀j c f x y. is_category j ∧ is_category c ∧ f :- x → y -:c ⇒
  (K_nt j c f) :- (K_functor j c x) → (K_functor j c y)`,
srw_tac [][maps_to_in_def,K_nt_dom,K_nt_cod]);

val _ = export_rewrites
["is_nat_trans_K_nt","K_nt_dom","K_nt_cod","K_nt_at",
 "K_nt_id","K_nt_maps_to"];

val pre_diagonal_functor_def = Define`
  pre_diagonal_functor j c = <|
    dom := c; cod := [j→c]; map := K_nt j c |>`;

val pre_diagonal_functor_dom = Q.store_thm(
"pre_diagonal_functor_dom",
`∀c j. (pre_diagonal_functor j c).dom = c`,
srw_tac [][pre_diagonal_functor_def]);

val pre_diagonal_functor_cod = Q.store_thm(
"pre_diagonal_functor_cod",
`∀c j. (pre_diagonal_functor j c).cod = [j→c]`,
srw_tac [][pre_diagonal_functor_def]);

val _ = export_rewrites ["pre_diagonal_functor_dom","pre_diagonal_functor_cod"];

val pre_diagonal_functor_objf = Q.store_thm(
"pre_diagonal_functor_objf",
`∀c j x. is_category c ∧ is_category j ∧ x ∈ c.obj ⇒
((pre_diagonal_functor j c)@@x = K_functor j c x)`,
srw_tac [][objf_def,morf_def] >>
srw_tac [][pre_diagonal_functor_def] >>
SELECT_ELIM_TAC >>
srw_tac [][] >- (
  qexists_tac `K_functor j c x` >>
  fsrw_tac [][] ) >>
pop_assum mp_tac >> srw_tac [][] >>
fsrw_tac [][morphism_component_equality]);
val _ = export_rewrites["pre_diagonal_functor_objf"];

val diagonal_functor_def = Define`
  diagonal_functor j c = mk_functor (pre_diagonal_functor j c)`;
val _ = overload_on("\226\150\179",``diagonal_functor``);

val is_functor_diagonal_functor = Q.store_thm(
"is_functor_diagonal_functor",
`∀c j. is_category c ∧ is_category j ⇒ is_functor (△ c j)`,
srw_tac [][diagonal_functor_def] >>
srw_tac [][functor_axioms_def] >>
imp_res_tac maps_to_obj >>
imp_res_tac maps_to_in_def >>
fsrw_tac [][morf_def,pre_diagonal_functor_def] >- (
  qexists_tac `K_functor c j x` >>
  srw_tac [][] ) >>
imp_res_tac composable_in_def >>
`K_nt c j f ≈≈> K_nt c j g` by (
  srw_tac [][composable_nts_def] >>
  fsrw_tac [][morphism_component_equality] ) >>
srw_tac [][] >>
imp_res_tac comp_mor_dom_cod >>
match_mp_tac nt_eq_thm >>
fsrw_tac [][] >>
srw_tac [][nt_comp_def,K_functor_def]);

val diagonal_functor_dom_cod = Q.store_thm(
"diagonal_functor_dom_cod",
`∀j c. ((diagonal_functor j c).dom = c) ∧
       ((diagonal_functor j c).cod = [j→c])`,
srw_tac [][diagonal_functor_def]);
val _ = export_rewrites["diagonal_functor_dom_cod"];

val diagonal_functor_morf = Q.store_thm(
"diagonal_functor_morf",
`∀c j f. f ∈ c.mor ⇒ ((diagonal_functor j c)##f = K_nt j c f)`,
srw_tac [][diagonal_functor_def,morf_def,pre_diagonal_functor_def,mk_functor_def,restrict_def]);
val _ = export_rewrites["diagonal_functor_morf"];

val diagonal_functor_objf = Q.store_thm(
"diagonal_functor_objf",
`∀c j x. is_category c ∧ is_category j ∧ x ∈ c.obj ⇒
((diagonal_functor j c)@@x = K_functor j c x)`,
srw_tac [][diagonal_functor_def]);
val _ = export_rewrites["diagonal_functor_objf"];

val pre_itself_functor_def = Define`
  pre_itself_functor f =
    <| dom := unit_cat; cod := [f.dom→f.cod]; map := K (id_nt f) |>`;

val pre_itself_functor_components = Q.store_thm(
"pre_itself_functor_components",
`∀f. ((pre_itself_functor f).dom = unit_cat) ∧
     ((pre_itself_functor f).cod = [f.dom→f.cod]) ∧
     ((pre_itself_functor f).map = K (id_nt f))`,
srw_tac [][pre_itself_functor_def]);
val _ = export_rewrites["pre_itself_functor_components"];

val pre_itself_functor_morf = Q.store_thm(
"pre_itself_functor_morf",
`∀f u. (pre_itself_functor f)##u = (id_nt f)`,
srw_tac [][morf_def]);

val pre_itself_functor_objf = Q.store_thm(
"pre_itself_functor_objf",
`∀f u. is_functor f ⇒ ((pre_itself_functor f)@@u = f)`,
srw_tac [][objf_def,morf_def] >>
SELECT_ELIM_TAC >>
conj_tac >- (
  qexists_tac `f` >>
  `f ∈ [f.dom→f.cod].obj` by srw_tac [][] >>
  srw_tac [][] ) >>
qx_gen_tac `g` >> strip_tac >>
`g ∈ [f.dom→f.cod].obj` by srw_tac [][] >>
fsrw_tac [][] >>
Q.ISPEC_THEN `[f.dom→f.cod]` (match_mp_tac o GSYM) id_inj >>
srw_tac [][is_functor_is_category]);

val _ = export_rewrites["pre_itself_functor_morf","pre_itself_functor_objf"];

val itself_functor_def = Define`
  itself_functor f = mk_functor (pre_itself_functor f)`;

val is_functor_itself_functor = Q.store_thm(
"is_functor_itself_functor",
`∀f. is_functor f ⇒ is_functor (itself_functor f)`,
srw_tac [][itself_functor_def] >>
srw_tac [][functor_axioms_def] >>
srw_tac [][is_functor_is_category] >- (
  qexists_tac `f` >> srw_tac [][] ) >>
Q.ISPECL_THEN [`[f.dom→f.cod]`,`f`] mp_tac id_comp_id >>
asm_simp_tac std_ss
[is_functor_is_category,is_category_functor_cat,functor_cat_obj,maps_to_def,functor_cat_id] >>
srw_tac [][]);

val itself_functor_components = Q.store_thm(
"itself_functor_components",
`∀f. ((itself_functor f).dom = unit_cat) ∧
     ((itself_functor f).cod = [f.dom→f.cod]) ∧
     ((itself_functor f).map = K (id_nt f))`,
srw_tac [][itself_functor_def,mk_functor_def,restrict_def,FUN_EQ_THM]);
val _ = export_rewrites["itself_functor_components"];

val itself_functor_morf = Q.store_thm(
"itself_functor_morf",
`∀f u. (itself_functor f)##u = (id_nt f)`,
srw_tac [][morf_def]);

val itself_functor_objf = Q.store_thm(
"itself_functor_objf",
`∀f u. is_functor f ⇒ ((itself_functor f)@@u = f)`,
srw_tac [][itself_functor_def]);
val _ = export_rewrites["itself_functor_morf","itself_functor_objf"];

val equivalence_pair_def = Define`
  equivalence_pair f g = (f ≈> g) ∧ (g ≈> f) ∧
    (f ◎ g ≅ id_functor g.dom -:[g.dom→g.dom]) ∧
    (g ◎ f ≅ id_functor f.dom -:[f.dom→f.dom])`;

val equivalence_def = Define`
  equivalence f = ∃g. is_functor g ∧ equivalence_pair f g`;

(*
val equivalence_full_faithful_ess_surj = Q.store_thm(
"equivalence_full_faithful_ess_surj", (* Mac Lane pp 91-92 *)
`∀f. is_functor f ⇒ (equivalence f = full f ∧ faithful f ∧ ess_surj_obj f)`,
gen_tac >> strip_tac >> EQ_TAC >> strip_tac >- (
  fsrw_tac [][equivalence_def,equivalence_pair_def] >>
  fsrw_tac [][iso_objs_def,iso_pair_between_objs_def] >>
  qmatch_assum_rename_tac `n1.dom = g ◎ f` [] >>
  qmatch_assum_abbrev_tac `X = g ◎ f` >>
  qmatch_assum_rename_tac `n2.dom = f ◎ g` [] >>
  qunabbrev_tac `X` >>
  `∀h x y. h :- x → y -:f.dom ⇒ (n1 @+ y o (g ◎ f)##h -:f.dom = ((id_functor f.dom)##h) o n1 @+ x -:f.dom)` by (
    rpt gen_tac >> strip_tac >>
    match_mp_tac naturality >>
    fsrw_tac [][functor_cat_iso_pair,composable_nts_def] ) >>
  imp_res_tac is_functor_is_category >>
  `∀a. a ∈ f.dom.obj ⇒ (n1 @+ a) :- (g ◎ f)@@a → a -:f.dom` by (
    srw_tac [][] >>
    match_mp_tac nt_at_maps_to >>
    map_every qexists_tac [`n1.dom`,`n1.cod`] >>
    fsrw_tac [][functor_cat_iso_pair,composable_nts_def]) >>
  `faithful f` by (
    simp_tac (srw_ss()) [faithful_def] >>
    map_every qx_gen_tac [`k1`,`k2`,`a`,`b`] >>
    strip_tac >>
    first_assum (qspecl_then [`k1`,`a`,`b`] mp_tac) >>
    first_x_assum (qspecl_then [`k2`,`a`,`b`] mp_tac) >>
    `k1 ∈ f.dom.mor ∧ k2 ∈ f.dom.mor` by fsrw_tac [][maps_to_in_def] >>
    srw_tac [][] >>
    `(k1 o n1 @+ a -:f.dom) o (n1 @+ a)⁻¹ -:f.dom -:f.dom =
     (k2 o n1 @+ a -:f.dom) o (n1 @+ a)⁻¹ -:f.dom -:f.dom` by srw_tac [][] >>
    pop_assum mp_tac >>
    `iso f.dom (n1 @+ a)` by (
      metis_tac [iso_def,functor_cat_iso_pair,maps_to_obj] ) >>
    qpat_assum `k2 o X -:f.dom = k1 o Y -:f.dom` (K ALL_TAC) >>
    `(n1 @+ a)⁻¹-:f.dom ≈> n1 @+ a -:f.dom` by (
      metis_tac [inv_composable,inv_idem] ) >>
    `a ∈ f.dom.obj` by metis_tac [maps_to_obj] >>
    `n1 @+ a ≈> k1 -:f.dom` by ( metis_tac [maps_to_composable] ) >>
    `n1 @+ a ≈> k2 -:f.dom` by ( metis_tac [maps_to_composable] ) >>
    fsrw_tac [][comp_inv_id,comp_assoc,maps_to_in_def] ) >>
  `∀h x y. h :- x → y -:g.dom ⇒ (n2 @+ y o (f ◎ g)##h -:g.dom = ((id_functor g.dom)##h) o n2 @+ x -:g.dom)` by (
    rpt gen_tac >> strip_tac >>
    match_mp_tac naturality >>
    fsrw_tac [][functor_cat_iso_pair,composable_nts_def] ) >>
  `∀a. a ∈ g.dom.obj ⇒ (n2 @+ a) :- (f ◎ g)@@a → a -:g.dom` by (
    srw_tac [][] >>
    match_mp_tac nt_at_maps_to >>
    map_every qexists_tac [`n2.dom`,`n2.cod`] >>
    fsrw_tac [][functor_cat_iso_pair,composable_nts_def]) >>
  `faithful g` by (
    simp_tac (srw_ss()) [faithful_def] >>
    map_every qx_gen_tac [`k1`,`k2`,`a`,`b`] >>
    strip_tac >>
    first_assum (qspecl_then [`k1`,`a`,`b`] mp_tac) >>
    first_x_assum (qspecl_then [`k2`,`a`,`b`] mp_tac) >>
    `k1 ∈ g.dom.mor ∧ k2 ∈ g.dom.mor` by fsrw_tac [][maps_to_in_def] >>
    srw_tac [][] >>
    `(k1 o n2 @+ a -:g.dom) o (n2 @+ a)⁻¹ -:g.dom -:g.dom =
     (k2 o n2 @+ a -:g.dom) o (n2 @+ a)⁻¹ -:g.dom -:g.dom` by srw_tac [][] >>
    pop_assum mp_tac >>
    `iso g.dom (n2 @+ a)` by (
      metis_tac [iso_def,functor_cat_iso_pair,maps_to_obj] ) >>
    qpat_assum `k2 o X -:g.dom = k1 o Y -:g.dom` (K ALL_TAC) >>
    `(n2 @+ a)⁻¹-:g.dom ≈> n2 @+ a -:g.dom` by (
      metis_tac [inv_composable,inv_idem] ) >>
    `a ∈ g.dom.obj` by metis_tac [maps_to_obj] >>
    `n2 @+ a ≈> k1 -:g.dom` by ( metis_tac [maps_to_composable] ) >>
    `n2 @+ a ≈> k2 -:g.dom` by ( metis_tac [maps_to_composable] ) >>
    fsrw_tac [][comp_inv_id,comp_assoc,maps_to_in_def] )
  `full f` by (
    srw_tac [][full_def] >>
    qabbrev_tac `w = n1 @+ b o (g##h) o (n1 @+ a)⁻¹ -:f.dom -:f.dom -:f.dom` >>
    qexists_tac `w` >>
    `n1 @+ a :- (g ◎ f)@@a → a -:f.dom` by metis_tac [] >>
    `(n1 @+ a)⁻¹ -: f.dom :- a → (g ◎ f)@@a -:f.dom` by (
      match_mp_tac inv_maps_to >>
      fsrw_tac [][maps_to_in_def] >>
      srw_tac [][iso_def] >>
      fsrw_tac [][functor_cat_iso_pair] >>
      metis_tac [] ) >>
    conj_asm1_tac >- (
      qunabbrev_tac `w` >>
      match_mp_tac maps_to_comp >>
      qexists_tac `(g ◎ f)@@b` >>
      conj_tac >- srw_tac [][] >>
      conj_tac >- (
        match_mp_tac maps_to_comp >>
        qexists_tac `(g ◎ f)@@a` >>
        conj_tac >- srw_tac [][] >>
        conj_tac >- srw_tac [][] >>
        match_mp_tac morf_maps_to >>
        map_every qexists_tac [`g.dom`,`f@@a`,`f@@b`] >>
        fsrw_tac [][] ) >>
      srw_tac [][] ) >>
    `g##h :- g@@(f@@a) → g@@(f@@b) -:f.dom` by (
      match_mp_tac morf_maps_to >>
      fsrw_tac [][] >> metis_tac [] ) >>
    qsuff_tac `f##w :- f@@a → f@@b -:g.dom ∧ (g##(f##w) = g##h)` >-
      metis_tac [faithful_def] >>
    conj_asm1_tac >- (
      match_mp_tac morf_maps_to >>
      map_every qexists_tac [`f.dom`,`a`,`b`] >>
      fsrw_tac [][] >>
      qunabbrev_tac `w` >>
      match_mp_tac maps_to_comp >>
      qexists_tac `(g ◎ f)@@b` >>
      fsrw_tac [][] >>
      match_mp_tac maps_to_comp >>
      qexists_tac `(g ◎ f)@@a` >>
      fsrw_tac [][] ) >>
    first_x_assum (qspecl_then [`w`,`a`,`b`] mp_tac) >>
    `w ∈ f.dom.mor` by fsrw_tac [][maps_to_in_def] >>
    srw_tac [][] >>
    `((n1 @+ b)⁻¹-:f.dom) o (n1 @+ b o g##(f##w) -:f.dom) -:f.dom =
     ((n1 @+ b)⁻¹-:f.dom) o (w o n1 @+ a -:f.dom) -:f.dom` by srw_tac [][] >>
    pop_assum mp_tac >>
    qpat_assum `n1 @+ b o X -:f.dom = Y` (K ALL_TAC) >>
    `g##(f##w) ≈> n1 @+ b -:f.dom` by (
      match_mp_tac maps_to_composable >>
      map_every qexists_tac [`g@@(f@@a)`,`g@@(f@@b)`,`b`] >>
      conj_tac >- (
        match_mp_tac morf_maps_to >>
        map_every qexists_tac [`g.dom`,`f@@a`,`f@@b`] >>
        srw_tac [][] ) >>
      metis_tac [functor_comp_objf,composable_def] ) >>
    `iso f.dom (n1 @+ b)` by (
      fsrw_tac [][iso_def,functor_cat_iso_pair] >>
      metis_tac [] ) >>
    `n1 @+ b ≈> (n1 @+ b)⁻¹-:f.dom -:f.dom` by (
      metis_tac [inv_composable] ) >>
    `g##(f##w) ∈ f.dom.mor ∧ ((n1 @+ b).dom = (g##(f##w)).cod)` by (
      fsrw_tac [][composable_in_def] ) >>
    fsrw_tac [][GSYM comp_assoc,comp_inv_id] >>
    strip_tac >>
    qunabbrev_tac `w` >>
    qabbrev_tac `c = f.dom` >>
    qmatch_abbrev_tac `(q1⁻¹-:c) o (q1 o gh o (q2⁻¹-:c) -:c -:c) o q2 -:c -:c = gh` >>
    `iso c q2` by (
      fsrw_tac [][iso_def,functor_cat_iso_pair,Abbr`q2`] >>
      metis_tac [] ) >>
    `q2 ≈> (q2⁻¹-:c) -:c` by fsrw_tac [][inv_composable] >>
    `(q2⁻¹-:c) ≈> gh -:c` by (
      match_mp_tac maps_to_composable >>
      metis_tac [functor_comp_objf,composable_def] ) >>
    `gh ≈> q1 -:c` by (
      match_mp_tac maps_to_composable >>
      metis_tac [functor_comp_objf,composable_def] ) >>
    `q1 ≈> (q1⁻¹-:c) -:c` by metis_tac [inv_composable] >>
    `gh o q2⁻¹-:c -:c ≈> q1 -:c` by metis_tac [composable_comp] >>
    `q2 ≈> (q1 o gh o q2⁻¹-:c -:c -:c) -:c` by metis_tac [composable_comp] >>
    qsuff_tac `((q1⁻¹-:c) o (q1 o gh o q2⁻¹-:c -:c -:c) -:c) o q2 -:c = gh` >-
      metis_tac [composable_comp,comp_assoc] >>
    qsuff_tac `(((q1⁻¹-:c) o q1 -:c) o (gh o (q2⁻¹-:c) -:c) -:c) o q2 -:c = gh` >-
      metis_tac [composable_comp,comp_assoc] >>
    qsuff_tac `(((q1⁻¹-:c) o q1 -:c) o gh -:c) o ((q2⁻¹-:c) o q2 -:c) -:c = gh` >-
      metis_tac [composable_comp,comp_assoc] >>
    fsrw_tac [][comp_inv_id,composable_in_def] >>
    match_mp_tac id_comp1 >>
    fsrw_tac [][] >>
    imp_res_tac maps_to_in_def >>
    fsrw_tac [][] ) >>
  srw_tac [boolSimps.DNF_ss][ess_surj_obj_def,iso_objs_def,iso_pair_between_objs_def] >>
  map_every qexists_tac [`g@@b`,`n2 @+ b`,`(n2 @+ b)⁻¹-:g.dom`] >>
  conj_tac >- metis_tac [objf_in_obj] >>
  first_x_assum (qspec_then `b` mp_tac) >>
  srw_tac [][maps_to_in_def] >>
  srw_tac [][inv_in_def] >>
  SELECT_ELIM_TAC >>
  srw_tac [][] >>
  fsrw_tac [][functor_cat_iso_pair] >>
  metis_tac [] ) >>
*)

val _ = export_theory ();
