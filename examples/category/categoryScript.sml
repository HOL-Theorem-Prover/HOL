open HolKernel boolLib bossLib

val _ = new_theory "category"

val extensional_def = Define`
  extensional f x = !e. e NOTIN x ==> (f e = ARB)`

val restrict_def = Define`
  restrict f x = \e. if e IN x then f e else ARB`

val extensional_restrict = Q.store_thm(
"extensional_restrict",
`extensional (restrict f x) x`,
SRW_TAC [][extensional_def,restrict_def])

val _ = Hol_datatype `category =
  <| obj : 'a set ;
     mor : 'b set ;
     dom : 'b -> 'a ;
     cod : 'b -> 'a ;
     id : 'a -> 'b ;
     comp : 'b # 'b -> 'b |>`

val maps_to_def = Define`
  maps_to c f x y = f IN c.mor /\ (c.dom f = x) /\ (c.cod f = y)`

val composable_def = Define`
  composable c gf = (SND gf) IN c.mor /\ (FST gf) IN c.mor /\
                    (c.cod (SND gf) = c.dom (FST gf))`

val extensional_category_def = Define`
  extensional_category c =
    extensional c.dom c.mor /\
    extensional c.cod c.mor /\
    extensional c.id c.obj /\
    extensional c.comp (composable c)`

val category_axioms_def = Define`
  category_axioms c =
    (!f. f IN c.mor ==> c.dom f IN c.obj) /\
    (!f. f IN c.mor ==> c.cod f IN c.obj) /\
    (!a. a IN c.obj ==> maps_to c (c.id a) a a) /\
    (!f. f IN c.mor ==> (c.comp (f, c.id (c.dom f)) = f)) /\
    (!f. f IN c.mor ==> (c.comp (c.id (c.cod f), f) = f)) /\
    (!f g h. composable c (g,f) /\ composable c (h,g) ==>
             (c.comp (h, (c.comp (g,f))) = c.comp (c.comp (h,g), f))) /\
    (!f g x y z. maps_to c f x y /\ maps_to c g y z ==>
                 maps_to c (c.comp (g,f)) x z)`

val is_category_def = Define`
  is_category c = extensional_category c /\ category_axioms c`

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
`maps_to (mk_cat c) f x y = maps_to c f x y`,
SRW_TAC [][maps_to_def,mk_cat_def,restrict_def])

val mk_cat_composable = Q.store_thm(
"mk_cat_composable",
`composable (mk_cat c) gf = composable c gf`,
SRW_TAC [][composable_def,mk_cat_def,restrict_def])

val mk_cat_id = Q.store_thm(
"mk_cat_id",
`a IN c.obj ==> ((mk_cat c).id a = c.id a)`,
SRW_TAC [][mk_cat_def,restrict_def])

val mk_cat_obj = Q.store_thm(
"mk_cat_obj",
`(mk_cat c).obj = c.obj`,
SRW_TAC [][mk_cat_def])

val mk_cat_mor = Q.store_thm(
"mk_cat_obj",
`(mk_cat c).mor = c.mor`,
SRW_TAC [][mk_cat_def])

val mk_cat_dom = Q.store_thm(
"mk_cat_dom",
`f IN c.mor ==> ((mk_cat c).dom f = c.dom f)`,
SRW_TAC [][mk_cat_def,restrict_def])

val mk_cat_cod = Q.store_thm(
"mk_cat_cod",
`f IN c.mor ==> ((mk_cat c).cod f = c.cod f)`,
SRW_TAC [][mk_cat_def,restrict_def])

val mk_cat_composable = Q.store_thm(
"mk_cat_composable",
`composable (mk_cat c) = composable c `,
SRW_TAC [][FUN_EQ_THM] THEN
METIS_TAC [composable_def,mk_cat_cod,mk_cat_dom,mk_cat_mor])

val mk_cat_comp = Q.store_thm(
"mk_cat_comp",
`composable c gf ==> ((mk_cat c).comp gf = c.comp gf)`,
SRW_TAC [][mk_cat_def,restrict_def,IN_DEF])

val extensional_mk_cat = Q.store_thm(
"extensional_mk_cat",
`extensional_category (mk_cat c)`,
SRW_TAC [][extensional_category_def]
THEN1 SRW_TAC [][mk_cat_def,extensional_restrict]
THEN1 SRW_TAC [][mk_cat_def,extensional_restrict]
THEN1 SRW_TAC [][mk_cat_def,extensional_restrict] THEN
SRW_TAC [][Once mk_cat_def,mk_cat_composable,extensional_restrict])

val mk_cat_is_category = Q.store_thm(
"mk_cat_is_category",
`category_axioms c ==> is_category (mk_cat c)`,
SRW_TAC [][is_category_def,extensional_mk_cat] THEN
FULL_SIMP_TAC (srw_ss()) [category_axioms_def] THEN
CONJ_TAC THEN1 SRW_TAC [][mk_cat_mor,mk_cat_dom,mk_cat_obj] THEN
CONJ_TAC THEN1 SRW_TAC [][mk_cat_mor,mk_cat_cod,mk_cat_obj] THEN
CONJ_TAC THEN1 SRW_TAC [][mk_cat_obj,mk_cat_maps_to,mk_cat_id] THEN
CONJ_TAC THEN1 (
  SRW_TAC [][mk_cat_mor,mk_cat_id,mk_cat_dom] THEN
  `composable c (f,c.id (c.dom f))` by (
    FULL_SIMP_TAC (srw_ss()) [maps_to_def,composable_def] ) THEN
  SRW_TAC [][mk_cat_comp] ) THEN
CONJ_TAC THEN1 (
  SRW_TAC [][mk_cat_mor,mk_cat_id,mk_cat_cod] THEN
  `composable c (c.id (c.cod f),f)` by (
    FULL_SIMP_TAC (srw_ss()) [maps_to_def,composable_def] ) THEN
  SRW_TAC [][mk_cat_comp] ) THEN
CONJ_TAC THEN1 (
  SRW_TAC [][mk_cat_composable,mk_cat_comp] THEN
  `composable c (c.comp (h,g),f)` by (
    FULL_SIMP_TAC (srw_ss()) [composable_def,maps_to_def] ) THEN
  `composable c (h,c.comp (g,f))` by (
    FULL_SIMP_TAC (srw_ss()) [composable_def,maps_to_def] ) THEN
  SRW_TAC [][mk_cat_comp] ) THEN
SRW_TAC [][mk_cat_maps_to] THEN
`composable c (g,f)` by (
  FULL_SIMP_TAC (srw_ss()) [composable_def,maps_to_def] ) THEN
SRW_TAC [][mk_cat_comp] THEN
FULL_SIMP_TAC (srw_ss()) [maps_to_def,composable_def])

val _ = export_theory ()
