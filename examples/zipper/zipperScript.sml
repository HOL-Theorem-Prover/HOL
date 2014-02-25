open HolKernel Parse boolLib bossLib;

open lcsymtacs
fun asimp thl = asm_simp_tac(srw_ss() ++ ARITH_ss) thl

val _ = new_theory "zipper";

val _ = ParseExtras.tight_equality()

val _ = Hol_datatype `zipper = Z of 'a list => 'a => 'a list`

val focus_def = Define`focus (Z p a s) = a`
val toList_def = Define`toList (Z p a s) = REVERSE p ++ [a] ++ s`
val size_def = Define`size (Z p a s) = LENGTH p + LENGTH s + 1`
val index_def = Define`index (Z p a s) = LENGTH p`
val _ = export_rewrites ["focus_def", "toList_def", "size_def", "index_def"]

val index_invariant = store_thm(
  "index_invariant",
  ``index z < size z``,
  Cases_on `z` >> simp[]);

val size_nonzero = store_thm(
  "size_nonzero",
  ``0 < size z``,
  Cases_on `z` >> simp[]);
val _ = export_rewrites ["size_nonzero"]

val LENGTH_toList = store_thm(
  "LENGTH_toList",
  ``LENGTH (toList z) = size z``,
  Cases_on `z` >> simp[]);
val _ = export_rewrites ["LENGTH_toList"]

val moveLeft_def = Define`
  (moveLeft (Z [] a s) = NONE) ∧
  (moveLeft (Z (h::t) a s) = SOME (Z t h (a::s)))
`

val moveRight_def = Define`
  (moveRight (Z p a []) = NONE) ∧
  (moveRight (Z p a (h::t)) = SOME (Z (a::p) h t))
`;

val moveLeft_invariant = store_thm(
  "moveLeft_invariant",
  ``moveLeft z = SOME z' ⇒ toList z = toList z' ∧ index z = index z' + 1``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> rw[moveLeft_def] >> rw[toList_def, index_def, arithmeticTheory.ADD1])

val moveLeft_possible = store_thm(
  "moveLeft_possible",
  ``0 < index z ==> ?z'. moveLeft z = SOME z'``,
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> simp[moveLeft_def]);

val moveLeft_invariant = store_thm(
  "moveLeft_invariant",
  ``moveLeft z = SOME z' ==>
    toList z' = toList z /\ index z' = index z - 1 /\ size z' = size z``,
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> rw[moveLeft_def] >> simp[]);


val moveRight_possible = store_thm(
  "moveRight_possible",
  ``index z < size z - 1 ==> ?z'. moveRight z = SOME z'``,
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> simp[moveRight_def, index_def, size_def]);

val moveRight_invariant = store_thm(
  "moveRight_invariant",
  ``moveRight z = SOME z' ==>
    toList z' = toList z /\ index z' = index z + 1 /\ size z' = size z``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> rw[moveRight_def] >>
  asimp[toList_def, index_def, arithmeticTheory.ADD1, size_def])

val rptM_def = Define`
  (rptM 0 f = SOME) ∧
  (rptM (SUC n) f = \x. OPTION_BIND (f x) (rptM n f))
`;
val _ = export_rewrites ["rptM_def"]

val moveToI_def = Define`
  moveToI i z = if index z < i then rptM (i - index z) moveRight z
                else rptM (index z - i) moveLeft z
`;

val moveToI_correct = store_thm(
  "moveToI_correct",
  ``i < size z ==>
    ?z'. moveToI i z = SOME z' /\ index z' = i /\ toList z' = toList z``,
  simp[moveToI_def] >> strip_tac >> Cases_on `index z < i` >> simp[] >| [
    Induct_on `i - index z` >> asimp[] >> rpt strip_tac >>
    qmatch_assum_rename_tac `SUC n = i - index z` [] >>
    qpat_assum `SUC n = i - index z` (assume_tac o SYM) >>
    simp[rptM_def] >>
    `index z < size z - 1` by decide_tac >>
    `?z'. moveRight z = SOME z' /\ toList z' = toList z /\
          index z' = index z + 1 /\ size z' = size z`
      by metis_tac[moveRight_possible, moveRight_invariant] >>
    `index z' < size z'` by metis_tac [index_invariant] >>
    Cases_on `n = 0` >> simp[] >>
    first_x_assum (qspecl_then [`i`, `z'`] mp_tac) >> asimp[] >>
    `n = i - (index z + 1)` by decide_tac >> metis_tac[],

    Induct_on `index z - i` >> asimp[] >> rpt strip_tac
    >- (`index z - i = 0` by decide_tac >> simp[]) >>
    `0 < index z` by decide_tac >>
    `?z'. moveLeft z = SOME z' /\ toList z' = toList z /\
          size z' = size z /\ index z' = index z - 1`
      by metis_tac[moveLeft_possible, moveLeft_invariant] >>
    first_x_assum (qspecl_then [`z'`, `i`] mp_tac) >> asimp[] >>
    `?n. index z - i = SUC n` by metis_tac[] >> simp[] >>
    `index z - (i + 1) = n` by decide_tac >> metis_tac[]
  ]);

val zmap_def = Define`
  zmap f (Z p a s) = Z (MAP f p) (f a) (MAP f s)
`;
val _ = export_rewrites ["zmap_def"]

val size_zmap = store_thm(
  "size_zmap",
  ``size (zmap f z) = size z``,
  Cases_on `z` >> simp[]);
val _ = export_rewrites ["size_zmap"]

val index_zmap = store_thm(
  "index_zmap",
  ``index (zmap f z) = index z``,
  Cases_on `z` >> simp[])
val _ = export_rewrites ["index_zmap"]

open listTheory
val zmap_zmap_o = store_thm(
  "zmap_zmap_o",
  ``zmap f (zmap g z) = zmap (f o g) z``,
  Cases_on `z` >> simp[zmap_def, MAP_MAP_o]);

val zmap_ID = store_thm(
  "zmap_ID",
  ``zmap (λx. x) z = z``,
  Cases_on `z` >> simp[zmap_def]);

val MAP_toList = store_thm(
  "MAP_toList",
  ``MAP f (toList z) = toList (zmap f z)``,
  Cases_on `z` >> simp[zmap_def, rich_listTheory.MAP_REVERSE]);

val zpure_def = Define`zpure a = Z [] a []`
val fromList_def = Define`fromList (h::t) = Z [] h t`
val _ = export_rewrites ["fromList_def"]

val size_fromList = store_thm(
  "size_fromList",
  ``0 < LENGTH l ==> size (fromList l) = LENGTH l``,
  Cases_on `l` >> simp[]);

val toList_fromList = store_thm(
  "toList_fromList",
  ``0 < LENGTH l ==> toList (fromList l) = l``,
  Cases_on `l` >> simp[]);

val zipper_EQ = store_thm(
  "zipper_EQ",
  ``(z1 = z2) <=> toList z1 = toList z2 /\ index z1 = index z2``,
  Cases_on `z1` >> Cases_on`z2` >> simp[EQ_IMP_THM] >> strip_tac >>
  fs[APPEND_11_LENGTH]);

val moveToI0_fromList_toList = store_thm(
  "moveToI0_fromList_toList",
  ``moveToI 0 z = SOME (fromList (toList z))``,
  `0 < size z` by simp[] >>
  `?z'. moveToI 0 z = SOME z' /\ toList z' = toList z /\
        index z' = 0` by metis_tac [moveToI_correct] >>
  Cases_on `z` >> fs[] >>
  `?h t. z' = Z [] h t`
     by (Cases_on `z'` >> fs[] >> metis_tac[LENGTH_NIL]) >>
  fs[] >> qpat_assum `h::t = ZZ` (fn th => REWRITE_TAC [SYM th]) >>
  simp[]);

val zapply_def = Define`
  zapply fz xz = THE (moveToI (MAX (index fz) (index xz))
                              (fromList (toList fz <*> toList xz)))
`

val zmap_pure = store_thm(
  "zmap_pure",
  ``zapply (zpure f) z = zmap f z``,
  simp[zapply_def, zpure_def, toList_def,
       listTheory.LIST_APPLY_DEF, MAP_toList] >>
  qabbrev_tac `fz0 = fromList (toList (zmap f z))` >>
  `size fz0 = size z`
    by metis_tac[size_fromList, LENGTH_toList, size_zmap,
                 size_nonzero] >>
  `index z < size fz0` by simp[index_invariant] >>
  `toList fz0 = toList (zmap f z)`
    by metis_tac[toList_fromList, LENGTH_toList, size_nonzero] >>
  `?fz. moveToI (index z) fz0 = SOME fz /\ index fz = index z /\
        toList fz = toList fz0`
    by metis_tac[moveToI_correct] >>
  simp[] >> simp[zipper_EQ]);



val _ = export_theory();
