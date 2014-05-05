open HolKernel Parse boolLib bossLib;

open lcsymtacs
open listTheory

fun asimp thl = asm_simp_tac(srw_ss() ++ ARITH_ss) thl

val _ = new_theory "zipper";

val _ = ParseExtras.tight_equality()

val _ = Datatype `zipper = Z ('a list) 'a  ('a list)`

val focus_def = Define`focus (Z p a s) = a`
val toList_def = Define`toList (Z p a s) = REVERSE p ++ [a] ++ s`
val size_def = Define`size (Z p a s) = LENGTH p + LENGTH s + 1`
val index_def = Define`index (Z p a s) = LENGTH p`
val _ = export_rewrites ["focus_def", "toList_def", "size_def", "index_def"]

val index_invariant = store_thm(
  "index_invariant[simp]",
  ``index z < size z``,
  Cases_on `z` >> simp[]);

val size_nonzero = store_thm(
  "size_nonzero[simp]",
  ``0 < size z``,
  Cases_on `z` >> simp[]);

val LENGTH_toList = store_thm(
  "LENGTH_toList[simp]",
  ``LENGTH (toList z) = size z``,
  Cases_on `z` >> simp[]);

val moveLeft_def = Define`
  (moveLeft (Z [] a s) = Z [] a s) ∧
  (moveLeft (Z (h::t) a s) = Z t h (a::s))
`

val moveRight_def = Define`
  (moveRight (Z p a []) = Z p a []) ∧
  (moveRight (Z p a (h::t)) = Z (a::p) h t)
`;

val moveLeft_invariant = store_thm(
  "moveLeft_invariant[simp]",
  ``toList (moveLeft z) = toList z ∧ size (moveLeft z) = size z``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> rw[moveLeft_def] >> simp[]);

val moveLeft_index_lemma = prove(
  ``index (moveLeft z) = if 0 < index z then index z - 1 else 0``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> rw[moveLeft_def]);

val moveLeft_index = store_thm(
  "moveLeft_index",
  ``0 < index z ⇒ index (moveLeft z) = index z - 1``,
  simp[moveLeft_index_lemma]);

val moveLeft_possible = store_thm(
  "moveLeft_possible",
  ``0 < index z ==> moveLeft z <> z``,
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> simp[moveLeft_def]);

val moveRight_possible = store_thm(
  "moveRight_possible",
  ``index z < size z - 1 ==> moveRight z <> z``,
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> simp[moveRight_def, index_def, size_def]);

val moveRight_invariant = store_thm(
  "moveRight_invariant[simp]",
  ``toList (moveRight z) = toList z /\ size (moveRight z) = size z``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> rw[moveRight_def] >>
  simp[toList_def, index_def, arithmeticTheory.ADD1, size_def])

val moveRight_index_lemma = prove(
  ``index (moveRight z) = if index z < size z - 1 then index z + 1
                          else index z``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> simp[moveRight_def]);

val moveRight_index = store_thm(
  "moveRight_index",
  ``index z < size z - 1 ⇒ index (moveRight z) = index z + 1``,
  simp[moveRight_index_lemma]);

val moveToI_def = Define`
  moveToI i z = if index z < i then FUNPOW moveRight (i - index z) z
                else FUNPOW moveLeft (index z - i) z
`;

val moveToI_lemma = prove(
  ``size (moveToI i z) = size z ∧ toList (moveToI i z) = toList z ∧
    index (moveToI i z) = if i < size z then i else size z - 1``,
  simp[moveToI_def] >> `index z < size z` by simp[] >> COND_CASES_TAC >| [
    qabbrev_tac `m = i - index z` >>
    `i = m + index z ∧ 0 < m` by simp[Abbr`m`] >>
    markerLib.RM_ABBREV_TAC "m" >> BasicProvers.VAR_EQ_TAC >>
    pop_assum mp_tac >> pop_assum kall_tac >>
    Induct_on `m` >> simp[] >> rpt gen_tac >>
    simp[arithmeticTheory.FUNPOW_SUC] >>
    Cases_on `m = 0` >> simp[moveRight_index_lemma],

    qabbrev_tac `m = index z - i` >>
    `index z = m + i` by simp[Abbr`m`] >>
    markerLib.RM_ABBREV_TAC "m" >> pop_assum mp_tac >> pop_assum kall_tac >>
    qid_spec_tac `i` >>
    Induct_on `m` >> simp[arithmeticTheory.FUNPOW_SUC] >>
    gen_tac >> strip_tac >>
    first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >>
    simp[moveLeft_index_lemma]
  ])

val moveToI_invariant = save_thm(
  "moveToI_invariant[simp]",
  LIST_CONJ (List.take(CONJUNCTS moveToI_lemma, 2)));

val moveToI_index = store_thm(
  "moveToI_index",
  ``i < size z ⇒ index (moveToI i z) = i``,
  simp[moveToI_lemma]);

val moveToI_index_COND = save_thm(
  "moveToI_index_COND",
  List.last (CONJUNCTS moveToI_lemma))

val zipper_EQ = store_thm(
  "zipper_EQ",
  ``(z1 = z2) <=> toList z1 = toList z2 /\ index z1 = index z2``,
  Cases_on `z1` >> Cases_on`z2` >> simp[EQ_IMP_THM] >> strip_tac >>
  fs[APPEND_11_LENGTH]);

val moveToI_moveToI = store_thm(
  "moveToI_moveToI[simp]",
  ``moveToI i (moveToI j z) = moveToI i z``,
  simp[zipper_EQ, moveToI_index_COND]);

val zmap_def = Define`
  zmap f (Z p a s) = Z (MAP f p) (f a) (MAP f s)
`;
val _ = export_rewrites ["zmap_def"]

val size_zmap = store_thm(
  "size_zmap[simp]",
  ``size (zmap f z) = size z``,
  Cases_on `z` >> simp[]);

val index_zmap = store_thm(
  "index_zmap[simp]",
  ``index (zmap f z) = index z``,
  Cases_on `z` >> simp[])

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

val index_fromList = store_thm(
  "index_fromList",
  ``0 < LENGTH l ⇒ index (fromList l) = 0``,
  Cases_on `l` >> simp[]);

val toList_fromList = store_thm(
  "toList_fromList",
  ``0 < LENGTH l ==> toList (fromList l) = l``,
  Cases_on `l` >> simp[]);

val fromList_toList = store_thm(
  "fromList_toList[simp]",
  ``fromList (toList z) = moveToI 0 z``,
  simp[zipper_EQ] >> `0 < size z` by simp[] >>
  simp[toList_fromList, index_fromList, moveToI_index]);

val zapply_def = Define`
  zapply fz xz = moveToI (MAX (index fz) (index xz))
                         (fromList (toList fz <*> toList xz))
`
val _ = overload_on("APPLICATIVE_FAPPLY", ``zapply``)

val zmap_pure = store_thm(
  "zmap_pure",
  ``zpure f <*> z = zmap f z``,
  simp[zapply_def, zpure_def, listTheory.SINGL_APPLY_MAP, MAP_toList] >>
  simp[zipper_EQ, moveToI_index]);

val pure_pure_apply = store_thm(
  "pure_pure_apply",
  ``zpure f <*> zpure x = zpure (f x)``,
  simp[zmap_pure] >> simp[zmap_def, zpure_def]);

val pure_apply_permute = store_thm(
  "pure_apply_permute",
  ``fs <*> zpure x = zpure (λf. f x) <*> fs``,
  simp[zapply_def, zpure_def, SINGL_APPLY_PERMUTE]);

val LENGTH_LIST_APPLY = store_thm(
  "LENGTH_LIST_APPLY",
  ``LENGTH (fs <*> xs) = LENGTH fs * LENGTH xs``,
  simp[LIST_APPLY_DEF] >> Induct_on `fs` >> simp[] >>
  simp[arithmeticTheory.MULT_CLAUSES]);


val mult_lemma = prove(
  ``x < y ∧ 0 < v ⇒ x < y * v``,
  Induct_on `v` >> simp[arithmeticTheory.MULT_CLAUSES]);

val lemma = prove(
  ``MAX (index z1) (index z2) < size (fromList (toList z1 <*> toList z2))``,
  simp[size_fromList, LENGTH_LIST_APPLY, arithmeticTheory.ZERO_LESS_MULT] >>
  metis_tac [index_invariant, size_nonzero, mult_lemma,
             arithmeticTheory.MULT_COMM]);

val lemma' = prove(
  ``MAX (index z1) (index z2) <
    size (fromList (toList (zmap f z1) <*> toList z2))``,
  simp[size_fromList, LENGTH_LIST_APPLY, arithmeticTheory.ZERO_LESS_MULT] >>
  metis_tac [index_invariant, size_nonzero, mult_lemma,
             arithmeticTheory.MULT_COMM]);

val apply_pure_o = store_thm(
  "apply_pure_o",
  ``zpure (o) <*> fs <*> gs <*> xs = fs <*> (gs <*> xs)``,
  simp[zmap_pure] >>
  simp[zapply_def, moveToI_index, lemma, size_fromList, toList_fromList,
       LENGTH_LIST_APPLY, arithmeticTheory.ZERO_LESS_MULT, lemma'] >>
  simp[GSYM LIST_APPLY_o, SINGL_APPLY_MAP, MAP_toList,
       arithmeticTheory.MAX_ASSOC]);

val _ = export_theory();
