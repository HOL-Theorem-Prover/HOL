Theory zipper
Ancestors
  list

(* a simple theory of zippers: lists coupled with a privileged index *)

(* final theorem is that there is an appropriate notion of application such
   that they form an applicative functor; given that lists already do this
   the "trick" is figuring out what the index of the result zipper should
   be when you apply a zipper of functions to a zipper of arguments.  *)

Datatype: zipper = Z ('a list) 'a  ('a list)
End

Definition focus_def[simp]: focus (Z p a s) = a
End

Definition toList_def[simp]: toList (Z p a s) = REVERSE p ++ [a] ++ s
End

Definition size_def[simp]: size (Z p a s) = LENGTH p + LENGTH s + 1
End

Definition index_def[simp]: index (Z p a s) = LENGTH p
End

Theorem index_invariant[simp]:
  index z < size z
Proof
  Cases_on `z` >> simp[]
QED

Theorem size_nonzero[simp]:
  0 < size z
Proof
  Cases_on `z` >> simp[]
QED

Theorem LENGTH_toList[simp]:
  LENGTH (toList z) = size z
Proof
  Cases_on `z` >> simp[]
QED

Definition moveLeft_def:
  (moveLeft (Z [] a s) = Z [] a s) ∧
  (moveLeft (Z (h::t) a s) = Z t h (a::s))
End

Definition moveRight_def:
  (moveRight (Z p a []) = Z p a []) ∧
  (moveRight (Z p a (h::t)) = Z (a::p) h t)
End

Theorem moveLeft_invariant[simp]:
  toList (moveLeft z) = toList z ∧ size (moveLeft z) = size z
Proof
  ‘∃p a s. z = Z p a s’ by (Cases_on ‘z’ >> simp[]) >>
  Cases_on `p` >> rw[moveLeft_def] >> simp[]
QED

val moveLeft_index_lemma = prove(
  ``index (moveLeft z) = if 0 < index z then index z - 1 else 0``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> rw[moveLeft_def]);

Theorem moveLeft_index:
    0 < index z ⇒ index (moveLeft z) = index z - 1
Proof
  simp[moveLeft_index_lemma]
QED

Theorem moveLeft_possible:
    0 < index z ==> moveLeft z <> z
Proof
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `p` >> simp[moveLeft_def]
QED

Theorem moveRight_possible:
    index z < size z - 1 ==> moveRight z <> z
Proof
  `?p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> simp[moveRight_def, index_def, size_def]
QED

Theorem moveRight_invariant[simp]:
    toList (moveRight z) = toList z /\ size (moveRight z) = size z
Proof
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> rw[moveRight_def] >>
  simp[toList_def, index_def, arithmeticTheory.ADD1, size_def]
QED

val moveRight_index_lemma = prove(
  ``index (moveRight z) = if index z < size z - 1 then index z + 1
                          else index z``,
  `∃p a s. z = Z p a s` by (Cases_on `z` >> simp[]) >>
  Cases_on `s` >> simp[moveRight_def]);

Theorem moveRight_index:
    index z < size z - 1 ⇒ index (moveRight z) = index z + 1
Proof
  simp[moveRight_index_lemma]
QED

Definition moveToI_def:
  moveToI i z = if index z < i then FUNPOW moveRight (i - index z) z
                else FUNPOW moveLeft (index z - i) z
End

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

Theorem moveToI_index:
    i < size z ⇒ index (moveToI i z) = i
Proof
  simp[moveToI_lemma]
QED

val moveToI_index_COND = save_thm(
  "moveToI_index_COND",
  List.last (CONJUNCTS moveToI_lemma))

Theorem zipper_EQ:
    (z1 = z2) <=> toList z1 = toList z2 /\ index z1 = index z2
Proof
  Cases_on `z1` >> Cases_on`z2` >> simp[EQ_IMP_THM] >> strip_tac >>
  fs[APPEND_11_LENGTH]
QED

Theorem moveToI_moveToI[simp]:
    moveToI i (moveToI j z) = moveToI i z
Proof
  simp[zipper_EQ, moveToI_index_COND]
QED

Definition zmap_def[simp]:
  zmap f (Z p a s) = Z (MAP f p) (f a) (MAP f s)
End

Theorem size_zmap[simp]:
  size (zmap f z) = size z
Proof
  Cases_on `z` >> simp[]
QED

Theorem index_zmap[simp]:
  index (zmap f z) = index z
Proof
  Cases_on `z` >> simp[]
QED

Theorem zmap_zmap_o:
  zmap f (zmap g z) = zmap (f o g) z
Proof
  Cases_on `z` >> simp[zmap_def, MAP_MAP_o]
QED

Theorem zmap_ID:
  zmap (λx. x) z = z
Proof
  Cases_on `z` >> simp[zmap_def]
QED

Theorem MAP_toList:
    MAP f (toList z) = toList (zmap f z)
Proof
  Cases_on `z` >> simp[zmap_def, rich_listTheory.MAP_REVERSE]
QED

Definition zpure_def:  zpure a = Z [] a []
End
Definition fromList_def:  fromList (h::t) = Z [] h t
End
val _ = export_rewrites ["fromList_def"]

Theorem size_fromList:
    0 < LENGTH l ==> size (fromList l) = LENGTH l
Proof
  Cases_on `l` >> simp[]
QED

Theorem index_fromList:
    0 < LENGTH l ⇒ index (fromList l) = 0
Proof
  Cases_on `l` >> simp[]
QED

Theorem toList_fromList:
    0 < LENGTH l ==> toList (fromList l) = l
Proof
  Cases_on `l` >> simp[]
QED

Theorem fromList_toList[simp]:
    fromList (toList z) = moveToI 0 z
Proof
  simp[zipper_EQ] >> `0 < size z` by simp[] >>
  simp[toList_fromList, index_fromList, moveToI_index]
QED

Definition zapply_def:
  zapply fz xz = moveToI (MAX (index fz) (index xz))
                         (fromList (toList fz <*> toList xz))
End
val _ = overload_on("APPLICATIVE_FAPPLY", ``zapply``)

Theorem zmap_pure:
    zpure f <*> z = zmap f z
Proof
  simp[zapply_def, zpure_def, listTheory.SINGL_APPLY_MAP, MAP_toList] >>
  simp[zipper_EQ, moveToI_index]
QED

Theorem pure_pure_apply:
    zpure f <*> zpure x = zpure (f x)
Proof
  simp[zmap_pure] >> simp[zmap_def, zpure_def]
QED

Theorem pure_apply_permute:
    fs <*> zpure x = zpure (λf. f x) <*> fs
Proof
  simp[zapply_def, zpure_def, SINGL_APPLY_PERMUTE]
QED

Theorem LENGTH_LIST_APPLY:
    LENGTH (fs <*> xs) = LENGTH fs * LENGTH xs
Proof
  simp[LIST_APPLY_def] >> Induct_on `fs` >> simp[] >>
  simp[arithmeticTheory.MULT_CLAUSES]
QED


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

Theorem apply_pure_o:
    zpure (o) <*> fs <*> gs <*> xs = fs <*> (gs <*> xs)
Proof
  simp[zmap_pure] >>
  simp[zapply_def, moveToI_index, lemma, size_fromList, toList_fromList,
       LENGTH_LIST_APPLY, arithmeticTheory.ZERO_LESS_MULT, lemma'] >>
  simp[GSYM LIST_APPLY_o, SINGL_APPLY_MAP, MAP_toList,
       arithmeticTheory.MAX_ASSOC]
QED

