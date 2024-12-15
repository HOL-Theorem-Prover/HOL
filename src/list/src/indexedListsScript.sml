open HolKernel Parse boolLib BasicProvers;

(* bossLib approximation *)
open TotalDefn simpLib numLib IndDefLib listTheory rich_listTheory;

fun simp thl = ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) thl
fun dsimp thl =
  ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss ++ boolSimps.DNF_ss) thl
fun csimp thl =
  ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss ++ boolSimps.CONJ_ss) thl
fun kall_tac th = K ALL_TAC th
val metis_tac = metisLib.METIS_TAC
val qid_spec_tac = Q.ID_SPEC_TAC
fun rw thl = SRW_TAC[] thl
fun fs thl = full_simp_tac (srw_ss() ++ numSimps.ARITH_ss) thl;
val rename1 = Q.RENAME1_TAC
val qspec_then = Q.SPEC_THEN
val zDefine = Lib.with_flag (computeLib.auto_import_definitions,false) Define

val _ = new_theory "indexedLists";

Definition MAPi_def[simp,nocompute]:
  (MAPi f [] = []) /\
  (MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t)
End

Definition MAPi_ACC_def:
  (MAPi_ACC f i a [] = REVERSE a) /\
  (MAPi_ACC f i a (h::t) = MAPi_ACC f (i + 1) (f i h :: a) t)
End

val MAPi_ACC_MAPi = store_thm(
  "MAPi_ACC_MAPi",
  ``MAPi_ACC f n a l = REVERSE a ++ MAPi (f o (+) n) l``,
  MAP_EVERY Q.ID_SPEC_TAC [`f`, `n`, `a`] >> Induct_on `l` >>
  simp[MAPi_ACC_def] >> REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >>
  REPEAT GEN_TAC >> REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]);

Theorem MAPi_compute[compute]:
  MAPi f l = MAPi_ACC f 0 [] l
Proof
  simp[MAPi_ACC_MAPi] >> REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]
QED

val LT_SUC = arithmeticTheory.LT_SUC

val MEM_MAPi = store_thm(
  "MEM_MAPi",
  ``!x f l. MEM x (MAPi f l) <=>
            ?n. n < LENGTH l /\ x = f n (EL n l)``,
  Induct_on `l` >> simp[] >> pop_assum kall_tac >>
  dsimp[EQ_IMP_THM, LT_SUC] >> metis_tac[]);

val MAPi_CONG = store_thm(
  "MAPi_CONG[defncong]",
  ``!l1 l2 f1 f2.
      l1 = l2 /\ (!x n. MEM x l2 ==> f1 n x = f2 n x) ==>
      MAPi f1 l1 = MAPi f2 l2``,
  Induct_on `l1` >> dsimp[LT_SUC]);

val MAPi_CONG' = store_thm(
  "MAPi_CONG'",
  ``l1 = l2 ==> (!x n. (x = EL n l2) ==> n < LENGTH l2 ==> f1 n x = f2 n x) ==>
    MAPi f1 l1 = MAPi f2 l2``,
  map_every qid_spec_tac [`f1`, `f2`, `l2`] >> Induct_on `l1` >>
  dsimp[LT_SUC]);

val LENGTH_MAPi = store_thm(
  "LENGTH_MAPi[simp]",
  ``!f l. LENGTH (MAPi f l) = LENGTH l``,
  Induct_on `l` >> simp[]);

val MAP_MAPi = store_thm(
  "MAP_MAPi[simp]",
  ``!f g l. MAP f (MAPi g l) = MAPi ((o) f o g) l``,
  Induct_on `l` >> simp[]);

val EL_MAPi = store_thm(
  "EL_MAPi[simp]",
  ``!f n l. n < LENGTH l ==> EL n (MAPi f l) = f n (EL n l)``,
  Induct_on `l` >> simp[] >> dsimp[LT_SUC]);

val MAPi_APPEND = store_thm(
  "MAPi_APPEND",
  ``!l1 l2 f. MAPi f (l1 ++ l2) = MAPi f l1 ++ MAPi (f o (+) (LENGTH l1)) l2``,
  Induct >> simp[] >> rpt gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]);

val MAPi_GENLIST = store_thm(
  "MAPi_GENLIST",
  ``!l f. MAPi f l = GENLIST (S f (combin$C EL l)) (LENGTH l)``,
  Induct >> simp[GENLIST_CONS] >> rpt gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[FUN_EQ_THM]);

Theorem MAPi_EQ_MAP[simp]:
  !l. MAPi (\i x. f x) l = MAP f l
Proof
  Induct >> simp[combinTheory.o_DEF]
QED

Definition FOLDRi_def[simp]:
  (FOLDRi f a [] = a) /\
  (FOLDRi f a (h::t) = f 0 h (FOLDRi (f o SUC) a t))
End

val FOLDR_MAPi = store_thm(
  "FOLDR_MAPi",
  ``!f g a l. FOLDR f a (MAPi g l) = FOLDRi ($o f o g) a l``,
  Induct_on `l` >> simp[MAPi_def]);

val FOLDRi_APPEND = store_thm(
  "FOLDRi_APPEND",
  ``!f.
     FOLDRi f a (l1 ++ l2) = FOLDRi f (FOLDRi (f o $+ (LENGTH l1)) a l2) l1``,
  Induct_on `l1` >> simp[]
  >- (gen_tac >> `f o $+ 0 = f` suffices_by simp[] >> simp[FUN_EQ_THM]) >>
  rpt gen_tac >>
  `f o SUC o $+ (LENGTH l1) = f o $+ (SUC (LENGTH l1))` suffices_by simp[] >>
  simp[FUN_EQ_THM, arithmeticTheory.ADD_CLAUSES]);

val FOLDRi_CONG = store_thm(
  "FOLDRi_CONG",
  ``l1 = l2 ==>
    (!n e a. n < LENGTH l2 ==> MEM e l2 ==> f1 n e a = f2 n e a) ==>
    a1 = a2 ==>
    FOLDRi f1 a1 l1 = FOLDRi f2 a2 l2``,
  disch_then SUBST_ALL_TAC >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`f1`, `f2`] >>
  Induct_on `l2` >> simp[] >> dsimp[LT_SUC] >> rpt strip_tac >>
  AP_TERM_TAC >> first_x_assum match_mp_tac >> simp[]);

val FOLDRi_CONG' = store_thm(
  "FOLDRi_CONG'",
  ``l1 = l2 /\ (!n a. n < LENGTH l2 ==> f1 n (EL n l2) a = f2 n (EL n l2) a) /\
    a1 = a2 ==>
    FOLDRi f1 a1 l1 = FOLDRi f2 a2 l2``,
  strip_tac >> rw[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`f1`, `f2`] >> Induct_on `l1` >>
  dsimp[LT_SUC] >> rpt strip_tac >> AP_TERM_TAC >>
  first_x_assum match_mp_tac >> simp[]);

val findi_def = Define`
  findi x [] = 0 /\
  findi x (h::t) = if x = h then 0 else 1 + findi x t
`;

Theorem findi_nil = findi_def |> CONJUNCT1;
(* val findi_nil = |- !x. findi x [] = 0: thm *)

Theorem findi_cons = findi_def |> CONJUNCT2;
(* val findi_cons = |- !x h t. findi x (h::t) = if x = h then 0 else 1 + findi x t: thm *)

(* Theorem: ~MEM x ls ==> findi x ls = LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: ~MEM x [] ==> findi x [] = LENGTH []
         findi x []
       = 0                         by findi_nil
       = LENGTH []                 by LENGTH
   Step:  ~MEM x ls ==> findi x ls = LENGTH ls ==>
         !h. ~MEM x (h::ls) ==> findi x (h::ls) = LENGTH (h::ls)
       Note ~MEM x (h::ls)
        ==> x <> h /\ ~MEM x ls    by MEM
       Thus findi x (h::ls)
          = 1 + findi x ls         by findi_cons
          = 1 + LENGTH ls          by induction hypothesis
          = SUC (LENGTH ls)        by ADD1
          = LENGTH (h::ls)         by LENGTH
*)
Theorem findi_none:
  !ls x. ~MEM x ls ==> findi x ls = LENGTH ls
Proof
  rpt strip_tac >>
  Induct_on `ls` >-
  simp[findi_nil] >>
  simp[findi_cons]
QED

val MEM_findi = store_thm(
  "MEM_findi",
  ``MEM x l ==> findi x l < LENGTH l``,
  Induct_on `l` >> simp[findi_def] >>
  rw[arithmeticTheory.ADD1, arithmeticTheory.ZERO_LESS_ADD]);

val findi_EL = store_thm(
  "findi_EL",
  ``!l n. n < LENGTH l /\ ALL_DISTINCT l ==> findi (EL n l) l = n``,
  Induct >> simp[] >> map_every Q.X_GEN_TAC [`h`, `n`] >> strip_tac >>
  Cases_on `n` >> simp[findi_def] >> rw[arithmeticTheory.ADD1] >>
  fs[] >> metis_tac[MEM_EL]);

val EL_findi = store_thm(
  "EL_findi",
  ``!l x. MEM x l ==> EL (findi x l) l = x``,
  Induct_on`l` >> rw[findi_def] >> simp[DECIDE ``1 + x = SUC x``]);

(* Theorem: ALL_DISTINCT ls /\ MEM x ls /\ n < LENGTH ls ==> (x = EL n ls <=> findi x ls = n) *)
(* Proof:
   If part: x = EL n ls ==> findi x ls = n
      Given ALL_DISTINCT ls /\ n < LENGTH ls
      This is true             by findi_EL
   Only-if part: findi x ls = n ==> x = EL n ls
      Given MEM x ls
      This is true             by EL_findi
*)
Theorem findi_EL_iff:
  !ls x n. ALL_DISTINCT ls /\ MEM x ls /\ n < LENGTH ls ==> (x = EL n ls <=> findi x ls = n)
Proof
  metis_tac[findi_EL, EL_findi]
QED

(* Theorem: findi x (l1 ++ l2) = if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2 *)
(* Proof:
   By induction on l1.
   Base: findi x ([] ++ l2) = if MEM x [] then findi x [] else LENGTH [] + findi x l2
      Note MEM x [] = F            by MEM
        so findi x ([] ++ l2)
         = findi x l2              by APPEND
         = 0 + findi x l2          by ADD
         = LENGTH [] + findi x l2  by LENGTH
   Step: findi x (l1 ++ l2) = if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2 ==>
         !h. findi x (h::l1 ++ l2) = if MEM x (h::l1) then findi x (h::l1)
                                     else LENGTH (h::l1) + findi x l2

      Note findi x (h::l1 ++ l2)
         = if x = h then 0 else 1 + findi x (l1 ++ l2)     by findi_cons

      Case: MEM x (h::l1).
      To show: findi x (h::l1 ++ l2) = findi x (h::l1).
      Note MEM x (h::l1)
       <=> x = h \/ MEM x l1       by MEM
      If x = h,
           findi x (h::l1 ++ l2)
         = 0 = findi x (h::l1)     by findi_cons
      If x <> h, then MEM x l1.
           findi x (h::l1 ++ l2)
         = 1 + findi x (l1 ++ l2)  by x <> h
         = 1 + findi x l1          by induction hypothesis
         = findi x (h::l1)         by findi_cons

      Case: ~MEM x (h::l1).
      To show: findi x (h::l1 ++ l2) = LENGTH (h::l1) + findi x l2.
      Note ~MEM x (h::l1)
       <=> x <> h /\ ~MEM x l1     by MEM
           findi x (h::l1 ++ l2)
         = 1 + findi x (l1 ++ l2)  by x <> h
         = 1 + (LENGTH l1 + findi x l2)        by induction hypothesis
         = (1 + LENGTH l1) + findi x l2        by arithmetic
         = LENGTH (h::l1) + findi x l2         by LENGTH
*)
Theorem findi_APPEND:
  !l1 l2 x. findi x (l1 ++ l2) = if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2
Proof
  rpt strip_tac >>
  Induct_on `l1` >-
  simp[] >>
  (rw[findi_cons] >> fs[])
QED

val delN_def = Define`
  delN i [] = [] /\
  delN i (h::t) = if i = 0 then t
                  else h::delN (i - 1) t
`;

val delN_shortens = store_thm(
  "delN_shortens",
  ``!l i. i < LENGTH l ==> LENGTH (delN i l) = LENGTH l - 1``,
  Induct >> dsimp[delN_def, LT_SUC]);

val EL_delN_BEFORE = store_thm(
  "EL_delN_BEFORE",
  ``!l i j. i < j /\ j < LENGTH l ==> EL i (delN j l) = EL i l``,
  Induct >> simp[delN_def] >> map_every Q.X_GEN_TAC [`h`, `i`, `j`] >>
  Cases_on `i` >> simp[])

val EL_delN_AFTER = store_thm(
  "EL_delN_AFTER",
  ``!l i j. j <= i /\ i + 1 < LENGTH l ==> (EL i (delN j l) = EL (i + 1) l)``,
  Induct >> simp[delN_def] >> rw[]
  >- simp[GSYM arithmeticTheory.ADD1] >>
  `?i0. i = SUC i0` by (Cases_on `i` >> fs[]) >> rw[] >>
  fs[arithmeticTheory.ADD_CLAUSES] >> simp[]);

val fupdLast_def = Define`
  (fupdLast f [] = []) /\
  (fupdLast f [h] = [f h]) /\
  (fupdLast f (h::t) = h::fupdLast f t)
`;
val _ = export_rewrites ["fupdLast_def"]

val fupdLast_EQ_NIL = store_thm(
  "fupdLast_EQ_NIL[simp]",
  ``(fupdLast f x = [] <=> x = []) /\
    ([] = fupdLast f x <=> x = [])``,
  Cases_on `x` >> simp[] >> Cases_on `t` >> simp[]);

val fupdLast_FRONT_LAST = store_thm(
  "fupdLast_FRONT_LAST",
  ``fupdLast f l = if l = [] then []
                  else FRONT l ++ [f (LAST l)]``,
  Induct_on `l` >> simp[] >> Cases_on `l` >> simp[]);

(* ----------------------------------------------------------------------
    LIST_RELi
   ---------------------------------------------------------------------- *)

val (LIST_RELi_rules, LIST_RELi_ind, LIST_RELi_cases) = Hol_reln`
  LIST_RELi R [] [] /\
  !h1 h2 l1 l2.
     R (LENGTH l1) h1 h2 /\ LIST_RELi R l1 l2 ==>
     LIST_RELi R (l1 ++ [h1]) (l2 ++ [h2])
`;

val LIST_RELi_LENGTH = Q.store_thm(
  "LIST_RELi_LENGTH",
  `!l1 l2. LIST_RELi R l1 l2 ==> LENGTH l1 = LENGTH l2`,
  Induct_on `LIST_RELi` >> simp[]);

val LIST_RELi_EL_EQN = Q.store_thm(
  "LIST_RELi_EL_EQN",
  `LIST_RELi R l1 l2 <=>
    LENGTH l1 = LENGTH l2 /\ !i. i < LENGTH l1 ==> R i (EL i l1) (EL i l2)`,
  eq_tac >> map_every qid_spec_tac [`l2`, `l1`]
  >- (Induct_on `LIST_RELi` >> csimp[] >> rpt strip_tac >>
      rename1 `i < LENGTH l2 + 1` >>
      `i < LENGTH l2 \/ i = LENGTH l2` by simp[] >- simp[EL_APPEND1] >>
      simp[EL_APPEND2]) >>
  ho_match_mp_tac SNOC_INDUCT >>
  simp[SNOC_APPEND, LENGTH_NIL_SYM, LIST_RELi_rules] >> rpt strip_tac >>
  Q.ISPEC_THEN `l2` FULL_STRUCT_CASES_TAC SNOC_CASES >> fs[SNOC_APPEND] >>
  irule (CONJUNCT2 (SPEC_ALL LIST_RELi_rules)) >> conj_tac
  >- (rename1 `R (LENGTH l1) x y` >>
      first_x_assum (qspec_then `LENGTH l1` mp_tac) >> simp[EL_APPEND2]) >>
  reverse (first_x_assum irule >> conj_tac) >- simp[] >> Q.X_GEN_TAC `j` >>
  strip_tac >> first_x_assum (qspec_then `j` mp_tac) >> simp[EL_APPEND1]);

val LIST_RELi_thm = Q.store_thm(
  "LIST_RELi_thm",
  `(LIST_RELi R [] x <=> (x = [])) /\
   (LIST_RELi R (h::t) l <=>
     ?h' t'. l = h'::t' /\ R 0 h h' /\ LIST_RELi (R o SUC) t t')`,
  simp[LIST_RELi_EL_EQN, LENGTH_NIL_SYM] >> eq_tac >> strip_tac
  >- (rename1 `l = _ :: _` >> Cases_on `l` >> fs[] >>
      fs[LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]) >>
  var_eq_tac >> dsimp[LT_SUC]);

val LIST_RELi_APPEND_I = Q.store_thm(
  "LIST_RELi_APPEND_I",
  ‘LIST_RELi R l1 l2 /\ LIST_RELi (R o ((+) (LENGTH l1))) m1 m2 ==>
   LIST_RELi R (l1 ++ m1) (l2 ++ m2)’,
  simp[LIST_RELi_EL_EQN] >> rpt strip_tac >>
  rename1 `i < LENGTH l2 + LENGTH m2` >> Cases_on `i < LENGTH l2`
  >- simp[EL_APPEND1]
  >- (simp[EL_APPEND2] >> first_x_assum (qspec_then `i - LENGTH l2` mp_tac) >>
      simp[]));

(* ----------------------------------------------------------------------
    MAP2i
   ---------------------------------------------------------------------- *)

val MAP2i_def = zDefine‘
  (MAP2i f [] _ = []) /\
  (MAP2i f _ [] = []) /\
  (MAP2i f (h1::t1) (h2::t2) = f 0 h1 h2::MAP2i (f o SUC) t1 t2)’;
val _ = export_rewrites["MAP2i_def"];

(* Define doesn't generate this case, though the second pattern looks as if
   it should *)
val MAP2i_NIL2 = Q.store_thm(
  "MAP2i_NIL2[simp]",
  ‘MAP2i f l1 [] = []’,
  Cases_on ‘l1’ >> simp[]);

val MAP2i_ind = theorem"MAP2i_ind";

val LENGTH_MAP2i = Q.store_thm(
  "LENGTH_MAP2i[simp]",
  ‘!f l1 l2. LENGTH (MAP2i f l1 l2) = MIN (LENGTH l1) (LENGTH l2)’,
  ho_match_mp_tac MAP2i_ind >> rw[arithmeticTheory.MIN_DEF]);

val EL_MAP2i = Q.store_thm("EL_MAP2i",
  ‘!f l1 l2 n.
      n < LENGTH l1 /\ n < LENGTH l2 ==>
      (EL n (MAP2i f l1 l2) = f n (EL n l1) (EL n l2))’,
  HO_MATCH_MP_TAC MAP2i_ind >> rw[] >> Cases_on‘n’ >> fs[]);

val MAP2ia_def = Define‘
  (MAP2ia f i [] _ = []) /\
  (MAP2ia f i _ [] = []) /\
  (MAP2ia f i (h1::t1) (h2::t2) = f i h1 h2 :: MAP2ia f (i + 1) t1 t2)
’;
val _= export_rewrites ["MAP2ia_def"]

val MAP2ia_NIL2 = Q.store_thm(
  "MAP2ia_NIL2[simp]",
  ‘MAP2ia f i l1 [] = []’,
  Cases_on ‘l1’ >> simp[]);

val MAP2i_compute = Q.store_thm(
  "MAP2i_compute",
  ‘MAP2i f l1 l2 = MAP2ia (f:num -> 'a -> 'b -> 'c) 0 l1 l2’,
  ‘!l1 l2 n f: num -> 'a -> 'b -> 'c.
     MAP2ia f n l1 l2 = MAP2i (f o (+) n) l1 l2’
    suffices_by
      (simp[] >> strip_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
       simp[FUN_EQ_THM]) >>
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[] >>
  rpt gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]);
val _ = computeLib.add_persistent_funs ["MAP2i_compute"]
val _ = remove_ovl_mapping "MAP2ia" {Name = "MAP2ia", Thy = "indexedLists"}

val _ = export_theory();
