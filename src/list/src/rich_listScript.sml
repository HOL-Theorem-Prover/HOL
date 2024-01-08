open HolKernel Parse BasicProvers boolLib numLib metisLib simpLib
open combinTheory arithmeticTheory prim_recTheory pred_setTheory
local open listTheory listSimps pred_setSimps TotalDefn in end

open listTheory
val FILTER_APPEND = FILTER_APPEND_DISTRIB
val REVERSE = REVERSE_SNOC_DEF

open markerLib

val () = new_theory "rich_list"

(* ------------------------------------------------------------------------ *)

val list_ss = arith_ss ++ listSimps.LIST_ss ++ pred_setSimps.PRED_SET_ss
val metis_tac = METIS_TAC
val rw = SRW_TAC[numSimps.ARITH_ss]
fun simp thl = ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) thl
fun fs thl = FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) thl

val DEF0 = Lib.with_flag (boolLib.def_suffix, "") TotalDefn.Define
val DEF = Lib.with_flag (boolLib.def_suffix, "_DEF") TotalDefn.Define

val zDefine =
   Lib.with_flag (computeLib.auto_import_definitions, false) TotalDefn.Define

val list_INDUCT = Q.prove(
   `!P. P [] /\ (!l. P l ==> !x. P (CONS x l)) ==> !l. P l`,
   REWRITE_TAC [list_INDUCT]);

val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;
val SNOC_INDUCT_TAC = Prim_rec.INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

(* ------------------------------------------------------------------------ *)

val ELL = DEF0`
   (ELL 0 l = LAST l) /\
   (ELL (SUC n) l = ELL n (FRONT l))`;

Definition REPLICATE[simp]:
   (REPLICATE 0 x = []) /\
   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))
End

val SCANL = DEF0`
   (SCANL f (e: 'b) [] = [e]) /\
   (SCANL f e (CONS x l) = CONS e (SCANL f (f e x) l))`;

val SCANR = DEF0`
   (SCANR f (e: 'b) [] = [e]) /\
   (SCANR f e (CONS x l) = CONS (f x (HD (SCANR f e l))) (SCANR f e l))`;

val SPLITP = Lib.with_flag (computeLib.auto_import_definitions, false) DEF0`
   (SPLITP P [] = ([],[])) /\
   (SPLITP P (CONS x l) =
      if P x then
         ([], CONS x l)
      else
         (CONS x (FST (SPLITP P l)), SND (SPLITP P l)))`;

val SPLITP_AUX_def = TotalDefn.Define`
   (SPLITP_AUX acc P [] = (acc,[])) /\
   (SPLITP_AUX acc P (h::t) =
      if P h then (acc, h::t) else SPLITP_AUX (acc ++ [h]) P t)`;

Theorem SPLITP_splitAtPki:
  SPLITP P = splitAtPki (K P) $,
Proof
  simp[FUN_EQ_THM] >> Induct >> simp[SPLITP,splitAtPki_def] >>
  rw[o_DEF] >> Q.HO_MATCH_ABBREV_TAC`f (splitAtPki (K P) $, x) = _` >>
  CONV_TAC(LAND_CONV(REWRITE_CONV[splitAtPki_RAND])) >>
  simp[Abbr‘f’, o_DEF]
QED

Theorem SPLITP_JOIN:
  !ls l r.
    (SPLITP P ls = (l, r)) ==> (ls = l ++ r)
Proof
  Induct >> rw[SPLITP] >> Cases_on `SPLITP P ls` >> rw[]
QED

Theorem SPLITP_IMP:
  !P ls l r.
     (SPLITP P ls = (l,r)) ==>
     EVERY ($~ o P) l /\ (~NULL r ==> P (HD r))
Proof
  Induct_on`ls` >> rw[SPLITP] >> rw[] >> fs[] >>
  Cases_on`SPLITP P ls` >> fs[]
QED

Theorem SPLITP_LENGTH:
  !l. LENGTH (FST (SPLITP P l)) + LENGTH (SND (SPLITP P l))
      = LENGTH l
Proof Induct \\ rw[SPLITP, LENGTH]
QED

Theorem SPLITP_APPEND:
  !l1 l2.
    SPLITP P (l1 ++ l2) =
     if EXISTS P l1 then
       (FST (SPLITP P l1), SND (SPLITP P l1) ++ l2)
     else
       (l1 ++ FST(SPLITP P l2), SND (SPLITP P l2))
Proof
  Induct \\ rw[SPLITP] \\ fs[]
QED

Theorem SPLITP_NIL_SND_EVERY:
  !ls r. (SPLITP P ls = (r, [])) <=> (r = ls) /\ (EVERY ($~ o P) ls)
Proof
  rw[] >> EQ_TAC
  >- (rw[] >> imp_res_tac SPLITP_IMP >> imp_res_tac SPLITP_JOIN >> fs[]) >>
  rw[] >> Induct_on `ls` >> rw[SPLITP]
QED

Theorem SPLITP_NIL_FST_IMP:
  !ls r. (SPLITP P ls = ([],r)) ==> (r = ls)
Proof Induct \\ rw[SPLITP]
QED

val SPLITL_def = TotalDefn.Define `SPLITL P = SPLITP ((~) o P)`;

val SPLITR_def = TotalDefn.Define`
   SPLITR P l =
   let (a, b) = SPLITP ((~) o P) (REVERSE l) in (REVERSE b, REVERSE a)`;

val PREFIX_DEF = DEF `PREFIX P l = FST (SPLITP ($~ o P) l)`;

val SUFFIX_DEF = DEF`
   SUFFIX P l = FOLDL (\l' x. if P x then SNOC x l' else []) [] l`;

val AND_EL_DEF = DEF `AND_EL = EVERY I`;
val OR_EL_DEF = DEF `OR_EL = EXISTS I`;

val UNZIP_FST_DEF = DEF `UNZIP_FST l = FST (UNZIP l)`;
val UNZIP_SND_DEF = DEF `UNZIP_SND l = SND (UNZIP l)`;

val LIST_ELEM_COUNT_DEF = DEF`
   LIST_ELEM_COUNT e l = LENGTH (FILTER (\x. x = e) l)`;

val COUNT_LIST_def = zDefine`
   (COUNT_LIST 0 = []) /\
   (COUNT_LIST (SUC n) = 0::MAP SUC (COUNT_LIST n))`;

val COUNT_LIST_AUX_def = TotalDefn.Define`
   (COUNT_LIST_AUX 0 l = l) /\
   (COUNT_LIST_AUX (SUC n) l = COUNT_LIST_AUX n (n::l))`;

(* total version of TL *)
val TL_T_def = TotalDefn.Define`
   (TL_T [] = []) /\
   (TL_T (h::t) = t)`;

(* ------------------------------------------------------------------------ *)

val TAKE = Q.store_thm("TAKE",
   `(!l:'a list. TAKE 0 l = []) /\
    (!n x l:'a list. TAKE (SUC n) (CONS x l) = CONS x (TAKE n l))`,
   SRW_TAC [] []);

val DROP = Q.store_thm("DROP",
   `(!l:'a list. DROP 0 l = l) /\
    (!n x l:'a list. DROP (SUC n) (CONS x l) = DROP n l)`,
  SRW_TAC [] []);

val tlt_lem = Q.prove (
  `FUNPOW TL_T n [] = []`,
  Induct_on `n` THEN ASM_SIMP_TAC list_ss [FUNPOW, TL_T_def]) ;

val DROP_FUNPOW_TL = Q.store_thm("DROP_FUNPOW_TL",
  `(!n l. DROP n l = FUNPOW TL_T n l)`,
  Induct THEN1 SIMP_TAC list_ss [DROP, FUNPOW]
  THEN Cases_on `l` THEN1 SIMP_TAC list_ss [DROP_def, tlt_lem]
  THEN ASM_SIMP_TAC list_ss [DROP, FUNPOW, TL_T_def]) ;

val NOT_NULL_SNOC = Q.store_thm("NOT_NULL_SNOC",
   `!x l. ~NULL (SNOC x l)`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC[SNOC, NULL_DEF]);

(* ------------------------------------------------------------------------ *)

val LASTN_def = zDefine `
  LASTN n xs = REVERSE (TAKE n (REVERSE xs))`;

val LASTN = store_thm("LASTN",
  ``(!l. LASTN 0 l = []) /\
    (!n x l. LASTN (SUC n) (SNOC x l) = SNOC x (LASTN n l))``,
  FULL_SIMP_TAC std_ss [LASTN_def,REVERSE_SNOC,
    TAKE,REVERSE_DEF]
  THEN FULL_SIMP_TAC std_ss [SNOC_APPEND]);

val BUTLASTN_def = zDefine `
  BUTLASTN n xs = REVERSE (DROP n (REVERSE xs))`;

val BUTLASTN = store_thm("BUTLASTN",
  ``(!l. BUTLASTN 0 l = l) /\
    (!n x l. BUTLASTN (SUC n) (SNOC x l) = BUTLASTN n l)``,
  FULL_SIMP_TAC std_ss [BUTLASTN_def,DROP,
    REVERSE_REVERSE,REVERSE_SNOC]);

local
   val is_sublist_thm = Prim_rec.prove_rec_fn_exists list_Axiom
      ``(is_sublist [] (l: 'a list) = (if NULL l then T else F)) /\
        (is_sublist (CONS x t) l =
           if NULL l then T
           else (x = HD l) /\ isPREFIX (TL l) t \/ is_sublist t l)``
   val tac = ASM_REWRITE_TAC [HD, TL, NULL_DEF]
   val is_sublist_exists = Q.prove(
      `?is_sublist.
          (!l:'a list. is_sublist l [] <=> T) /\
          (!x: 'a l. is_sublist [] (CONS x l) <=> F) /\
          (!x1 l1 x2 l2.
             is_sublist (CONS x1 l1) (CONS x2 l2) <=>
             (x1 = x2) /\ isPREFIX l2 l1 \/ is_sublist l1 (CONS x2 l2))`,
      STRIP_ASSUME_TAC is_sublist_thm
      THEN Q.EXISTS_TAC `is_sublist`
      THEN tac THEN BasicProvers.Induct THEN tac)
in
   val IS_SUBLIST = Definition.new_specification
                      ("IS_SUBLIST", ["IS_SUBLIST"], is_sublist_exists)
end;

local
   val seg_exists = Q.prove(
      `?SEG.
          (!k (l:'a list). SEG 0 k l = []) /\
          (!m x l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
          (!m k x l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)`,
      Q.EXISTS_TAC
        `\m k (l: 'a list). (TAKE: num -> 'a list -> 'a list) m
                                ((DROP: num -> 'a list -> 'a list) k l)`
      THEN SIMP_TAC bool_ss [TAKE, DROP])
in
   val SEG = Definition.new_specification ("SEG", ["SEG"], seg_exists)
end;

local
    val is_suffix_thm = Prim_rec.prove_rec_fn_exists SNOC_Axiom
       ``(is_suffix l [] = T) /\
         (is_suffix l (SNOC x t) =
           if NULL l then F else (LAST l = x) /\ is_suffix (FRONT l) t)``
   val is_suffix_exists = Q.prove(
      `?is_suffix.
           (!l. is_suffix l [] <=> T) /\
           (!(x:'a) l. is_suffix [] (SNOC x l) <=> F) /\
           (!(x1:'a) l1 (x2:'a) l2.
               is_suffix (SNOC x1 l1) (SNOC x2 l2) <=>
               (x1 = x2) /\ is_suffix l1 l2)`,
      METIS_TAC [is_suffix_thm, FRONT_SNOC, LAST_SNOC,
                 NULL_DEF, NOT_NULL_SNOC])
in
   val IS_SUFFIX = Definition.new_specification
                      ("IS_SUFFIX", ["IS_SUFFIX"], is_suffix_exists)
end;

val _ = overload_on ("IS_PREFIX", ``\x y. isPREFIX y x``)
val _ = remove_ovl_mapping "<<=" {Name = "isPREFIX", Thy = "list"}
val _ = overload_on ("<<=", ``\x y. isPREFIX x y``)
(* second call makes the infix the preferred printing form *)

(* ======================================================================== *)

Theorem LENGTH_NOT_NULL:
   !l. 0 < LENGTH l <=> ~NULL l
Proof
   BasicProvers.Induct THEN REWRITE_TAC [LENGTH, NULL, NOT_LESS_0, LESS_0]
QED

(* |- !(x:'a) l. ~([] = SNOC x l) *)
val NOT_NIL_SNOC = Theory.save_thm ("NOT_NIL_SNOC",
   valOf (hd (Prim_rec.prove_constructors_distinct SNOC_Axiom)));

val NOT_SNOC_NIL = Theory.save_thm ("NOT_SNOC_NIL", GSYM NOT_NIL_SNOC);

val SNOC_EQ_LENGTH_EQ = Q.store_thm ("SNOC_EQ_LENGTH_EQ",
   `!x1 l1 x2 l2. (SNOC x1 l1 = SNOC x2 l2) ==> (LENGTH l1 = LENGTH l2)`,
   REPEAT STRIP_TAC
   THEN RULE_ASSUM_TAC (AP_TERM ``LENGTH``)
   THEN RULE_ASSUM_TAC
          (REWRITE_RULE [LENGTH_SNOC, LENGTH, EQ_MONO_ADD_EQ, ADD1])
   THEN FIRST_ASSUM ACCEPT_TAC);

(* |- !x l. SNOC x l = REVERSE (x::REVERSE l) *)
val SNOC_REVERSE_CONS = Theory.save_thm ("SNOC_REVERSE_CONS",
   GEN_ALL (REWRITE_RULE [REVERSE_REVERSE]
      (AP_TERM ``REVERSE`` (SPEC_ALL REVERSE_SNOC))));

val FOLDR_SNOC = Q.store_thm ("FOLDR_SNOC",
   `!f e x l. FOLDR f e (SNOC x l) = FOLDR f (f x e) l`,
   REPEAT (FILTER_GEN_TAC ``l: 'a list``)
   THEN BasicProvers.Induct
   THEN REWRITE_TAC [SNOC, FOLDR]
   THEN REPEAT GEN_TAC
   THEN ASM_REWRITE_TAC []);

val FOLDR_FOLDL = Q.store_thm ("FOLDR_FOLDL",
   `!f e. MONOID f e ==> !l. FOLDR f e l = FOLDL f e l`,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [MONOID_DEF, ASSOC_DEF, LEFT_ID_DEF, RIGHT_ID_DEF]
   THEN STRIP_TAC
   THEN BasicProvers.Induct
   THEN REWRITE_TAC [FOLDL, FOLDR]
   THEN FIRST_ASSUM SUBST1_TAC
   THEN GEN_TAC
   THEN SPEC_TAC (``l:'a list``, ``l:'a list``)
   THEN SNOC_INDUCT_TAC
   THEN1 ASM_REWRITE_TAC [FOLDL]
   THEN PURE_ONCE_REWRITE_TAC [FOLDL_SNOC]
   THEN GEN_TAC
   THEN ASM_REWRITE_TAC []);

val LENGTH_FOLDR = Q.store_thm ("LENGTH_FOLDR",
   `!l. LENGTH l = FOLDR (\x l'. SUC l') 0 l`,
   BasicProvers.Induct
   THEN REWRITE_TAC [LENGTH, FOLDR]
   THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
   THEN ASM_REWRITE_TAC []);

val LENGTH_FOLDL = Q.store_thm ("LENGTH_FOLDL",
   `!l. LENGTH l = FOLDL (\l' x. SUC l') 0 l`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH_SNOC, FOLDL_SNOC]
   THEN1 REWRITE_TAC [LENGTH, FOLDL]
   THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
   THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
   THEN ASM_REWRITE_TAC []);

val MAP_FOLDR = Q.store_thm ("MAP_FOLDR",
   `!f l. MAP f l = FOLDR (\x l'. CONS (f x) l') [] l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [MAP, FOLDR]
   THEN GEN_TAC
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN ASM_REWRITE_TAC []);

val MAP_FOLDL = Q.store_thm ("MAP_FOLDL",
   `!f l. MAP f l = FOLDL (\l' x. SNOC (f x) l') [] l`,
   GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [MAP_SNOC, FOLDL_SNOC]
   THEN1 REWRITE_TAC [FOLDL, MAP]
   THEN FIRST_ASSUM (SUBST1_TAC o SYM)
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN GEN_TAC
   THEN REFL_TAC);

Theorem FOLDL_CONG_invariant:
  !P f1 f2 l e.
  P e /\
  (!x a. MEM x l /\ P a ==> f1 a x = f2 a x /\ P (f2 a x))
  ==>
  FOLDL f1 e l = FOLDL f2 e l /\ P (FOLDL f2 e l)
Proof
  ntac 3 gen_tac \\ Induct \\ rw[]
QED

val FILTER_FOLDR = Q.store_thm ("FILTER_FOLDR",
   `!P l. FILTER P l = FOLDR (\x l'. if P x then CONS x l' else l') [] l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [FILTER, FOLDR]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN ASM_REWRITE_TAC []);

val FILTER_SNOC = Q.store_thm ("FILTER_SNOC",
   `!P x l.
      FILTER P (SNOC x l) = if P x then SNOC x (FILTER P l) else FILTER P l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [FILTER, SNOC]
   THEN REPEAT GEN_TAC
   THEN REPEAT COND_CASES_TAC
   THEN ASM_REWRITE_TAC [SNOC]);

val FILTER_FOLDL = Q.store_thm ("FILTER_FOLDL",
   `!P l. FILTER P l = FOLDL (\l' x. if P x then SNOC x l' else l') [] l`,
   GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [FILTER, FOLDL]
   THEN REWRITE_TAC [FILTER_SNOC, FOLDL_SNOC]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN ASM_REWRITE_TAC []);

val FILTER_COMM = Q.store_thm ("FILTER_COMM",
   `!f1 f2 l. FILTER f1 (FILTER f2 l) = FILTER f2 (FILTER f1 l)`,
   NTAC 2 GEN_TAC
   THEN BasicProvers.Induct
   THEN REWRITE_TAC [FILTER]
   THEN GEN_TAC
   THEN REPEAT COND_CASES_TAC
   THEN ASM_REWRITE_TAC [FILTER]);

val FILTER_IDEM = Q.store_thm ("FILTER_IDEM",
   `!f l. FILTER f (FILTER f l) = FILTER f l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [FILTER]
   THEN REPEAT GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC [FILTER]);

val FILTER_MAP = Q.store_thm ("FILTER_MAP",
   `!f1 f2 l. FILTER f1 (MAP f2 l) = MAP f2 (FILTER (f1 o f2) l)`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [FILTER, MAP]
   THEN REPEAT GEN_TAC
   THEN PURE_ONCE_REWRITE_TAC [combinTheory.o_THM]
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC [FILTER, MAP]);

val LENGTH_FILTER_LEQ = Q.store_thm ("LENGTH_FILTER_LEQ",
   `!P l. LENGTH (FILTER P l) <= LENGTH l`,
   BasicProvers.Induct_on `l`
   THEN SRW_TAC [] [numLib.DECIDE ``!a b. a <= b ==> a <= SUC b``]);

val EL_FILTER = Q.prove(
   `!i l P. i < LENGTH (FILTER P l) ==> P (EL i (FILTER P l))`,
   BasicProvers.Induct_on `l`
   THEN SRW_TAC [] []
   THEN Cases_on `i`
   THEN SRW_TAC [numSimps.ARITH_ss] []);

val FILTER_EQ_lem = Q.prove(
   `!l l2 P h. ~P h ==> (FILTER P l <> h :: l2)`,
   SRW_TAC [] [LIST_EQ_REWRITE]
   THEN Q.EXISTS_TAC `0`
   THEN SRW_TAC [numSimps.ARITH_ss] []
   THEN `0 < LENGTH (FILTER P l)` by numLib.DECIDE_TAC
   THEN IMP_RES_TAC EL_FILTER
   THEN FULL_SIMP_TAC (srw_ss()) []
   THEN metisLib.METIS_TAC []);

val FILTER_EQ = Q.store_thm ("FILTER_EQ",
   `!P1 P2 l. (FILTER P1 l = FILTER P2 l) = (!x. MEM x l ==> (P1 x = P2 x))`,
   Induct_on `l`
   THEN SRW_TAC [] []
   THEN metisLib.METIS_TAC [FILTER_EQ_lem]);

val LENGTH_SEG = Q.store_thm ("LENGTH_SEG",
   `!n k l. n + k <= LENGTH l ==> (LENGTH (SEG n k l) = n)`,
   NTAC 2 BasicProvers.Induct
   THEN REWRITE_TAC [SEG, LENGTH]
   THEN BasicProvers.Induct
   THENL [
      REWRITE_TAC [LENGTH, ADD_0, LESS_OR_EQ, numTheory.NOT_SUC, NOT_LESS_0],
      REWRITE_TAC [SEG, LENGTH, ADD, LESS_EQ_MONO, INV_SUC_EQ]
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o (SPEC ``0n``)),
      REWRITE_TAC [LENGTH, ADD, LESS_OR_EQ, numTheory.NOT_SUC, NOT_LESS_0],
      REWRITE_TAC [LENGTH, SEG, GSYM ADD_SUC, LESS_EQ_MONO]
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val APPEND_NIL = Q.store_thm ("APPEND_NIL",
   `(!l. APPEND l [] = l) /\ (!l. APPEND [] l = l)`,
   CONJ_TAC THENL [BasicProvers.Induct, ALL_TAC] THEN ASM_REWRITE_TAC [APPEND]);

val APPEND_FOLDR = Q.store_thm ("APPEND_FOLDR",
   `!l1 l2. APPEND l1 l2 = FOLDR CONS l2 l1`,
   BasicProvers.Induct THEN ASM_REWRITE_TAC [APPEND, FOLDR]);

val APPEND_FOLDL = Q.store_thm ("APPEND_FOLDL",
   `!l1 l2. APPEND l1 l2 = FOLDL (\l' x. SNOC x l') l1 l2`,
   GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [APPEND_NIL, FOLDL]
   THEN ASM_REWRITE_TAC [APPEND_SNOC, FOLDL_SNOC]
   THEN GEN_TAC
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val FOLDR_APPEND = Q.store_thm ("FOLDR_APPEND",
   `!f e l1 l2. FOLDR f e (APPEND l1 l2) = FOLDR f (FOLDR f e l2) l1`,
   REPEAT GEN_TAC
   THEN MAP_EVERY Q.SPEC_TAC
          [(`l1`, `l1`), (`e`, `e`), (`f`, `f`), (`l2`, `l2`)]
   THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [APPEND_NIL, FOLDR]
   THEN REWRITE_TAC [APPEND_SNOC, FOLDR_SNOC]
   THEN REPEAT GEN_TAC
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val FOLDL_APPEND = Q.store_thm ("FOLDL_APPEND",
   `!f e l1 l2. FOLDL f e (APPEND l1 l2) = FOLDL f (FOLDL f e l1) l2`,
   BasicProvers.Induct_on `l1`
   THEN REWRITE_TAC [APPEND, FOLDL]
   THEN REPEAT GEN_TAC
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val CONS_APPEND = Q.store_thm ("CONS_APPEND",
   `!x l. CONS x l = APPEND [x] l`,
   GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [APPEND_NIL]
   THEN ASM_REWRITE_TAC [APPEND_SNOC, GSYM (CONJUNCT2 SNOC)]);

val ASSOC_APPEND = Q.store_thm ("ASSOC_APPEND",
   `ASSOC APPEND`,
   REWRITE_TAC [ASSOC_DEF, APPEND_ASSOC]);

val RIGHT_ID_APPEND_NIL = Q.prove(
   `RIGHT_ID APPEND []`,
   REWRITE_TAC [RIGHT_ID_DEF, APPEND, APPEND_NIL]);

val LEFT_ID_APPEND_NIL = Q.prove(
   `LEFT_ID APPEND []`,
   REWRITE_TAC [LEFT_ID_DEF, APPEND, APPEND_NIL]);

val MONOID_APPEND_NIL = Q.store_thm ("MONOID_APPEND_NIL",
   `MONOID APPEND []`,
   REWRITE_TAC [MONOID_DEF, APPEND, APPEND_NIL, APPEND_ASSOC, LEFT_ID_DEF,
                ASSOC_DEF, RIGHT_ID_DEF]);

val FLAT_SNOC = Q.store_thm ("FLAT_SNOC",
   `!x l. FLAT (SNOC x l) = APPEND (FLAT l) x`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [FLAT, SNOC, APPEND, APPEND_NIL, APPEND_ASSOC]);

val FLAT_FOLDR = Q.store_thm ("FLAT_FOLDR",
   `!l. FLAT l = FOLDR APPEND [] l`,
   BasicProvers.Induct THEN ASM_REWRITE_TAC [FLAT, FOLDR]);

val FLAT_FOLDL = Q.store_thm ("FLAT_FOLDL",
   `!l. FLAT l = FOLDL APPEND [] l`,
   SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [FLAT, FOLDL]
   THEN ASM_REWRITE_TAC [FLAT_SNOC, FOLDL_SNOC]);

val LENGTH_FLAT = Q.store_thm ("LENGTH_FLAT",
   `!l. LENGTH (FLAT l) = SUM (MAP LENGTH l)`,
   BasicProvers.Induct
   THEN REWRITE_TAC [FLAT]
   THEN1 REWRITE_TAC [LENGTH, MAP, SUM]
   THEN ASM_REWRITE_TAC [LENGTH_APPEND, MAP, SUM]);

val REVERSE_FOLDR = Q.store_thm ("REVERSE_FOLDR",
   `!l. REVERSE l = FOLDR SNOC [] l`,
   BasicProvers.Induct THEN ASM_REWRITE_TAC [REVERSE, FOLDR]);

val REVERSE_FOLDL = Q.store_thm ("REVERSE_FOLDL",
   `!l. REVERSE l = FOLDL (\l' x. CONS x l') [] l`,
   SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [REVERSE, FOLDL]
   THEN REWRITE_TAC [REVERSE_SNOC, FOLDL_SNOC]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN ASM_REWRITE_TAC []);

val ALL_EL_MAP = Q.store_thm ("ALL_EL_MAP",
   `!P f l. EVERY P (MAP f l) = EVERY (P o f) l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [EVERY_DEF, MAP]
   THEN ASM_REWRITE_TAC [combinTheory.o_DEF]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val MEM_EXISTS = Q.store_thm ("MEM_EXISTS",
  `!x:'a l. MEM x l = EXISTS ($= x) l`,
  Induct_on `l` THEN ASM_REWRITE_TAC [EXISTS_DEF, MEM]);

val SUM_FOLDR = Q.store_thm ("SUM_FOLDR",
   `!l. SUM l = FOLDR $+ 0 l`,
   BasicProvers.Induct
   THEN REWRITE_TAC [SUM, FOLDR, ADD]
   THEN GEN_TAC
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN FIRST_ASSUM SUBST1_TAC
   THEN REFL_TAC);

val SUM_FOLDL = Q.store_thm ("SUM_FOLDL",
   `!l. SUM l = FOLDL $+ 0 l`,
   SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [SUM, FOLDL]
   THEN REWRITE_TAC [SUM_SNOC, FOLDL_SNOC]
   THEN GEN_TAC
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN FIRST_ASSUM SUBST1_TAC
   THEN REFL_TAC);

(*
   |- (!l. [] <<= l <=> T) /\ (!x l. x::l <<= [] <=> F) /\
      !x1 l1 x2 l2. x2::l2 <<= x1::l1 <=> (x1 = x2) /\ l2 <<= l1``
*)
val IS_PREFIX = save_thm ("IS_PREFIX",
   let
      val [c1, c2, c3] = CONJUNCTS isPREFIX_THM
   in
      LIST_CONJ [GEN ``l:'a list`` c1,
                 (CONV_RULE (RENAME_VARS_CONV ["x", "l"]) o
                  GENL [``h:'a``, ``t:'a list``]) c2,
                 (CONV_RULE (RENAME_VARS_CONV ["x1", "l1", "x2", "l2"]) o
                  GENL [``h2:'a``, ``t2:'a list``, ``h1:'a``, ``t1:'a list``] o
                  CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])))
                 c3]
   end)

val IS_PREFIX_APPEND = Q.store_thm ("IS_PREFIX_APPEND",
   `!l1 l2. isPREFIX l2 l1 = ?l. l1 = APPEND l2 l`,
   BasicProvers.Induct
   THENL [
     BasicProvers.Induct
     THENL [
       REWRITE_TAC [IS_PREFIX, APPEND]
       THEN Q.EXISTS_TAC `[]`
       THEN REFL_TAC,
       REWRITE_TAC [IS_PREFIX, APPEND, GSYM NOT_CONS_NIL]],
       BasicProvers.Induct_on `l2`
       THENL [
         REWRITE_TAC [IS_PREFIX, APPEND]
         THEN GEN_TAC
         (* **list_Axiom** variable dependancy *)
         THEN Q.EXISTS_TAC `CONS h l1`
         THEN REFL_TAC,
         ASM_REWRITE_TAC [IS_PREFIX, APPEND, CONS_11]
         THEN REPEAT GEN_TAC
         THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV)
         THEN REFL_TAC]]);

val IS_SUFFIX_APPEND = Q.store_thm ("IS_SUFFIX_APPEND",
   `!l1 l2. IS_SUFFIX l1 l2 = ?l. l1 = APPEND l l2`,
    SNOC_INDUCT_TAC THENL [
     SNOC_INDUCT_TAC THENL [
      REWRITE_TAC [IS_SUFFIX, APPEND_NIL]
      THEN EXISTS_TAC ``[]:'a list`` THEN REFL_TAC,
      REWRITE_TAC [IS_SUFFIX, APPEND_SNOC]
      THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
      THEN REWRITE_TAC [GSYM NULL_EQ, NOT_NULL_SNOC]],
     GEN_TAC THEN SNOC_INDUCT_TAC THENL [
      REWRITE_TAC [IS_SUFFIX, APPEND_NIL]
      THEN EXISTS_TAC ``SNOC (x:'a) l1`` THEN REFL_TAC,
      ASM_REWRITE_TAC [IS_SUFFIX, APPEND_SNOC, SNOC_11]
      THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);

val NOT_NIL_APPEND_CONS2 = Q.prove(
   `!l1 l2 x. ~([] = APPEND l1 (CONS x l2))`,
   BasicProvers.Induct THEN REWRITE_TAC [APPEND] THEN REPEAT GEN_TAC
   THEN MATCH_ACCEPT_TAC (GSYM NOT_CONS_NIL))

val IS_SUBLIST_APPEND = Q.store_thm ("IS_SUBLIST_APPEND",
   `!l1 l2. IS_SUBLIST l1 l2 = ?l l'. l1 = APPEND l (APPEND l2 l')`,
    BasicProvers.Induct THEN REPEAT (FILTER_GEN_TAC ``l2:'a list``)
    THEN BasicProvers.Induct THENL [
        REWRITE_TAC [IS_SUBLIST, APPEND]
        THEN MAP_EVERY EXISTS_TAC [``[]:'a list``, ``[]:'a list``]
        THEN REWRITE_TAC [APPEND],
        GEN_TAC THEN REWRITE_TAC [IS_SUBLIST, APPEND, NOT_NIL_APPEND_CONS2],
        REWRITE_TAC [IS_SUBLIST, APPEND]
        (* **list_Axiom** variable dependancy *)
        THEN MAP_EVERY EXISTS_TAC [``[h]:'a list``, ``l1:'a list``]
        THEN MATCH_ACCEPT_TAC CONS_APPEND,
        GEN_TAC THEN REWRITE_TAC [IS_SUBLIST] THEN EQ_TAC
        THEN ONCE_ASM_REWRITE_TAC [IS_PREFIX_APPEND] THENL [
          STRIP_TAC THENL [
            MAP_EVERY EXISTS_TAC [``[]:'a list``, ``l:'a list``]
            THEN ASM_REWRITE_TAC [APPEND],
            (* **list_Axiom** variable dependancy *)
            MAP_EVERY EXISTS_TAC [``(CONS h l):'a list``, ``l':'a list``]
            THEN ONCE_ASM_REWRITE_TAC [APPEND] THEN REFL_TAC],
          CONV_TAC LEFT_IMP_EXISTS_CONV THEN BasicProvers.Induct THENL [
            REWRITE_TAC [APPEND, CONS_11]
            THEN STRIP_TAC THEN DISJ1_TAC
            THEN ASM_REWRITE_TAC [IS_PREFIX_APPEND]
            THEN EXISTS_TAC ``l':'a list`` THEN REFL_TAC,
            GEN_TAC THEN REWRITE_TAC [APPEND, CONS_11]
            THEN STRIP_TAC THEN DISJ2_TAC
            THEN MAP_EVERY EXISTS_TAC [``l:'a list``, ``l':'a list``]
            THEN FIRST_ASSUM ACCEPT_TAC]]]);

val IS_PREFIX_IS_SUBLIST = Q.store_thm ("IS_PREFIX_IS_SUBLIST",
   `!l1 l2. IS_PREFIX l1 l2 ==> IS_SUBLIST l1 l2`,
   LIST_INDUCT_TAC
   THEN TRY (FILTER_GEN_TAC ``l2:'a list``)
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [IS_PREFIX, IS_SUBLIST]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC []);

val IS_SUFFIX_IS_SUBLIST = Q.store_thm ("IS_SUFFIX_IS_SUBLIST",
   `!l1 l2. IS_SUFFIX l1 l2 ==> IS_SUBLIST l1 l2`,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [IS_SUFFIX_APPEND, IS_SUBLIST_APPEND]
   THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
   THEN MAP_EVERY EXISTS_TAC [``l:'a list``, ``[]:'a list``]
   THEN REWRITE_TAC [APPEND_NIL]);

Theorem IS_SUFFIX_CONS:
  !l1 l2 a. IS_SUFFIX l1 l2 ==> IS_SUFFIX (a::l1) l2
Proof
  srw_tac[][IS_SUFFIX_APPEND] >> Q.EXISTS_TAC ‘a::l’ >> srw_tac[][]
QED

Theorem IS_SUFFIX_APPEND1:
  !l1 l2 l. IS_SUFFIX l2 l ==> IS_SUFFIX (l1 ++ l2) l
Proof
  Induct >> fs[IS_SUFFIX_CONS]
QED

Theorem IS_SUFFIX_TRANS:
  !l1 l2 l3. IS_SUFFIX l1 l2 /\ IS_SUFFIX l2 l3 ==> IS_SUFFIX l1 l3
Proof
  rw[IS_SUFFIX_APPEND] \\ metis_tac[APPEND_ASSOC]
QED

val NOT_NIL_APPEND_SNOC2 = Q.prove(
   `!l1 l2 x. ~([] = (APPEND l1 (SNOC x l2)))`,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [APPEND_SNOC]
   THEN REPEAT GEN_TAC
   THEN MATCH_ACCEPT_TAC NOT_NIL_SNOC)

val IS_PREFIX_REVERSE = Q.store_thm ("IS_PREFIX_REVERSE",
   `!l1 l2. IS_PREFIX (REVERSE l1) (REVERSE l2) = IS_SUFFIX l1 l2`,
   SNOC_INDUCT_TAC
   THEN REPEAT (FILTER_GEN_TAC ``l2:'a list``)
   THEN SNOC_INDUCT_TAC
   THENL [
        REWRITE_TAC [IS_SUFFIX_APPEND, REVERSE, IS_PREFIX]
        THEN EXISTS_TAC ``[]:'a list``
        THEN REWRITE_TAC [APPEND],
        GEN_TAC
        THEN REWRITE_TAC [IS_SUFFIX_APPEND, REVERSE, REVERSE_SNOC, IS_PREFIX]
        THEN CONV_TAC NOT_EXISTS_CONV
        THEN GEN_TAC
        THEN REWRITE_TAC [APPEND, NOT_NIL_APPEND_SNOC2],
        REWRITE_TAC [IS_SUFFIX_APPEND, REVERSE, APPEND_NIL, IS_PREFIX]
        THEN EXISTS_TAC ``SNOC (x:'a) l1``
        THEN REFL_TAC,
        GEN_TAC
        THEN REWRITE_TAC [IS_SUFFIX_APPEND, REVERSE_SNOC, IS_PREFIX]
        THEN PURE_ONCE_ASM_REWRITE_TAC []
        THEN REWRITE_TAC [IS_SUFFIX_APPEND, APPEND_SNOC, SNOC_11]
        THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_AND_CONV)
        THEN REFL_TAC]);

(* |- !l1 l2. IS_SUFFIX (REVERSE l1) (REVERSE l2) = IS_PREFIX l1 l2 *)
val IS_SUFFIX_REVERSE = save_thm ("IS_SUFFIX_REVERSE",
   IS_PREFIX_REVERSE
   |> SPECL [``REVERSE (l1:'a list)``, ``REVERSE (l2:'a list)``]
   |> REWRITE_RULE [REVERSE_REVERSE]
   |> SYM |> GEN_ALL);

val IS_SUFFIX_CONS2_E = Q.store_thm ("IS_SUFFIX_CONS2_E",
   `!s h t. IS_SUFFIX s (h::t) ==> IS_SUFFIX s t`,
   SRW_TAC [] [IS_SUFFIX_APPEND]
   THEN metisLib.METIS_TAC [APPEND, APPEND_ASSOC]);

val IS_SUFFIX_REFL = Q.store_thm ("IS_SUFFIX_REFL",
   `!l. IS_SUFFIX l l`,
   SRW_TAC [][IS_SUFFIX_APPEND] THEN metisLib.METIS_TAC [APPEND]);
val () = export_rewrites ["IS_SUFFIX_REFL"]

val IS_SUBLIST_REVERSE = Q.store_thm ("IS_SUBLIST_REVERSE",
   `!l1 l2. IS_SUBLIST (REVERSE l1) (REVERSE l2) = IS_SUBLIST l1 l2`,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [IS_SUBLIST_APPEND]
   THEN EQ_TAC
   THEN STRIP_TAC
   THENL [
      MAP_EVERY EXISTS_TAC [``REVERSE(l':'a list)``, ``REVERSE(l:'a list)``]
      THEN FIRST_ASSUM (SUBST1_TAC o
         (REWRITE_RULE [REVERSE_REVERSE, REVERSE_APPEND]) o
         (AP_TERM ``REVERSE:'a list -> 'a list``))
      THEN REWRITE_TAC [APPEND_ASSOC],
      FIRST_ASSUM SUBST1_TAC
      THEN REWRITE_TAC [REVERSE_APPEND, APPEND_ASSOC]
      THEN MAP_EVERY EXISTS_TAC
             [``REVERSE(l':'a list)``, ``REVERSE(l:'a list)``]
      THEN REFL_TAC]);

val PREFIX_FOLDR = Q.store_thm ("PREFIX_FOLDR",
   `!P l. PREFIX P l = FOLDR (\x l'. if P x then CONS x l' else []) [] l`,
   GEN_TAC
   THEN REWRITE_TAC [PREFIX_DEF]
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [FOLDR, SPLITP]
   THEN GEN_TAC
   THEN REWRITE_TAC [combinTheory.o_THM]
   THEN BETA_TAC
   (* **list_Axiom** variable dependancy *)
   THEN ASM_CASES_TAC ``(P:'a->bool) x``
   THEN ASM_REWRITE_TAC []);

val PREFIX = Q.store_thm ("PREFIX",
   `(!P. PREFIX P [] = []) /\
    (!P x l. PREFIX P (CONS x l) = if P x then CONS x (PREFIX P l) else [])`,
   REWRITE_TAC [PREFIX_FOLDR, FOLDR]
   THEN REPEAT GEN_TAC
   THEN BETA_TAC
   THEN REFL_TAC);

val IS_PREFIX_PREFIX = Q.store_thm ("IS_PREFIX_PREFIX",
   `!P l. IS_PREFIX l (PREFIX P l)`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [IS_PREFIX, PREFIX]
   THEN REPEAT GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC [IS_PREFIX]);

val LENGTH_SCANL = Q.store_thm ("LENGTH_SCANL",
   `!f e l. LENGTH (SCANL f e l) = SUC (LENGTH l)`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [SCANL, LENGTH]
   THEN REPEAT GEN_TAC
   THEN ASM_REWRITE_TAC []);

val LENGTH_SCANR = Q.store_thm ("LENGTH_SCANR",
   `!f e l. LENGTH (SCANR f e l) = SUC (LENGTH l)`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [SCANR]
   THEN CONV_TAC (ONCE_DEPTH_CONV pairLib.let_CONV)
   THEN REPEAT GEN_TAC
   THEN ASM_REWRITE_TAC [LENGTH]);

val COMM_MONOID_FOLDL = Q.store_thm ("COMM_MONOID_FOLDL",
   `!f. COMM f ==> !e'. MONOID f e' ==> !e l. FOLDL f e l = f e (FOLDL f e' l)`,
   REWRITE_TAC [MONOID_DEF, ASSOC_DEF, LEFT_ID_DEF, COMM_DEF]
   THEN REPEAT STRIP_TAC
   THEN SPEC_TAC (``e:'a``,``e:'a``)
   THEN SPEC_TAC (``l:'a list``,``l:'a list``)
   THEN LIST_INDUCT_TAC
   THEN PURE_ONCE_REWRITE_TAC [FOLDL]
   THENL [
      GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC []
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM),
      REPEAT GEN_TAC THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC [t])
      THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC [t])
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM)]);

val COMM_MONOID_FOLDR = Q.store_thm ("COMM_MONOID_FOLDR",
   `!f. COMM f ==> !e'. MONOID f e' ==> !e l. FOLDR f e l = f e (FOLDR f e' l)`,
   REWRITE_TAC [MONOID_DEF, ASSOC_DEF, LEFT_ID_DEF, COMM_DEF]
   THEN GEN_TAC
   THEN DISCH_THEN
      (fn th_sym => GEN_TAC THEN DISCH_THEN
        (fn th_assoc_etc =>
            let
               val th_assoc = CONJUNCT1 th_assoc_etc
               val th_ident = CONJUNCT2(CONJUNCT2 th_assoc_etc)
            in
               GEN_TAC
               THEN LIST_INDUCT_TAC
               THEN PURE_ONCE_REWRITE_TAC [FOLDR] THENL [
                 PURE_ONCE_REWRITE_TAC [th_sym]
                 THEN MATCH_ACCEPT_TAC (GSYM th_ident),
                 REPEAT GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC []
                 THEN PURE_ONCE_REWRITE_TAC [th_ident]
                 THEN PURE_ONCE_REWRITE_TAC [th_assoc]
                 THEN AP_THM_TAC THEN AP_TERM_TAC
                 THEN MATCH_ACCEPT_TAC (GSYM th_sym)]
            end)));

val FCOMM_FOLDR_APPEND = Q.store_thm ("FCOMM_FOLDR_APPEND",
   `!g f.
      FCOMM g f ==>
      !e. LEFT_ID g e ==>
          !l1 l2. FOLDR f e (APPEND l1 l2) = g (FOLDR f e l1) (FOLDR f e l2)`,
    REWRITE_TAC [FCOMM_DEF, LEFT_ID_DEF]
    THEN REPEAT GEN_TAC
    THEN REPEAT DISCH_TAC
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC [APPEND, FOLDR]);

val FCOMM_FOLDL_APPEND = Q.store_thm ("FCOMM_FOLDL_APPEND",
   `!f g.
      FCOMM f g ==>
      !e. RIGHT_ID g e ==>
          !l1 l2. FOLDL f e (APPEND l1 l2) = g (FOLDL f e l1) (FOLDL f e l2)`,
   REWRITE_TAC [FCOMM_DEF, RIGHT_ID_DEF]
   THEN REPEAT GEN_TAC
   THEN DISCH_THEN (ASSUME_TAC o GSYM)
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [APPEND_NIL, APPEND_SNOC, FOLDL_SNOC, FOLDL]);

(* ??

val MONOID_FOLDR_APPEND_FOLDR = Q.prove(
   `!(f:'a->'a->'a) e. MONOID f e ==>
     (!l1 l2. FOLDR f e (APPEND l1 l2) = f (FOLDR f e l1) (FOLDR f e l2))`,
    REWRITE_TAC [MONOID_DEF, GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC []);

val MONOID_FOLDL_APPEND_FOLDL = Q.prove(
   `!(f:'a->'a->'a) e. MONOID f e ==>
      (!l1 l2. FOLDL f e (APPEND l1 l2) = f (FOLDL f e l1) (FOLDL f e l2))`,
    REWRITE_TAC [MONOID_DEF, GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC []);

?? *)

val FOLDL_SINGLE = Q.store_thm ("FOLDL_SINGLE",
   `!f e x. FOLDL f e [x] = f e x`,
   REWRITE_TAC [FOLDL]);

val FOLDR_SINGLE = Q.store_thm ("FOLDR_SINGLE",
   `!f e x. FOLDR f e [x] = f x e`,
   REWRITE_TAC [FOLDR]);

val FOLDR_CONS_NIL = Q.store_thm ("FOLDR_CONS_NIL",
   `!l. FOLDR CONS [] l = l`,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FOLDR]);

val FOLDL_SNOC_NIL = Q.store_thm ("FOLDL_SNOC_NIL",
   `!l. FOLDL (\xs x. SNOC x xs) [] l = l`,
   SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [FOLDL, FOLDL_SNOC]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val FOLDR_FOLDL_REVERSE = Q.store_thm ("FOLDR_FOLDL_REVERSE",
   `!f e l. FOLDR f e l = FOLDL (\x y. f y x) e (REVERSE l)`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [FOLDR, FOLDL, REVERSE, FOLDL_SNOC]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val FOLDL_FOLDR_REVERSE = Q.store_thm ("FOLDL_FOLDR_REVERSE",
   `!f e l. FOLDL f e l = FOLDR (\x y. f y x) e (REVERSE l)`,
   GEN_TAC
   THEN GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [REVERSE, FOLDR, FOLDL, REVERSE_SNOC, FOLDR_SNOC]
   THEN BETA_TAC
   THEN ASM_REWRITE_TAC [FOLDL_SNOC]);

val FOLDR_REVERSE = Q.store_thm ("FOLDR_REVERSE",
   `!f e l. FOLDR f e (REVERSE l) = FOLDL (\x y. f y x) e l`,
   REWRITE_TAC [FOLDR_FOLDL_REVERSE, REVERSE_REVERSE]);

val FOLDL_REVERSE = Q.store_thm ("FOLDL_REVERSE",
   `!f e l. FOLDL f e (REVERSE l) = FOLDR (\x y. f y x) e l`,
   REWRITE_TAC [FOLDL_FOLDR_REVERSE, REVERSE_REVERSE]);

val FOLDR_MAP = Q.store_thm ("FOLDR_MAP",
   `!f e g l. FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [FOLDL, MAP, FOLDR] THEN BETA_TAC
   THEN REWRITE_TAC []);

val FOLDL_MAP = Q.store_thm ("FOLDL_MAP",
   `!f e g l.  FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l`,
   NTAC 3 GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [MAP, FOLDL, FOLDL_SNOC, MAP_SNOC, FOLDR]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val EVERY_FOLDR = Q.store_thm ("EVERY_FOLDR",
   `!P l. EVERY P l = FOLDR (\x l'. P x /\ l') T l`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [EVERY_DEF, FOLDR, MAP]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val EVERY_FOLDL = Q.store_thm ("EVERY_FOLDL",
   `!P l. EVERY P l = FOLDL (\l' x. l' /\ P x) T l`,
   GEN_TAC
   THEN SNOC_INDUCT_TAC
   THENL [
      REWRITE_TAC [EVERY_DEF, FOLDL, MAP],
      ASM_REWRITE_TAC [EVERY_SNOC, FOLDL_SNOC, MAP_SNOC]]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val EXISTS_FOLDR = Q.store_thm ("EXISTS_FOLDR",
   `!P l. EXISTS P l = FOLDR (\x l'. P x \/ l') F l`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [EXISTS_DEF, MAP, FOLDR]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val EXISTS_FOLDL = Q.store_thm ("EXISTS_FOLDL",
   `!P l. EXISTS P l = FOLDL (\l' x. l' \/ P x) F l`,
   GEN_TAC THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [EXISTS_DEF, MAP, FOLDL]
   THEN REWRITE_TAC [EXISTS_SNOC, MAP_SNOC, FOLDL_SNOC]
   THEN BETA_TAC
   THEN GEN_TAC
   THEN FIRST_ASSUM SUBST1_TAC
   THEN MATCH_ACCEPT_TAC DISJ_SYM);

val EVERY_FOLDR_MAP = Q.store_thm ("EVERY_FOLDR_MAP",
   `!P l. EVERY P l = FOLDR $/\ T (MAP P l)`,
   REWRITE_TAC [EVERY_FOLDR, FOLDR_MAP]);

val EVERY_FOLDL_MAP = Q.store_thm ("EVERY_FOLDL_MAP",
   `!P l. EVERY P l = FOLDL $/\ T (MAP P l)`,
   REWRITE_TAC [EVERY_FOLDL, FOLDL_MAP]);

val EXISTS_FOLDR_MAP = Q.store_thm ("EXISTS_FOLDR_MAP",
   `!P l. EXISTS P l = FOLDR $\/ F (MAP P l)`,
   REWRITE_TAC [EXISTS_FOLDR, FOLDR_MAP]);

val EXISTS_FOLDL_MAP = Q.store_thm ("EXISTS_FOLDL_MAP",
   `!P l. EXISTS P l = FOLDL $\/ F (MAP P l)`,
   REWRITE_TAC [EXISTS_FOLDL, FOLDL_MAP]);

val FOLDR_FILTER = Q.store_thm ("FOLDR_FILTER",
   `!f e P l.
       FOLDR f e (FILTER P l) = FOLDR (\x y. if P x then f x y else y) e l`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [FOLDL, FILTER, FOLDR]
   THEN BETA_TAC
   THEN REPEAT GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC [FOLDR]);

val FOLDL_FILTER = Q.store_thm ("FOLDL_FILTER",
   `!f e P l.
       FOLDL f e (FILTER P l) = FOLDL (\x y. if P y then f x y else x) e l`,
    GEN_TAC
    THEN GEN_TAC
    THEN GEN_TAC
    THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC
            [FOLDL, FOLDR_SNOC, FOLDL_SNOC, FILTER, FOLDR, FILTER_SNOC]
    THEN BETA_TAC
    THEN GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC [FOLDL_SNOC]);

val ASSOC_FOLDR_FLAT = Q.store_thm ("ASSOC_FOLDR_FLAT",
   `!f. ASSOC f ==>
     !e. LEFT_ID f e ==>
       !l. FOLDR f e (FLAT l) = FOLDR f e (MAP (FOLDR f e) l)`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [FLAT, MAP, FOLDR]
   THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
   THEN IMP_RES_TAC FCOMM_FOLDR_APPEND
   THEN ASM_REWRITE_TAC []);

val ASSOC_FOLDL_FLAT = Q.store_thm ("ASSOC_FOLDL_FLAT",
   `!f. ASSOC f ==>
     !e. RIGHT_ID f e ==>
       !l. FOLDL f e (FLAT l) = FOLDL f e (MAP (FOLDL f e) l)`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [FLAT_SNOC, MAP_SNOC, MAP, FLAT, FOLDL_SNOC]
   THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
   THEN IMP_RES_TAC FCOMM_FOLDL_APPEND
   THEN ASM_REWRITE_TAC []);

val MAP_FLAT = Q.store_thm ("MAP_FLAT",
   `!f l. MAP f (FLAT l) = FLAT (MAP  (MAP f) l)`,
   BasicProvers.Induct_on `l` THEN ASM_REWRITE_TAC [FLAT, MAP, MAP_APPEND]);

val FILTER_FLAT = Q.store_thm ("FILTER_FLAT",
   `!P l. FILTER P (FLAT l) = FLAT (MAP (FILTER P) l)`,
   BasicProvers.Induct_on `l`
   THEN ASM_REWRITE_TAC [FLAT, MAP, FILTER, FILTER_APPEND]);

val EXISTS_DISJ = Q.store_thm ("EXISTS_DISJ",
   `!P Q l. EXISTS (\x. P x \/ Q x) l = EXISTS P l \/ EXISTS Q l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [EXISTS_DEF]
   THEN metisLib.METIS_TAC []);

val MEM_FOLDR = Q.store_thm ("MEM_FOLDR",
   `!(y:'a) l. MEM y l = FOLDR (\x l'. (y = x) \/ l') F l`,
   REWRITE_TAC [MEM_EXISTS, EXISTS_FOLDR, FOLDR_MAP]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val MEM_FOLDL = Q.store_thm ("MEM_FOLDL",
   `!y l. MEM y l = FOLDL (\l' x. l' \/ (y = x)) F l`,
   REWRITE_TAC [MEM_EXISTS, EXISTS_FOLDL, FOLDL_MAP]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val NULL_FOLDR = Q.store_thm ("NULL_FOLDR",
   `!l. NULL l = FOLDR (\x l'. F) T l`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [NULL_DEF, FOLDR]);

val NULL_FOLDL = Q.store_thm ("NULL_FOLDL",
   `!l. NULL l = FOLDL (\x l'. F) T l`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC [NULL_DEF, FOLDL_SNOC, NULL_EQ, FOLDL,
                     GSYM NOT_NIL_SNOC]);

val MAP_REVERSE = Q.store_thm ("MAP_REVERSE",
   `!f l. MAP f (REVERSE l) = REVERSE (MAP f l)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [REVERSE, MAP, MAP_SNOC]);

val SEG_LENGTH_ID = Q.store_thm ("SEG_LENGTH_ID",
   `!l. SEG (LENGTH l) 0 l = l`,
   BasicProvers.Induct THEN ASM_REWRITE_TAC [LENGTH, SEG]);

val SEG_SUC_CONS = Q.store_thm ("SEG_SUC_CONS",
   `!m n l x. SEG m (SUC n) (CONS x l) = SEG m n l`,
   BasicProvers.Induct THEN REWRITE_TAC [SEG]);

val SEG_0_SNOC = Q.store_thm ("SEG_0_SNOC",
   `!m l x. m <= LENGTH l ==> (SEG m 0 (SNOC x l) = SEG m 0 l)`,
   INDUCT_TAC
   THEN1 REWRITE_TAC [SEG]
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH]
   THEN1 REWRITE_TAC [LESS_OR_EQ, numTheory.NOT_SUC, NOT_LESS_0]
   THEN REWRITE_TAC [SNOC, SEG, LESS_EQ_MONO]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val BUTLASTN_SEG = Q.store_thm ("BUTLASTN_SEG",
   `!n l. n <= LENGTH l ==> (BUTLASTN n l = SEG (LENGTH l - n) 0 l)`,
   INDUCT_TAC
   THEN REWRITE_TAC [BUTLASTN, SUB_0, SEG_LENGTH_ID]
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, BUTLASTN]
   THEN1 REWRITE_TAC [LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LESS_EQ_MONO, SUB_MONO_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_THEN SUBST1_TAC
   THEN MATCH_MP_TAC (GSYM SEG_0_SNOC)
   THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val LASTN_CONS = Q.store_thm ("LASTN_CONS",
   `!n l. n <= LENGTH l ==> !x. LASTN n (CONS x l) = LASTN n l`,
   BasicProvers.Induct
   THEN REWRITE_TAC [LASTN]
   THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [LENGTH, LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LENGTH_SNOC, GSYM (CONJUNCT2 SNOC), LESS_EQ_MONO]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC [LASTN]);

val LENGTH_LASTN = Q.store_thm ("LENGTH_LASTN",
   `!n l. n <= LENGTH l ==> (LENGTH (LASTN n l) = n)`,
   INDUCT_TAC
   THEN REWRITE_TAC [LASTN, LENGTH]
   THEN SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [LENGTH, LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LENGTH_SNOC, LASTN, LESS_EQ_MONO]
   THEN DISCH_TAC
   THEN RES_THEN SUBST1_TAC
   THEN REFL_TAC);

val LASTN_LENGTH_ID = Q.store_thm ("LASTN_LENGTH_ID",
   `!l. LASTN (LENGTH l) l = l`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, LASTN]
   THEN GEN_TAC
   THEN POP_ASSUM SUBST1_TAC
   THEN REFL_TAC);

val LASTN_LASTN = Q.store_thm ("LASTN_LASTN",
   `!l n m. m <= LENGTH l ==> n <= m ==> (LASTN n (LASTN m l) = LASTN n l)`,
   SNOC_INDUCT_TAC
   THENL [
      REWRITE_TAC [LENGTH, LESS_OR_EQ, NOT_LESS_0]
      THEN REPEAT GEN_TAC
      THEN DISCH_THEN SUBST1_TAC
      THEN REWRITE_TAC [NOT_LESS_0, LASTN],
      GEN_TAC
      THEN REPEAT INDUCT_TAC
      THEN REWRITE_TAC [LENGTH_SNOC, LASTN, LESS_EQ_MONO, ZERO_LESS_EQ]
      THEN1 REWRITE_TAC [LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
      THEN REPEAT DISCH_TAC
      THEN RES_TAC
      THEN ASM_REWRITE_TAC []]);

val TAKE_SNOC = Q.store_thm ("TAKE_SNOC",
   `!n l. n <= LENGTH l ==> !x. TAKE n (SNOC x l) = TAKE n l`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [TAKE, LENGTH]
   THEN1 REWRITE_TAC [LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LESS_EQ_MONO, SNOC, TAKE]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val BUTLASTN_LENGTH_NIL = Q.store_thm ("BUTLASTN_LENGTH_NIL",
   `!l. BUTLASTN (LENGTH l) l = []`,
   SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, LENGTH_SNOC, BUTLASTN]);

val BUTLASTN_SUC_FRONT = Q.store_thm ("BUTLASTN_SUC_FRONT",
   `!n l. n < LENGTH l ==> (BUTLASTN (SUC n) l =  BUTLASTN n (FRONT l))`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_LESS_0, BUTLASTN, FRONT_SNOC]);

val BUTLASTN_FRONT = Q.store_thm ("BUTLASTN_FRONT",
   `!n l. n < LENGTH l ==> (BUTLASTN n (FRONT l) = FRONT (BUTLASTN n l))`,
   INDUCT_TAC
   THEN REWRITE_TAC [BUTLASTN]
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC
          [LENGTH, LENGTH_SNOC, NOT_LESS_0, LESS_MONO_EQ, BUTLASTN, FRONT_SNOC]
   THEN DISCH_TAC
   THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SUC_FRONT
   THEN RES_TAC);

val LENGTH_BUTLASTN = Q.store_thm ("LENGTH_BUTLASTN",
   `!n l. n <= LENGTH l ==> (LENGTH (BUTLASTN n l) = LENGTH l - n)`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [BUTLASTN, SUB_0]
   THEN1 REWRITE_TAC [LENGTH, LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO, SUB_MONO_EQ]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ADD_SUC_lem = numLib.DECIDE ``!n m. m + SUC n = SUC m + n``

val BUTLASTN_BUTLASTN = Q.store_thm ("BUTLASTN_BUTLASTN",
   `!m n l.
       n + m <= LENGTH l ==>
       (BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l)`,
   REPEAT INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, ADD, ADD_0, BUTLASTN]
   THEN1 REWRITE_TAC [LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO, ADD_SUC_lem]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val APPEND_BUTLASTN_LASTN = Q.store_thm ("APPEND_BUTLASTN_LASTN",
   `!n l. n <= LENGTH l ==> (APPEND (BUTLASTN n l) (LASTN n l) = l)`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [BUTLASTN, LASTN, APPEND, APPEND_NIL]
   THEN1 REWRITE_TAC [LENGTH, LESS_OR_EQ, NOT_LESS_0, numTheory.NOT_SUC]
   THEN REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO, APPEND_SNOC]
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN RES_THEN SUBST1_TAC
   THEN REFL_TAC);

val APPEND_TAKE_LASTN = Q.store_thm ("APPEND_TAKE_LASTN",
   `!m n l. (m + n = LENGTH l) ==> (APPEND (TAKE n l) (LASTN m l) = l)`,
    REPEAT INDUCT_TAC
    THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, ADD, ADD_0, TAKE, LASTN,
                      APPEND, APPEND_NIL, SUC_NOT, numTheory.NOT_SUC]
    THENL [
        GEN_TAC
        THEN DISCH_THEN SUBST1_TAC
        THEN SUBST1_TAC (SYM (SPEC_ALL LENGTH_SNOC))
        THEN MATCH_ACCEPT_TAC TAKE_LENGTH_ID,
        PURE_ONCE_REWRITE_TAC [INV_SUC_EQ]
        THEN GEN_TAC
        THEN DISCH_THEN SUBST1_TAC
        THEN REWRITE_TAC [LASTN_LENGTH_ID],
        PURE_ONCE_REWRITE_TAC [INV_SUC_EQ, ADD_SUC_lem, APPEND_SNOC]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC (numLib.DECIDE ``!m n p. (n + m = p) ==> m <= p``)
        THEN IMP_RES_TAC TAKE_SNOC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC []]);

val BUTLASTN_APPEND2 = Q.store_thm ("BUTLASTN_APPEND2",
   `!n l1 l2.
      n <= LENGTH l2 ==>
      (BUTLASTN n (APPEND l1 l2) = APPEND l1 (BUTLASTN n l2))`,
   INDUCT_TAC
   THEN GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, BUTLASTN, NOT_SUC_LESS_EQ_0, APPEND_SNOC]
   THEN ASM_REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO]);

(* |- !l2 l1. BUTLASTN (LENGTH l2) (APPEND l1 l2) = l1 *)
val BUTLASTN_LENGTH_APPEND = save_thm ("BUTLASTN_LENGTH_APPEND",
   GENL[``l2:'a list``,``l1:'a list``]
     (REWRITE_RULE [LESS_EQ_REFL, BUTLASTN_LENGTH_NIL, APPEND_NIL]
     (SPECL [``LENGTH (l2:'a list)``,``l1:'a list``,``l2:'a list``]
            BUTLASTN_APPEND2)));

val LASTN_LENGTH_APPEND = Q.store_thm ("LASTN_LENGTH_APPEND",
   `!l2 l1. LASTN (LENGTH l2) (APPEND l1 l2) = l2`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, APPEND, APPEND_SNOC, LASTN]
   THEN ASM_REWRITE_TAC [FRONT_SNOC, LAST_SNOC, SNOC_APPEND]);

val BUTLASTN_CONS = Q.store_thm ("BUTLASTN_CONS",
   `!n l. n <= LENGTH l ==> !x. BUTLASTN n (CONS x l) = CONS x (BUTLASTN n l)`,
   BasicProvers.Induct
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_SUC_LESS_EQ_0, BUTLASTN, GSYM (CONJUNCT2 SNOC)]
   THEN ASM_REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO]);

(* |- !l x. BUTLASTN (LENGTH l) (CONS x l) = [x] *)
val BUTLASTN_LENGTH_CONS = save_thm ("BUTLASTN_LENGTH_CONS",
   let
      val thm1 = SPECL [``LENGTH (l:'a list)``,``l:'a list``] BUTLASTN_CONS
   in
      GEN_ALL (REWRITE_RULE [LESS_EQ_REFL, BUTLASTN_LENGTH_NIL] thm1)
   end);

val LAST_LASTN_LAST = Q.store_thm ("LAST_LASTN_LAST",
   `!n l. n <= LENGTH l ==> 0 < n ==> (LAST (LASTN n l) = LAST l)`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_LESS_0, NOT_SUC_LESS_EQ_0]
   THEN REWRITE_TAC [LASTN, LAST_SNOC]);

val BUTLASTN_LASTN_NIL = Q.store_thm ("BUTLASTN_LASTN_NIL",
   `!n l. n <= LENGTH l ==> (BUTLASTN n (LASTN n l) = [])`,
   REPEAT STRIP_TAC
   THEN IMP_RES_THEN (fn t => SUBST_OCCS_TAC [([1], SYM t)]) LENGTH_LASTN
   THEN MATCH_ACCEPT_TAC BUTLASTN_LENGTH_NIL);

val LASTN_BUTLASTN = Q.store_thm ("LASTN_BUTLASTN",
   `!n m l.
      n + m <= LENGTH l ==>
      (LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l))`,
   REPEAT INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_SUC_LESS_EQ_0, ADD, ADD_0, LASTN, BUTLASTN]
   THEN REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO]
   THENL [
       DISCH_TAC THEN CONV_TAC SYM_CONV THEN IMP_RES_TAC BUTLASTN_LASTN_NIL,
       PURE_ONCE_REWRITE_TAC [numLib.DECIDE ``!n m. m + SUC n = SUC m + n``]
       THEN DISCH_TAC
       THEN RES_TAC]);

val BUTLASTN_LASTN = Q.store_thm ("BUTLASTN_LASTN",
   `!m n l.
       m <= n /\ n <= LENGTH l ==>
       (BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l))`,
   REPEAT INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC
          [LENGTH, NOT_LESS_0, NOT_SUC_LESS_EQ_0, SUB_0, BUTLASTN, LASTN]
   THEN ASM_REWRITE_TAC [LENGTH_SNOC, LESS_EQ_MONO, SUB_MONO_EQ]);

val LASTN_1 = Q.store_thm ("LASTN_1",
   `!l. ~(l = []) ==> (LASTN 1 l = [LAST l])`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC []
   THEN REPEAT STRIP_TAC
   THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
   THEN REWRITE_TAC [LASTN, APPEND_NIL, SNOC, LAST_SNOC]);

val BUTLASTN_1 = Q.store_thm ("BUTLASTN_1",
   `!l. ~(l = []) ==> (BUTLASTN 1 l = FRONT l)`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC []
   THEN REPEAT STRIP_TAC
   THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
   THEN REWRITE_TAC [FRONT_SNOC, BUTLASTN]);

val BUTLASTN_APPEND1 = Q.store_thm ("BUTLASTN_APPEND1",
   `!l2 n.
      LENGTH l2 <= n ==>
      !l1. BUTLASTN n (APPEND l1 l2) = BUTLASTN (n - (LENGTH l2)) l1`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC
           [LENGTH, LENGTH_SNOC, APPEND, APPEND_SNOC, APPEND_NIL, SUB_0]
   THEN GEN_TAC
   THEN INDUCT_TAC
   THEN REWRITE_TAC [NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, BUTLASTN, SUB_MONO_EQ]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val LASTN_APPEND2 = Q.store_thm ("LASTN_APPEND2",
   `!n l2. n <= LENGTH l2 ==> !l1. LASTN n (APPEND l1 l2) = LASTN n l2`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, LASTN, NOT_SUC_LESS_EQ_0]
   THEN REWRITE_TAC [LESS_EQ_MONO, LASTN, APPEND_SNOC]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val LASTN_APPEND1 = Q.store_thm ("LASTN_APPEND1",
   `!l2 n.
       LENGTH l2 <= n ==>
       !l1. LASTN n (APPEND l1 l2) = APPEND (LASTN (n - (LENGTH l2)) l1) l2`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC
           [LENGTH, LENGTH_SNOC, APPEND, APPEND_SNOC, APPEND_NIL, LASTN, SUB_0]
   THEN GEN_TAC
   THEN INDUCT_TAC
   THEN REWRITE_TAC [NOT_SUC_LESS_EQ_0, LASTN, LESS_EQ_MONO, SUB_MONO_EQ]
   THEN DISCH_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val LASTN_MAP = Q.store_thm ("LASTN_MAP",
   `!n l. n <= LENGTH l ==> !f. LASTN n (MAP f l) = MAP f (LASTN n l)`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LASTN, MAP, NOT_SUC_LESS_EQ_0]
   THEN REWRITE_TAC [LENGTH_SNOC, LASTN, MAP_SNOC, LESS_EQ_MONO]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val BUTLASTN_MAP = Q.store_thm ("BUTLASTN_MAP",
   `!n l. n <= LENGTH l ==> !f. BUTLASTN n (MAP f l) = MAP f (BUTLASTN n l)`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, BUTLASTN, MAP, NOT_SUC_LESS_EQ_0]
   THEN REWRITE_TAC [LENGTH_SNOC, BUTLASTN, MAP_SNOC, LESS_EQ_MONO]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val TAKE_TAKE_T = Q.store_thm ("TAKE_TAKE_T",
   `!m l n. n <= m ==> (TAKE n (TAKE m l) = TAKE n l)`,
  Induct THEN1 SIMP_TAC list_ss [TAKE, TAKE_def]
  THEN Cases THEN1 SIMP_TAC list_ss [TAKE, TAKE_def]
  THEN Cases THEN1 SIMP_TAC list_ss [TAKE, TAKE_def]
  THEN ASM_SIMP_TAC list_ss [TAKE, TAKE_def]) ;

val TAKE_TAKE = Q.store_thm ("TAKE_TAKE",
   `!m l. m <= LENGTH l ==> !n. n <= m ==> (TAKE n (TAKE m l) = TAKE n l)`,
   SIMP_TAC bool_ss [TAKE_TAKE_T]) ;

val DROP_LENGTH_NIL = Q.store_thm ("DROP_LENGTH_NIL",
   `!l. DROP (LENGTH l) l = []`,
   BasicProvers.Induct THEN ASM_REWRITE_TAC [LENGTH, DROP]);

val DROP_APPEND = Q.store_thm ("DROP_APPEND",
   `!n l1 l2. DROP n (APPEND l1 l2) = DROP n l1 ++ DROP (n - LENGTH l1) l2`,
   Induct THEN1 SIMP_TAC list_ss [DROP, DROP_def]
   THEN Cases THEN1 SIMP_TAC list_ss [DROP, DROP_def]
   THEN ASM_SIMP_TAC list_ss [DROP, DROP_def]) ;

val DROP_APPEND1 = Q.store_thm ("DROP_APPEND1",
   `!n l1.
       n <= LENGTH l1 ==> !l2. DROP n (APPEND l1 l2) = APPEND (DROP n l1) l2`,
   NTAC 2 BasicProvers.Induct
   THEN REWRITE_TAC [LENGTH, DROP, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]
   THEN GEN_TAC THEN ASM_REWRITE_TAC [APPEND, DROP]);

val DROP_APPEND2 = Q.store_thm ("DROP_APPEND2",
   `!l1 n.
       LENGTH l1 <= n ==> !l2. DROP n (APPEND l1 l2) = DROP (n - LENGTH l1) l2`,
   BasicProvers.Induct
   THEN REWRITE_TAC [LENGTH, APPEND, DROP, SUB_0]
   THEN GEN_TAC
   THEN BasicProvers.Induct
   THEN ASM_REWRITE_TAC [NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, SUB_MONO_EQ, DROP])

val DROP_DROP_T = Q.store_thm ("DROP_DROP_T",
   `!n m l. DROP n (DROP m l) = DROP (n + m) l`,
   SIMP_TAC list_ss [DROP_FUNPOW_TL, GSYM FUNPOW_ADD]) ;

val DROP_DROP = Q.store_thm ("DROP_DROP",
   `!n m l. n + m <= LENGTH l ==> (DROP n (DROP m l) = DROP (n + m) l)`,
   SIMP_TAC list_ss [DROP_DROP_T]) ;

val LASTN_SEG = Q.store_thm ("LASTN_SEG",
   `!n l. n <= LENGTH l ==> (LASTN n l = SEG n (LENGTH l - n) l)`,
    BasicProvers.Induct
    THEN REWRITE_TAC [LASTN, SUB_0, SEG]
    THEN BasicProvers.Induct
    THEN REWRITE_TAC [LENGTH, LASTN, NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC [LESS_EQ_MONO, SUB_MONO_EQ]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN IMP_RES_TAC LESS_OR_EQ
    THENL [
        IMP_RES_THEN SUBST1_TAC
           (numLib.DECIDE ``!k m. m < k ==> (k - m = SUC (k - SUC m))``)
        THEN PURE_ONCE_REWRITE_TAC [SEG]
        THEN IMP_RES_TAC LESS_EQ
        THEN RES_THEN (SUBST1_TAC o SYM)
        THEN MATCH_MP_TAC LASTN_CONS
        THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM SUBST1_TAC
        THEN REWRITE_TAC [SUB_EQUAL_0]
        (* **list_Axiom** variable dependancy *)
        THEN SUBST1_TAC (SYM (Q.SPECL [`h`, `l`] (CONJUNCT2 LENGTH)))
        THEN REWRITE_TAC [SEG_LENGTH_ID, LASTN_LENGTH_ID]]);

val TAKE_SEG = Q.store_thm ("TAKE_SEG",
   `!n l. n <= LENGTH l ==> (TAKE n l = SEG n 0 l)`,
   NTAC 2 BasicProvers.Induct
   THEN REWRITE_TAC [LENGTH, TAKE, SEG, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val DROP_SEG = Q.store_thm ("DROP_SEG",
   `!n l. n <= LENGTH l ==> (DROP n l = SEG (LENGTH l - n) n l)`,
   NTAC 2 BasicProvers.Induct
   THEN REWRITE_TAC [LENGTH, DROP, SEG, NOT_SUC_LESS_EQ_0,
                     LESS_EQ_MONO, SUB_0, SEG_LENGTH_ID]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC [SUB_MONO_EQ, SEG_SUC_CONS]);

val DROP_SNOC = Q.store_thm ("DROP_SNOC",
   `!n l. n <= LENGTH l ==> !x. DROP n (SNOC x l) = SNOC x (DROP n l)`,
   NTAC 2 BasicProvers.Induct
   THEN REWRITE_TAC [LENGTH, DROP, SNOC, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val APPEND_BUTLASTN_DROP = Q.store_thm ("APPEND_BUTLASTN_DROP",
   `!m n l. (m + n = LENGTH l) ==> (APPEND (BUTLASTN m l) (DROP n l) = l)`,
   REPEAT BasicProvers.Induct
   THEN REWRITE_TAC
          [LENGTH, APPEND, ADD, ADD_0, numTheory.NOT_SUC, SUC_NOT,
           SNOC, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, INV_SUC_EQ]
   THENL [
        REWRITE_TAC [BUTLASTN, DROP, APPEND],
        GEN_TAC
        THEN DISCH_THEN SUBST1_TAC
        (* **list_Axiom** variable dependancy *)
        THEN SUBST1_TAC (SYM (Q.SPECL [`h`, `l`] (CONJUNCT2 LENGTH)))
        THEN REWRITE_TAC [DROP_LENGTH_NIL, BUTLASTN, APPEND_NIL],
        GEN_TAC
        THEN DISCH_THEN SUBST1_TAC
        (* **list_Axiom** variable dependancy *)
        THEN SUBST1_TAC (SYM (Q.SPECL [`h`, `l`] (CONJUNCT2 LENGTH)))
        THEN REWRITE_TAC [BUTLASTN_LENGTH_NIL, DROP, APPEND],
        GEN_TAC
        THEN DISCH_TAC
        THEN PURE_ONCE_REWRITE_TAC [DROP]
        THEN RULE_ASSUM_TAC (REWRITE_RULE [ADD_SUC_lem])
        THEN IMP_RES_TAC (numLib.DECIDE ``!m n p. (m + n = p) ==> (m <= p)``)
        THEN IMP_RES_TAC BUTLASTN_CONS
        THEN ASM_REWRITE_TAC [APPEND, CONS_11]
        THEN RES_TAC]);

val SEG_SEG = Q.store_thm ("SEG_SEG",
   `!n1 m1 n2 m2 l.
       n1 + m1 <= LENGTH l /\ n2 + m2 <= n1 ==>
       (SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l)`,
   REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, SEG, NOT_LESS_0, NOT_SUC_LESS_EQ_0, ADD, ADD_0]
   THENL [
        (* 1 *)
        GEN_TAC THEN REWRITE_TAC [LESS_EQ_MONO, CONS_11]
        THEN STRIP_TAC THEN SUBST_OCCS_TAC [([3], SYM(SPEC``0``ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [ADD_0],
        (* 2 *)
        REWRITE_TAC [LESS_EQ_MONO, ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC [([2], SYM(SPEC``m2:num``(CONJUNCT1 ADD)))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [ADD_0],
        (* 3 *)
        REWRITE_TAC [LESS_EQ_MONO, ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC [([2], SYM(SPEC``m1:num``ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC [LESS_EQ_MONO, ADD_0],
        (* 4 *)
        PURE_ONCE_REWRITE_TAC [LESS_EQ_MONO] THEN STRIP_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [
            PURE_ONCE_REWRITE_TAC [GSYM ADD_SUC_lem]
            THEN FIRST_ASSUM ACCEPT_TAC,
            ASM_REWRITE_TAC [ADD, LESS_EQ_MONO]]]);

val SEG_APPEND1 = Q.store_thm ("SEG_APPEND1",
   `!n m l1. n + m <= LENGTH l1 ==> !l2. SEG n m (APPEND l1 l2) = SEG n m l1`,
   REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, SEG, NOT_LESS_0, NOT_SUC_LESS_EQ_0, ADD, ADD_0]
   THEN GEN_TAC
   THEN REWRITE_TAC [LESS_EQ_MONO, APPEND, SEG, CONS_11]
   THENL [
       DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC
       THEN ASM_REWRITE_TAC [ADD_0],
       PURE_ONCE_REWRITE_TAC [ADD_SUC_lem]
       THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SEG_APPEND2 = Q.store_thm ("SEG_APPEND2",
   `!l1 m n l2.
      LENGTH l1 <= m /\ n <= LENGTH l2 ==>
      (SEG n m (APPEND l1 l2) = SEG n (m - (LENGTH l1)) l2)`,
   LIST_INDUCT_TAC
   THEN REPEAT (FILTER_GEN_TAC ``m:num``)
   THEN REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, SEG, NOT_LESS_0, NOT_SUC_LESS_EQ_0, ADD, ADD_0]
   THEN REPEAT GEN_TAC
   THEN REWRITE_TAC [SUB_0, APPEND, SEG]
   THEN REWRITE_TAC [LESS_EQ_MONO, SUB_MONO_EQ]
   THEN STRIP_TAC
   THEN FIRST_ASSUM MATCH_MP_TAC
   THEN ASM_REWRITE_TAC [LENGTH, LESS_EQ_MONO]);

val SEG_TAKE_DROP = Q.store_thm ("SEG_TAKE_DROP",
   `!n m l. n + m <= LENGTH l ==> (SEG n m l = TAKE n (DROP m l))`,
   REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_SUC_LESS_EQ_0, ADD, ADD_0,
                     SEG, TAKE, DROP, LESS_EQ_MONO, CONS_11]
   THEN1 MATCH_ACCEPT_TAC (GSYM TAKE_SEG)
   THEN PURE_ONCE_REWRITE_TAC [ADD_SUC_lem]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val SEG_APPEND = Q.store_thm ("SEG_APPEND",
   `!m l1 n l2.
      m < LENGTH l1 /\ LENGTH l1 <= n + m /\ n + m <= LENGTH l1 + LENGTH l2 ==>
      (SEG n m (APPEND l1 l2) =
       APPEND (SEG (LENGTH l1 - m) m l1) (SEG (n + m - LENGTH l1) 0 l2))`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REPEAT (FILTER_GEN_TAC ``n:num``)
   THEN INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REPEAT GEN_TAC
   THEN REWRITE_TAC
          [LENGTH, SEG, NOT_LESS_0, NOT_SUC_LESS_EQ_0, ADD, ADD_0, SUB_0]
   THEN REWRITE_TAC
          [LESS_EQ_MONO, SUB_0, SUB_MONO_EQ, APPEND, SEG, NOT_SUC_LESS_EQ_0,
           CONS_11]
   THEN RULE_ASSUM_TAC (REWRITE_RULE [ADD_0, SUB_0])
   THENL [
       DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
       THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
       THEN REWRITE_TAC [SEG, APPEND_NIL, SUB_EQUAL_0],
       STRIP_TAC THEN DISJ_CASES_TAC (SPEC ``LENGTH (l1:'a list)``LESS_0_CASES)
       THENL [
           POP_ASSUM (ASSUME_TAC o SYM) THEN IMP_RES_TAC LENGTH_NIL
           THEN ASM_REWRITE_TAC [APPEND, SEG, SUB_0],
           FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [LENGTH]],
       DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
       THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
       THEN REWRITE_TAC [SEG, APPEND_NIL, SUB_EQUAL_0],
       REWRITE_TAC [LESS_MONO_EQ, GSYM NOT_LESS] THEN STRIP_TAC THEN RES_TAC,
       DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
       THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
       THEN REWRITE_TAC [SEG, APPEND_NIL, SUB_EQUAL_0]
       THEN REWRITE_TAC [ADD_SUC_lem, ADD_SUB, SEG],
       REWRITE_TAC [LESS_MONO_EQ, SEG_SUC_CONS] THEN STRIP_TAC
       THEN PURE_ONCE_REWRITE_TAC [ADD_SUC_lem]
       THEN FIRST_ASSUM MATCH_MP_TAC
       THEN ASM_REWRITE_TAC [GSYM ADD_SUC_lem, LENGTH]]);

val SEG_LENGTH_SNOC = Q.store_thm ("SEG_LENGTH_SNOC",
   `!l x. SEG 1 (LENGTH l) (SNOC x l) = [x]`,
   CONV_TAC (ONCE_DEPTH_CONV num_CONV)
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [LENGTH, SNOC, SEG]);

val SEG_SNOC = Q.store_thm ("SEG_SNOC",
   `!n m l. n + m <= LENGTH l ==> !x. SEG n m (SNOC x l) = SEG n m l`,
   REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_SUC_LESS_EQ_0, ADD, ADD_0, SNOC, SEG]
   THENL [
      REWRITE_TAC [CONS_11, LESS_EQ_MONO]
      THEN REPEAT STRIP_TAC
      THEN FIRST_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC [ADD_0],
      REWRITE_TAC [LESS_EQ_MONO, ADD_SUC_lem]
      THEN DISCH_TAC
      THEN FIRST_ASSUM MATCH_MP_TAC
      THEN FIRST_ASSUM ACCEPT_TAC]);

val ELL_SEG = Q.store_thm ("ELL_SEG",
   `!n l. n < LENGTH l ==> (ELL n l = HD (SEG 1 (PRE (LENGTH l - n)) l))`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, NOT_LESS_0]
   THEN1 REWRITE_TAC [PRE, SUB_0, ELL, LAST_SNOC, SEG_LENGTH_SNOC, HD]
   THEN REWRITE_TAC [LESS_MONO_EQ, ELL, FRONT_SNOC, SUB_MONO_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_THEN SUBST1_TAC
   THEN CONV_TAC SYM_CONV
   THEN AP_TERM_TAC
   THEN MATCH_MP_TAC SEG_SNOC
   THEN PURE_ONCE_REWRITE_TAC [ADD_SYM]
   THEN PURE_ONCE_REWRITE_TAC [GSYM ADD1]
   THEN IMP_RES_TAC SUB_LESS_0
   THEN IMP_RES_THEN SUBST1_TAC SUC_PRE
   THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val SNOC_FOLDR = Q.store_thm ("SNOC_FOLDR",
   `!x l. SNOC x l = FOLDR CONS [x] l `,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FOLDR, SNOC]);

val MEM_FOLDR_MAP = Q.store_thm ("MEM_FOLDR_MAP",
   `!x l. MEM x l = FOLDR $\/ F (MAP ($= x) l)`,
   REWRITE_TAC [MEM_FOLDR, FOLDR_MAP]);

val MEM_FOLDL_MAP = Q.store_thm ("MEM_FOLDL_MAP",
   `!x l. MEM x l = FOLDL $\/ F (MAP ($= x) l)`,
   REWRITE_TAC [MEM_FOLDL, FOLDL_MAP]);

val FILTER_FILTER = Q.store_thm ("FILTER_FILTER",
   `!P Q l. FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l`,
   BasicProvers.Induct_on `l`
   THEN REWRITE_TAC [FILTER]
   THEN BETA_TAC
   THEN REPEAT GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC [FILTER]);

val FCOMM_FOLDR_FLAT = Q.store_thm ("FCOMM_FOLDR_FLAT",
   `!g f.
       FCOMM g f ==>
       !e. LEFT_ID g e ==>
           !l. FOLDR f e (FLAT l) = FOLDR g e (MAP (FOLDR f e) l)`,
   GEN_TAC
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [FLAT, MAP, FOLDR]
   THEN IMP_RES_TAC FCOMM_FOLDR_APPEND
   THEN ASM_REWRITE_TAC []);

val FCOMM_FOLDL_FLAT = Q.store_thm ("FCOMM_FOLDL_FLAT",
   `!f g. FCOMM f g ==>
       !e. RIGHT_ID g e ==>
           !l. FOLDL f e (FLAT l) = FOLDL g e (MAP (FOLDL f e) l)`,
   GEN_TAC
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [FLAT_SNOC, MAP_SNOC, MAP, FLAT, FOLDL_SNOC, FOLDL]
   THEN IMP_RES_TAC FCOMM_FOLDL_APPEND
   THEN ASM_REWRITE_TAC []);

val FOLDR1 = Q.prove(
   `!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. (FOLDR f (f x e) l = f x (FOLDR f e l)))`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [REVERSE, FOLDR]
   THEN ONCE_REWRITE_TAC
           [ASSUME ``!a b c. (f:'a->'a->'a) a (f b c) = f b (f a c)``]
   THEN REWRITE_TAC
           [ASSUME ``FOLDR (f:'a->'a->'a)(f x e) l = f x (FOLDR f e l)``]);

val FOLDL1 = Q.prove(
   `!(f:'a->'a->'a).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. (FOLDL f (f e x) l = f (FOLDL f e l) x))`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [REVERSE, FOLDL, FOLDL_SNOC]
   THEN ONCE_REWRITE_TAC
           [ASSUME ``!a b c. (f:'a->'a->'a) (f a b) c = f (f a c) b``]
   THEN REWRITE_TAC
           [ASSUME``FOLDL(f:'a->'a->'a)(f e x) l = f (FOLDL f e l) x``]);

val FOLDR_REVERSE2 = Q.prove(
   `!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. FOLDR f e (REVERSE l) = FOLDR f e l)`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [REVERSE, FOLDR, FOLDR_SNOC]
   THEN IMP_RES_TAC FOLDR1
   THEN ASM_REWRITE_TAC []);

val FOLDR_MAP_REVERSE = Q.store_thm ("FOLDR_MAP_REVERSE",
   `!f:'a -> 'a -> 'a.
       (!a b c. f a (f b c) = f b (f a c)) ==>
       !e g l. FOLDR f e (MAP g (REVERSE l)) = FOLDR f e (MAP g l)`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [REVERSE, FOLDR, FOLDR_SNOC, MAP, MAP_SNOC]
   THEN IMP_RES_TAC FOLDR1
   THEN ASM_REWRITE_TAC []);

val FOLDR_FILTER_REVERSE = Q.store_thm ("FOLDR_FILTER_REVERSE",
   `!f:'a -> 'a -> 'a.
       (!a b c. f a (f b c) = f b (f a c)) ==>
       !e P l. FOLDR f e (FILTER P (REVERSE l)) = FOLDR f e (FILTER P l)`,
   GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [REVERSE, FOLDR, FOLDR_SNOC, FILTER, FILTER_SNOC]
   THEN IMP_RES_TAC FOLDR1
   THEN GEN_TAC
   THEN COND_CASES_TAC
   THENL [
        ASM_REWRITE_TAC [FOLDR, FOLDR_SNOC, FILTER, FILTER_SNOC]
        THEN ASM_REWRITE_TAC [GSYM FILTER_REVERSE],
        ASM_REWRITE_TAC [FOLDR, FOLDR_SNOC, FILTER, FILTER_SNOC]]);

val FOLDL_REVERSE2 = Q.prove(
   `!(f:'a->'a->'a).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l)`,
   GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [REVERSE, REVERSE_SNOC, FOLDL, FOLDL_SNOC]
   THEN IMP_RES_TAC FOLDL1 THEN ASM_REWRITE_TAC []);

val COMM_ASSOC_LEM1 = Q.prove(
   `!(f:'a->'a->'a). COMM f ==> (ASSOC f ==>
      (!a b c. f a (f b c) = f b (f a c)))`,
   REWRITE_TAC [ASSOC_DEF] THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC [] THEN SUBST1_TAC(SPECL [``a:'a``,``b:'a``]
      (REWRITE_RULE [COMM_DEF] (ASSUME ``COMM (f:'a->'a->'a)``)))
   THEN REWRITE_TAC []);

val COMM_ASSOC_LEM2 = Q.prove(
   `!(f:'a->'a->'a). COMM f ==> (ASSOC f ==>
      (!a b c. f (f a b) c = f (f a c) b))`,
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC
      [GSYM (REWRITE_RULE [ASSOC_DEF] (ASSUME ``ASSOC (f:'a->'a->'a)``))]
   THEN SUBST1_TAC(SPECL [``b:'a``,``c:'a``]
      (REWRITE_RULE [COMM_DEF] (ASSUME ``COMM (f:'a->'a->'a)``)))
   THEN REWRITE_TAC []);

val COMM_ASSOC_FOLDR_REVERSE = Q.store_thm ("COMM_ASSOC_FOLDR_REVERSE",
   `!f:'a -> 'a -> 'a.
       COMM f ==> ASSOC f ==> !e l. FOLDR f e (REVERSE l) = FOLDR f e l`,
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC FOLDR_REVERSE2
   THEN REPEAT GEN_TAC
   THEN IMP_RES_TAC COMM_ASSOC_LEM1
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val COMM_ASSOC_FOLDL_REVERSE = Q.store_thm ("COMM_ASSOC_FOLDL_REVERSE",
   `!f:'a -> 'a -> 'a.
       COMM f ==> ASSOC f ==> !e l. FOLDL f e (REVERSE l) = FOLDL f e l`,
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC FOLDL_REVERSE2
   THEN IMP_RES_TAC COMM_ASSOC_LEM2
   THEN REPEAT GEN_TAC
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_LAST = Q.store_thm ("ELL_LAST",
   `!l. ~NULL l ==> (ELL 0 l = LAST l)`,
   SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [NULL]
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC [ELL]);

val ELL_0_SNOC = Q.store_thm ("ELL_0_SNOC",
   `!l x. ELL 0 (SNOC x l) = x`,
   REPEAT GEN_TAC THEN REWRITE_TAC [ELL, LAST_SNOC]);

val ELL_SNOC = Q.store_thm ("ELL_SNOC",
   `!n. 0 < n ==> !x l. ELL n (SNOC x l) = ELL (PRE n) l`,
   INDUCT_TAC THEN REWRITE_TAC [NOT_LESS_0, ELL, FRONT_SNOC, PRE, LESS_0]);

(* |- !n x l. ELL (SUC n) (SNOC x l) = ELL n l *)
val ELL_SUC_SNOC = save_thm ("ELL_SUC_SNOC",
   GEN_ALL (PURE_ONCE_REWRITE_RULE [PRE]
      (MP (SPEC ``SUC n`` ELL_SNOC) (SPEC_ALL LESS_0))));

val ELL_CONS = Q.store_thm ("ELL_CONS",
   `!n l. n < LENGTH l ==> !x. ELL n (CONS x l) = ELL n l`,
   let
      val SNOC_lem = GSYM (CONJUNCT2 SNOC)
   in
      INDUCT_TAC
      THEN SNOC_INDUCT_TAC
      THEN REWRITE_TAC [NOT_LESS_0, LENGTH]
      THENL [
        REPEAT STRIP_TAC THEN REWRITE_TAC [SNOC_lem, ELL_0_SNOC],
        GEN_TAC
        THEN REWRITE_TAC [LENGTH_SNOC, LESS_MONO_EQ, ELL_SUC_SNOC, SNOC_lem]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]
   end);

val ELL_LENGTH_CONS = Q.store_thm ("ELL_LENGTH_CONS",
   `!l x. ELL (LENGTH l) (CONS x l) = x`,
   SNOC_INDUCT_TAC
   THEN1 REWRITE_TAC [ELL, LENGTH, LAST_CONS]
   THEN REWRITE_TAC [ELL, LENGTH_SNOC, FRONT_SNOC, GSYM (CONJUNCT2 SNOC)]
   THEN POP_ASSUM ACCEPT_TAC);

val ELL_LENGTH_SNOC = Q.store_thm ("ELL_LENGTH_SNOC",
   `!l x. ELL (LENGTH l) (SNOC x l) = if NULL l then x else HD l`,
   LIST_INDUCT_TAC
   THEN1 REWRITE_TAC [ELL_0_SNOC, LENGTH, NULL]
   THEN REWRITE_TAC [ELL_SUC_SNOC, LENGTH, HD, NULL, ELL_LENGTH_CONS]);

val ELL_APPEND2 = Q.store_thm ("ELL_APPEND2",
   `!n l2. n < LENGTH l2 ==> !l1. ELL n (APPEND l1 l2) = ELL n l2`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_LESS_0]
   THEN REWRITE_TAC
          [APPEND_SNOC, ELL_0_SNOC, ELL_SUC_SNOC, LENGTH_SNOC, LESS_MONO_EQ]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_APPEND1 = Q.store_thm ("ELL_APPEND1",
   `!l2 n.
      LENGTH l2 <= n ==> !l1. ELL n (APPEND l1 l2) = ELL (n - LENGTH l2) l1`,
   SNOC_INDUCT_TAC
   THEN REPEAT (FILTER_GEN_TAC ``n:num``)
   THEN INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, LENGTH_SNOC, SUB_0, APPEND_NIL, NOT_SUC_LESS_EQ_0]
   THEN REWRITE_TAC [LESS_EQ_MONO, ELL_SUC_SNOC, SUB_MONO_EQ, APPEND_SNOC]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_PRE_LENGTH = Q.store_thm ("ELL_PRE_LENGTH",
   `!l. ~(l = []) ==> (ELL (PRE (LENGTH l)) l = HD l)`,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, PRE]
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC [ELL_LENGTH_CONS, HD]);

val EL_PRE_LENGTH = Q.store_thm ("EL_PRE_LENGTH",
   `!l. ~(l = []) ==> (EL (PRE (LENGTH l)) l = LAST l)`,
   SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH_SNOC, PRE, LAST_SNOC, EL_LENGTH_SNOC]);

val EL_ELL = Q.store_thm ("EL_ELL",
   `!n l. n < LENGTH l ==> (EL n l = ELL (PRE (LENGTH l - n)) l)`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_LESS_0]
   THEN1 REWRITE_TAC [PRE, EL, ELL_LENGTH_CONS, HD, SUB_0]
   THEN REWRITE_TAC [EL, TL, LESS_MONO_EQ, SUB_MONO_EQ]
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN MAP_EVERY IMP_RES_TAC
          [numLib.DECIDE ``!n m. m < n ==> PRE (n - m) < n``, ELL_CONS]
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []);

val EL_LENGTH_APPEND = Q.store_thm ("EL_LENGTH_APPEND",
   `!l2 l1. ~NULL l2 ==> (EL (LENGTH l1) (APPEND l1 l2) = HD l2)`,
  GEN_TAC
  THEN LIST_INDUCT_TAC
  THEN REWRITE_TAC [LENGTH, APPEND, EL, TL, NULL]
  THEN REPEAT STRIP_TAC
  THEN RES_TAC);

val ELL_EL = Q.store_thm ("ELL_EL",
   `!n l. n < LENGTH l ==> (ELL n l = EL (PRE((LENGTH l) - n)) l)`,
   INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC [LENGTH, NOT_LESS_0]
   THEN1 REWRITE_TAC
            [SUB_0, ELL_0_SNOC, LENGTH_SNOC, PRE, EL_LENGTH_SNOC]
   THEN REWRITE_TAC [LENGTH_SNOC, ELL_SUC_SNOC, SUB_MONO_EQ, LESS_MONO_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_THEN SUBST1_TAC
   THEN MATCH_MP_TAC (GSYM EL_SNOC)
   THEN IMP_RES_TAC (Q.prove (
           `!n m. n < m ==> ?k. (m - n = SUC k) /\ k < m`,
           REPEAT STRIP_TAC THEN Q.EXISTS_TAC `PRE (m - n)`
           THEN numLib.DECIDE_TAC))
   THEN ASM_REWRITE_TAC [PRE])

val ELL_MAP = Q.store_thm ("ELL_MAP",
   `!n l f. n < LENGTH l ==> (ELL n (MAP f l) = f (ELL n l))`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, NOT_LESS_0]
   THEN1 REWRITE_TAC [ELL_0_SNOC, MAP_SNOC]
   THEN REWRITE_TAC [LENGTH_SNOC, ELL_SUC_SNOC, MAP_SNOC, LESS_MONO_EQ]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val LENGTH_FRONT = Q.store_thm ("LENGTH_FRONT",
   `!l. ~(l = []) ==> (LENGTH (FRONT l) = PRE (LENGTH l))`,
   SNOC_INDUCT_TAC THEN REWRITE_TAC [LENGTH_SNOC, FRONT_SNOC, PRE]);

val DROP_LENGTH_APPEND = Q.store_thm ("DROP_LENGTH_APPEND",
   `!l1 l2. DROP (LENGTH l1) (APPEND l1 l2) = l2`,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, DROP, APPEND]);

val TAKE_APPEND = Q.store_thm ("TAKE_APPEND",
   `!n l1 l2. TAKE n (APPEND l1 l2) = TAKE n l1 ++ TAKE (n - LENGTH l1) l2`,
   Induct THEN1 SIMP_TAC list_ss [TAKE, TAKE_def]
   THEN Cases THEN1 SIMP_TAC list_ss [TAKE, TAKE_def]
   THEN ASM_SIMP_TAC list_ss [TAKE, TAKE_def]) ;

val TAKE_APPEND1 = Q.store_thm ("TAKE_APPEND1",
   `!n l1. n <= LENGTH l1 ==> !l2. TAKE n (APPEND l1 l2) = TAKE n l1`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC
          [LENGTH, NOT_SUC_LESS_EQ_0, TAKE, APPEND, CONS_11, LESS_EQ_MONO]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val TAKE_APPEND2 = Q.store_thm ("TAKE_APPEND2",
   `!l1 n.
       LENGTH l1 <= n ==>
       !l2. TAKE n (APPEND l1 l2) = APPEND l1 (TAKE (n - LENGTH l1) l2)`,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [LENGTH, APPEND, SUB_0]
   THEN GEN_TAC
   THEN INDUCT_TAC
   THEN REWRITE_TAC
          [NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, SUB_MONO_EQ, TAKE, CONS_11]
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val TAKE_LENGTH_APPEND = Q.store_thm ("TAKE_LENGTH_APPEND",
   `!l1 l2. TAKE (LENGTH l1) (APPEND l1 l2) = l1`,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, TAKE, APPEND]);

val REVERSE_FLAT = Q.store_thm ("REVERSE_FLAT",
   `!l. REVERSE (FLAT l) = FLAT (REVERSE (MAP REVERSE l))`,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [REVERSE, FLAT, MAP]
   THEN ASM_REWRITE_TAC [REVERSE_APPEND, FLAT_SNOC]);

val MAP_COND = Q.prove(
   `!(f:'a-> 'b) c l1 l2.
       (MAP f (if c then l1 else l2)) = (if c then (MAP f l1) else (MAP f l2))`,
   REPEAT GEN_TAC THEN BOOL_CASES_TAC ``c:bool`` THEN ASM_REWRITE_TAC []);

val MAP_FILTER = Q.store_thm ("MAP_FILTER",
   `!f P l. (!x. P (f x) = P x) ==> (MAP f (FILTER P l) = FILTER P (MAP f l))`,
   GEN_TAC
   THEN GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [MAP, FILTER]
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN ASM_REWRITE_TAC [MAP_COND, MAP]
   THEN RES_THEN SUBST1_TAC
   THEN REFL_TAC);

val FLAT_REVERSE = Q.store_thm ("FLAT_REVERSE",
   `!l. FLAT (REVERSE l) = REVERSE (FLAT (MAP REVERSE l))`,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [FLAT, REVERSE, MAP]
   THEN ASM_REWRITE_TAC [FLAT_SNOC, REVERSE_APPEND, REVERSE_REVERSE]);

val FLAT_FLAT = Q.store_thm ("FLAT_FLAT",
   `!l. FLAT (FLAT l) = FLAT (MAP FLAT l)`,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FLAT, FLAT_APPEND, MAP]);

val EXISTS_REVERSE = Q.store_thm ("EXISTS_REVERSE",
   `!P l. EXISTS P (REVERSE l) = EXISTS P l`,
   GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [EXISTS_DEF, REVERSE, EXISTS_SNOC]
   THEN GEN_TAC
   THEN MATCH_ACCEPT_TAC DISJ_SYM);

val EXISTS_SEG = Q.store_thm ("EXISTS_SEG",
   `!m k (l:'a list). (m + k) <= (LENGTH l) ==>
     !P. EXISTS P (SEG m k l) ==> EXISTS P l`,
   REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [EXISTS_DEF, SEG, LENGTH, ADD, ADD_0, NOT_SUC_LESS_EQ_0]
   THEN GEN_TAC
   THEN REWRITE_TAC [LESS_EQ_MONO]
   THENL [
      FIRST_ASSUM (ASSUME_TAC o (REWRITE_RULE [ADD_0]) o (SPEC``0``))
      THEN REPEAT STRIP_TAC
      THENL [
        DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        DISJ2_TAC THEN RES_TAC],
        SUBST1_TAC (numLib.DECIDE ``m + SUC k = SUC m + k``)
        THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC]);

val EXISTS_TAKE = Q.store_thm ("EXISTS_TAKE",
   `!l m P. EXISTS P (TAKE m l) ==> EXISTS P l`,
   Induct \\ rw [TAKE_def] \\ simp [] \\ first_x_assum drule \\ simp []);

val EXISTS_DROP = Q.store_thm ("EXISTS_DROP",
   `!l m P. EXISTS P (DROP m l) ==> EXISTS P l`,
   Induct \\ rw [DROP_def] \\ first_x_assum drule \\ simp []);

Theorem EXISTS_LASTN:
  !l m P. EXISTS P (LASTN m l) ==> EXISTS P l
Proof
  rw [LASTN_def, EXISTS_REVERSE] \\ drule EXISTS_TAKE \\ simp [EXISTS_REVERSE]
QED

Theorem EXISTS_BUTLASTN:
  !l m P. EXISTS P (BUTLASTN m l) ==> EXISTS P l
Proof
  rw[BUTLASTN_def, EXISTS_REVERSE] \\ drule EXISTS_DROP \\ simp[EXISTS_REVERSE]
QED

val MEM_SEG = Q.store_thm ("MEM_SEG",
   `!n m l. n + m <= LENGTH l ==> !x. MEM x (SEG n m l) ==> MEM x l`,
   REPEAT INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC
          [ADD, ADD_0, NOT_SUC_LESS_EQ_0, LENGTH, MEM, SEG, LESS_EQ_MONO]
   THEN GEN_TAC
   THENL [
        DISCH_TAC
        THEN FIRST_ASSUM (IMP_RES_TAC o REWRITE_RULE [ADD_0] o SPEC ``0``)
        THEN GEN_TAC
        THEN DISCH_THEN (DISJ_CASES_THEN2
               (fn t => DISJ1_TAC THEN ACCEPT_TAC t)
               (fn t => DISJ2_TAC THEN ASSUME_TAC t THEN RES_TAC)),
        PURE_ONCE_REWRITE_TAC [numLib.DECIDE ``!n m. m + SUC n = SUC m + n``]
        THEN REPEAT STRIP_TAC
        THEN DISJ2_TAC
        THEN RES_TAC]);

val MEM_TAKE = Q.store_thm ("MEM_TAKE",
   `!l m x. MEM x (TAKE m l) ==> MEM x l`,
   rw [MEM_EXISTS] \\ drule EXISTS_TAKE \\ simp []);

Theorem MEM_DROP_IMP:
  !l m x. MEM x (DROP m l) ==> MEM x l
Proof
  rw [MEM_EXISTS] \\ drule EXISTS_DROP \\ simp []
QED

val MEM_BUTLASTN = Q.store_thm ("MEM_BUTLASTN",
   `!l m x. MEM x (BUTLASTN m l) ==> MEM x l`,
   rw [MEM_EXISTS] \\ drule EXISTS_BUTLASTN \\ simp []);

val MEM_LASTN = Q.store_thm ("MEM_LASTN",
   `!m l x. MEM x (LASTN m l) ==> MEM x l`,
   rw [MEM_EXISTS] \\ drule EXISTS_LASTN \\ simp []);

val EVERY_SEG = Q.store_thm ("EVERY_SEG",
   `!P l. EVERY P l ==> !m k. m + k <= LENGTH l ==> EVERY P (SEG m k l)`,
   GEN_TAC
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [EVERY_DEF, SEG, LENGTH]
   THENL [
      REPEAT INDUCT_TAC
      THEN REWRITE_TAC [ADD, ADD_0, NOT_SUC_LESS_EQ_0, SEG, EVERY_DEF],
      GEN_TAC
      THEN STRIP_TAC
      THEN REPEAT INDUCT_TAC
      THEN REWRITE_TAC
             [ADD, ADD_0, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, SEG, EVERY_DEF]
      THEN1 mesonLib.ASM_MESON_TAC [ADD_CLAUSES]
      THEN SUBST1_TAC (numLib.DECIDE ``m + SUC k = SUC m + k``)
      THEN DISCH_TAC
      THEN RES_TAC]);

Theorem EVERY_TAKE:
 !P l m. EVERY P l ==> EVERY P (TAKE m l)
Proof
 metis_tac [EVERY_MEM, MEM_TAKE]
QED

Theorem EVERY_DROP:
 !P l m. EVERY P l ==> EVERY P (DROP m l)
Proof
 metis_tac [EVERY_MEM, MEM_DROP_IMP]
QED

Theorem EVERY_REVERSE[simp]:
  !P l. EVERY P (REVERSE l) = EVERY P l
Proof
  GEN_TAC
  THEN LIST_INDUCT_TAC
  THEN ASM_REWRITE_TAC [EVERY_DEF, REVERSE, EVERY_SNOC]
  THEN GEN_TAC
  THEN MATCH_ACCEPT_TAC CONJ_SYM
QED

Theorem EVERY_LASTN:
 !P l m. EVERY P l ==> EVERY P (LASTN m l)
Proof
 simp [LASTN_def, EVERY_REVERSE, EVERY_TAKE]
QED

Theorem EVERY_BUTLASTN:
 !P l m. EVERY P l ==> EVERY P (BUTLASTN m l)
Proof
 simp [BUTLASTN_def, EVERY_REVERSE, EVERY_DROP]
QED

val ZIP_SNOC = Q.store_thm ("ZIP_SNOC",
   `!l1 l2.
       (LENGTH l1 = LENGTH l2) ==>
       !x1 x2.  ZIP (SNOC x1 l1, SNOC x2 l2) = SNOC (x1, x2) (ZIP (l1, l2))`,
   LIST_INDUCT_TAC
   THEN REPEAT (FILTER_GEN_TAC ``l2:'b list``)
   THEN LIST_INDUCT_TAC
   THEN REWRITE_TAC [SNOC, ZIP, LENGTH, numTheory.NOT_SUC, SUC_NOT]
   THEN REWRITE_TAC [INV_SUC_EQ, CONS_11]
   THEN REPEAT STRIP_TAC
   THEN RES_THEN MATCH_ACCEPT_TAC);

val UNZIP_SNOC = Q.store_thm ("UNZIP_SNOC",
   `!x l. UNZIP (SNOC x l) =
          (SNOC (FST x) (FST (UNZIP l)), SNOC (SND x) (SND (UNZIP l)))`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [SNOC, UNZIP]);

val LENGTH_UNZIP_FST = Q.store_thm ("LENGTH_UNZIP_FST",
   `!l. LENGTH (UNZIP_FST l) = LENGTH l`,
   PURE_ONCE_REWRITE_TAC [UNZIP_FST_DEF]
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [UNZIP, LENGTH]);

val LENGTH_UNZIP_SND = Q.store_thm ("LENGTH_UNZIP_SND",
   `!l. LENGTH (UNZIP_SND l) = LENGTH l`,
   PURE_ONCE_REWRITE_TAC [UNZIP_SND_DEF]
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [UNZIP, LENGTH]);

val SUM_REVERSE = Q.store_thm ("SUM_REVERSE",
   `!l. SUM (REVERSE l) = SUM l`,
   LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [SUM, REVERSE, SUM_SNOC]
   THEN MATCH_ACCEPT_TAC ADD_SYM);

val SUM_FLAT = Q.store_thm ("SUM_FLAT",
   `!l. SUM (FLAT l) = SUM (MAP SUM l)`,
   LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [SUM, FLAT, MAP, SUM_APPEND]);

val EL_APPEND1 = Q.store_thm ("EL_APPEND1",
   `!n l1 l2. n < LENGTH l1 ==> (EL n (APPEND l1 l2) = EL n l1)`,
   simp_tac(srw_ss()) [EL_APPEND_EQN]);

val EL_APPEND2 = Q.store_thm ("EL_APPEND2",
   `!l1 n.
      LENGTH l1 <= n ==> !l2. EL n (APPEND l1 l2) = EL (n - (LENGTH l1)) l2`,
   simp_tac (srw_ss() ++ numSimps.ARITH_ss) [EL_APPEND_EQN]);

local
  val op >> = op THEN
  val rw = SRW_TAC[]
  val simp = ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++numSimps.ARITH_ss)
  val fs = FULL_SIMP_TAC(srw_ss())
in
Theorem LUPDATE_APPEND2:
   !l1 l2 n x.
      LENGTH l1 <= n ==>
      (LUPDATE x n (l1 ++ l2) = l1 ++ (LUPDATE x (n-LENGTH l1) l2))
Proof
  Induct_on ‘l1’ THENL [
    SRW_TAC [] [],
    Cases_on ‘n’ THENL [
      SRW_TAC [] [],
      FULL_SIMP_TAC (srw_ss ()) [] THEN METIS_TAC [LUPDATE_def]
    ]
  ]
QED

val LUPDATE_APPEND1 = Q.store_thm("LUPDATE_APPEND1",
   `!l1 l2 n x.
      n < LENGTH l1 ==> (LUPDATE x n (l1 ++ l2) = (LUPDATE x n l1) ++ l2)`,
   rw[]
   >> simp[LIST_EQ_REWRITE]
   >> Q.X_GEN_TAC`z`
   >> simp[EL_LUPDATE]
   >> rw[]
   >> simp[EL_APPEND2,EL_LUPDATE]
   >> fs[]
   >> Cases_on`z < LENGTH l1`
   >> fs[]
   >> simp[EL_APPEND1,EL_APPEND2,EL_LUPDATE]);

val is_prefix_el = Q.store_thm ("is_prefix_el",
  `!n l1 l2.
    isPREFIX l1 l2 /\ n < LENGTH l1 /\ n < LENGTH l2
   ==>
    (EL n l1 = EL n l2)`,
  Induct_on `n` >> rw [] >>
  Cases_on `l1` >>
  Cases_on `l2` >>
  rw [] >> fs []);

end

val EL_CONS = Q.store_thm ("EL_CONS",
   `!n. 0 < n ==> !x l. EL n (CONS x l) = EL (PRE n) l`,
   INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_LESS_0, EL, HD, TL, PRE]);

val SEG1 = Q.store_thm(
  "SEG1",
  ‘!n l. n < LENGTH l ==> (SEG 1 n l = [EL n l])’,
  Induct >- (Cases_on ‘l’ >> REWRITE_TAC [SEG, ONE] >> SIMP_TAC (srw_ss())[]) >>
  Cases_on ‘l’ >> REWRITE_TAC [SEG, ONE] >>
  ASM_SIMP_TAC (srw_ss()) []);

val EL_SEG = Q.store_thm ("EL_SEG",
   `!n l. n < LENGTH l ==> (EL n l = HD (SEG 1 n l))`,
   METIS_TAC [SEG1, HD]);

val SEG_CONS = Q.store_thm("SEG_CONS",
  ‘!j n h t. 0 < j /\ n+j <= LENGTH t + 1 ==> (SEG n j (h::t) = SEG n (j-1) t)’,
  Induct_on ‘j’ >> SIMP_TAC (srw_ss()) [] >> Cases_on ‘n’ >>
  SIMP_TAC (srw_ss()) [SEG]);

val SEG_SUC_EL = Q.store_thm("SEG_SUC_EL",
  ‘!n i l.
    i + n < LENGTH l ==> (SEG (SUC n) i l = EL i l :: SEG n (i+1) l)’,
  Induct_on `l` >> SIMP_TAC (srw_ss()) [] >> Cases_on ‘i’ >>
  ASM_SIMP_TAC(srw_ss() ++ numSimps.ARITH_ss) [SEG, SEG_CONS, ADD_CLAUSES] >>
  SIMP_TAC (srw_ss()) [ADD1]);

val TAKE_SEG_DROP = Q.store_thm("TAKE_SEG_DROP",
  ‘!n i l. i + n <= LENGTH l ==> (TAKE i l ++ SEG n i l ++ DROP (i + n) l = l)’,
  Induct_on `l` >> SIMP_TAC (srw_ss()) [SEG] >> Cases_on `n`
  >- SIMP_TAC (srw_ss()) [SEG] >>
  Cases_on `i` >> ASM_SIMP_TAC (srw_ss()) [SEG] >> strip_tac
  >- (Q.RENAME_TAC [‘SEG n 0 s ++ DROP n s’] >>
      first_x_assum (Q.SPECL_THEN [‘n’, ‘0’] mp_tac) >>
      ASM_SIMP_TAC (srw_ss()) []) >>
  Q.RENAME_TAC [‘TAKE m s ++ SEG (SUC n) m s ++ _’] >>
  first_x_assum (Q.SPECL_THEN [‘SUC n’, ‘m’] mp_tac) >>
  SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [ADD1]);

val EL_MEM = Q.store_thm ("EL_MEM",
   `!n l. n < LENGTH l ==> (MEM (EL n l) l)`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [LENGTH, EL, HD, TL, NOT_LESS_0, LESS_MONO_EQ, MEM]
   THEN REPEAT STRIP_TAC
   THEN DISJ2_TAC
   THEN RES_TAC);

val TL_SNOC = Q.store_thm ("TL_SNOC",
   `!x l. TL (SNOC x l) = if NULL l then [] else SNOC x (TL l)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [SNOC, TL, NULL]);

val EL_REVERSE_ELL = Q.store_thm ("EL_REVERSE_ELL",
   `!n l. n < LENGTH l ==> (EL n (REVERSE l) = ELL n l)`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC
           [LENGTH, LENGTH_SNOC, REVERSE_SNOC, EL, ELL, HD, TL, LAST_SNOC,
            FRONT_SNOC, NOT_LESS_0, LESS_MONO_EQ, SUB_0]);

val ELL_LENGTH_APPEND = Q.store_thm ("ELL_LENGTH_APPEND",
   `!l1 l2.  ~NULL l1 ==> (ELL (LENGTH l2) (APPEND l1 l2) = LAST l1)`,
   GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC
         [LENGTH, LENGTH_SNOC, APPEND_SNOC, APPEND_NIL, ELL, TL, FRONT_SNOC]);

val ELL_MEM = Q.store_thm ("ELL_MEM",
   `!n l. n < LENGTH l ==> MEM (ELL n l) l`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [NOT_LESS_0, LESS_MONO_EQ, LENGTH_SNOC, ELL_0_SNOC,
                         MEM_SNOC, ELL_SUC_SNOC, LENGTH]
   THEN REPEAT STRIP_TAC
   THEN DISJ2_TAC
   THEN RES_TAC);

val ELL_REVERSE = Q.store_thm ("ELL_REVERSE",
   `!n l. n < LENGTH l ==> (ELL n (REVERSE l) = ELL (PRE (LENGTH l - n)) l)`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC
          [LENGTH, LENGTH_SNOC, REVERSE, SUB_0, ELL, LAST_SNOC, FRONT_SNOC,
           NOT_LESS_0, LESS_MONO_EQ, PRE, ELL_LENGTH_CONS, SUB_MONO_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_THEN SUBST1_TAC
   THEN MATCH_MP_TAC (GSYM ELL_CONS)
   THEN REWRITE_TAC (PRE_SUB1 :: (map GSYM [SUB_PLUS, ADD1]))
   THEN IMP_RES_TAC (numLib.DECIDE ``!m n. n < m ==> m - SUC n < m``));

val ELL_REVERSE_EL = Q.store_thm ("ELL_REVERSE_EL",
   `!n l. n < LENGTH l ==> (ELL n (REVERSE l) = EL n l)`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC
          [LENGTH, LENGTH_SNOC, REVERSE, REVERSE_SNOC, EL, ELL, HD, TL,
           LAST_SNOC, FRONT_SNOC, NOT_LESS_0, LESS_MONO_EQ, SUB_0]);

val LESS_EQ_SPLIT = numLib.DECIDE ``!p n m. m + n <= p ==> n <= p /\ m <= p``

val SUB_LESS_EQ_ADD =
   numLib.DECIDE ``!p n m. n <= p ==> (m <= p - n <=> m + n <= p)``


Theorem BUTLASTN_TAKE_UNCOND:
  !n l. BUTLASTN n l = TAKE (LENGTH l - n) l
Proof
  simp[BUTLASTN_def] >> Induct >> simp[] >>
  Cases using SNOC_CASES >> simp[TAKE_APPEND] >>
  simp[ARITH_PROVE “1 - SUC x = 0”, ARITH_PROVE “x + 1 - SUC y = x - y”]
QED

Theorem BUTLASTN_TAKE:
  !n l. n <= LENGTH l ==> (BUTLASTN n l = TAKE (LENGTH l - n) l)
Proof
  simp[BUTLASTN_TAKE_UNCOND]
QED

Theorem TAKE_BUTLASTN:
  !n l. n <= LENGTH l ==> TAKE n l = BUTLASTN (LENGTH l - n) l
Proof
  simp[BUTLASTN_TAKE]
QED

Theorem LASTN_DROP_UNCOND:
  !n l. LASTN n l = DROP (LENGTH l - n) l
Proof
  simp[LASTN_def] >> Induct >> simp[] >>
  Cases using SNOC_CASES >> simp[DROP_APPEND] >>
  simp[ARITH_PROVE “1 - SUC n = 0”, ARITH_PROVE “x + 1 - SUC y = x - y”]
QED

Theorem LASTN_DROP:
   !n l. n <= LENGTH l ==> LASTN n l = DROP (LENGTH l - n) l
Proof
  simp[LASTN_DROP_UNCOND]
QED

Theorem DROP_LASTN:
  !n l. n <= LENGTH l ==> DROP n l = LASTN (LENGTH l - n) l
Proof
  simp[LASTN_DROP_UNCOND]
QED

val SUB_ADD_lem =
   numLib.DECIDE ``!l n m. n + m <= l ==> ((l - (n + m)) + n = l - m)``

val SEG_LASTN_BUTLASTN = Q.store_thm ("SEG_LASTN_BUTLASTN",
   `!n m l.
       n + m <= LENGTH l ==>
       (SEG n m l = LASTN n (BUTLASTN (LENGTH l - (n + m)) l))`,
   let
      val th2 = SUBS [(REWRITE_RULE [SUB_LESS_EQ]
                 (SPECL [``LENGTH (l:'a list) - m``, ``l:'a list``]
                    LENGTH_LASTN))]
                 (SPECL [``n:num``, ``LASTN (LENGTH l - m) (l:'a list)``]
                    TAKE_BUTLASTN)
      val th3 = UNDISCH_ALL (SUBS [UNDISCH_ALL
                   (SPECL [``LENGTH (l:'a list)``,``m:num``,``n:num``]
                    SUB_LESS_EQ_ADD)] th2)
      val th4 = PURE_ONCE_REWRITE_RULE [ADD_SYM] (REWRITE_RULE
                  [UNDISCH_ALL
                     (SPECL [``LENGTH (l:'a list)``,``n:num``,``m:num``]
                      SUB_ADD_lem), SUB_LESS_EQ]
                  (PURE_ONCE_REWRITE_RULE [ADD_SYM]
                      (SPECL [``n:num``,``LENGTH (l:'a list) - (n + m)``,
                              ``l:'a list``] LASTN_BUTLASTN)))
   in
      REPEAT GEN_TAC
      THEN DISCH_TAC
      THEN IMP_RES_THEN SUBST1_TAC SEG_TAKE_DROP
      THEN IMP_RES_TAC LESS_EQ_SPLIT
      THEN SUBST1_TAC (UNDISCH_ALL (SPECL [``m:num``,``l:'a list``] DROP_LASTN))
      THEN SUBST1_TAC th3
      THEN REWRITE_TAC [GSYM SUB_PLUS]
      THEN SUBST_OCCS_TAC [([1], (SPEC_ALL ADD_SYM))]
      THEN CONV_TAC SYM_CONV
      THEN ACCEPT_TAC th4
   end);

val DROP_REVERSE = Q.store_thm ("DROP_REVERSE",
   `!n l. n <= LENGTH l ==> (DROP n (REVERSE l) = REVERSE (BUTLASTN n l))`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [NOT_SUC_LESS_EQ_0, LENGTH, LENGTH_SNOC, DROP,
                         BUTLASTN, LESS_EQ_MONO, REVERSE_SNOC]);

val BUTLASTN_REVERSE = Q.store_thm ("BUTLASTN_REVERSE",
   `!n l. n <= LENGTH l ==> (BUTLASTN n (REVERSE l) = REVERSE (DROP n l))`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC
          [NOT_SUC_LESS_EQ_0, LENGTH, DROP, BUTLASTN, LESS_EQ_MONO, REVERSE]);

val LASTN_REVERSE = Q.store_thm ("LASTN_REVERSE",
   `!n l. n <= LENGTH l ==> (LASTN n (REVERSE l) = REVERSE (TAKE n l))`,
   INDUCT_TAC
   THEN LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC [NOT_SUC_LESS_EQ_0, LENGTH, TAKE, LASTN, LESS_EQ_MONO,
                         REVERSE, SNOC_11]);

val TAKE_REVERSE = Q.store_thm ("TAKE_REVERSE",
   `!n l. n <= LENGTH l ==> (TAKE n (REVERSE l) = REVERSE (LASTN n l))`,
   INDUCT_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [NOT_SUC_LESS_EQ_0, LENGTH, LENGTH_SNOC, TAKE, LASTN,
                         LESS_EQ_MONO, REVERSE, REVERSE_SNOC, CONS_11]);

val SEG_REVERSE = Q.store_thm ("SEG_REVERSE",
   `!n m l.
      n + m <= LENGTH l ==>
      (SEG n m (REVERSE l) = REVERSE (SEG n (LENGTH l - (n + m)) l))`,
   let
      val SUB_LE_ADD =
         SPECL [``LENGTH (l:'a list)``, ``m:num``, ``n:num``] SUB_LESS_EQ_ADD
      val SEG_lem =
         REWRITE_RULE [SUB_LESS_EQ] (PURE_ONCE_REWRITE_RULE [ADD_SYM]
          (SUBS[UNDISCH_ALL(SPEC_ALL(SPEC``LENGTH(l:'a list)`` SUB_ADD_lem))]
           (PURE_ONCE_REWRITE_RULE [ADD_SYM]
            (SPECL[``n:num``,``LENGTH(l:'a list) -(n+m)``,``l:'a list``]
              SEG_LASTN_BUTLASTN))))
      val lem =
         PURE_ONCE_REWRITE_RULE [ADD_SUB](PURE_ONCE_REWRITE_RULE [ADD_SYM]
           (SPEC ``LENGTH(l:'a list)``
            (UNDISCH_ALL(SPECL[``LENGTH(l:'a list)``,``m:num``]SUB_SUB))))
   in
      REPEAT GEN_TAC THEN DISCH_TAC
      THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP SEG_TAKE_DROP)
          o (SUBS[SYM (SPEC``l:'a list`` LENGTH_REVERSE)]))
      THEN IMP_RES_TAC LESS_EQ_SPLIT
      THEN IMP_RES_THEN SUBST1_TAC (SPECL[``m:num``,``l:'a list``] DROP_REVERSE)
      THEN FIRST_ASSUM
          (ASSUME_TAC o (MP(SPECL[``m:num``,``(l:'a list)``]LENGTH_BUTLASTN)))
      THEN FIRST_ASSUM (fn t =>  ASSUME_TAC (SUBS[t]
          (SPECL[``n:num``,``BUTLASTN m (l:'a list)``] TAKE_REVERSE)))
      THEN FIRST_ASSUM (SUBST_ALL_TAC o (MP SUB_LE_ADD))
      THEN RES_THEN SUBST1_TAC THEN AP_TERM_TAC
      THEN SUBST1_TAC SEG_lem THEN SUBST1_TAC lem THEN REFL_TAC
   end);

Theorem LENGTH_REPLICATE[simp]:
   !n x. LENGTH (REPLICATE n x) = n
Proof INDUCT_TAC THEN ASM_REWRITE_TAC [REPLICATE, LENGTH]
QED

Theorem MEM_REPLICATE[simp]:
  !n x y. MEM y (REPLICATE n x) <=> x = y /\ 0 < n
Proof INDUCT_TAC THEN simp [NOT_LESS_0, MEM, EQ_IMP_THM, DISJ_IMP_THM]
QED

(* |- !l. AND_EL l <=> FOLDL $/\ T l *)
val AND_EL_FOLDL = save_thm ("AND_EL_FOLDL",
   GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE [EVERY_FOLDL, combinTheory.I_THM]
      (AP_THM AND_EL_DEF ``l:bool list``))));

(* |- !l. AND_EL l <=> FOLDR $/\ T l *)
val AND_EL_FOLDR = save_thm ("AND_EL_FOLDR",
   GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE [EVERY_FOLDR, combinTheory.I_THM]
      (AP_THM AND_EL_DEF ``l:bool list``))));

(* |- !l. OR_EL l <=> FOLDL $\/ F l *)
val OR_EL_FOLDL = save_thm ("OR_EL_FOLDL",
   GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE [EXISTS_FOLDL, combinTheory.I_THM]
      (AP_THM OR_EL_DEF ``l:bool list``))));

(* |- !l. OR_EL l <=> FOLDR $\/ F l *)
val OR_EL_FOLDR = save_thm ("OR_EL_FOLDR",
   GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE [EXISTS_FOLDR, combinTheory.I_THM]
      (AP_THM OR_EL_DEF ``l:bool list``))));

Theorem ITSET_TO_FOLDR:
    !f s b. FINITE s ==> ITSET f s b = FOLDR f b (REVERSE (SET_TO_LIST s))
Proof
    rw[listTheory.ITSET_eq_FOLDL_SET_TO_LIST,FOLDR_REVERSE,combinTheory.C_DEF]
QED

(*---------------------------------------------------------------------------
   A bunch of properties relating to the use of IS_PREFIX as a partial order
 ---------------------------------------------------------------------------*)

val list_CASES = list_CASES

val IS_PREFIX_NIL = Q.store_thm ("IS_PREFIX_NIL",
   `!x. IS_PREFIX x [] /\ (IS_PREFIX [] x = (x = []))`,
   STRIP_TAC
   THEN MP_TAC (Q.SPEC `x` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN PROVE_TAC [NOT_NIL_CONS]);

val IS_PREFIX_REFL = Q.store_thm ("IS_PREFIX_REFL",
   `!x. IS_PREFIX x x`,
   INDUCT_THEN list_INDUCT MP_TAC
   THEN SIMP_TAC boolSimps.bool_ss [IS_PREFIX]);
val _ = export_rewrites ["IS_PREFIX_REFL"]

val IS_PREFIX_ANTISYM = Q.store_thm ("IS_PREFIX_ANTISYM",
   `!x y. IS_PREFIX y x /\ IS_PREFIX x y ==> (x = y)`,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN ONCE_REWRITE_TAC [IS_PREFIX]
   THEN PROVE_TAC []);

val IS_PREFIX_TRANS = Q.store_thm ("IS_PREFIX_TRANS",
   `!x y z. IS_PREFIX x y /\ IS_PREFIX y z ==> IS_PREFIX x z`,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN MP_TAC (Q.SPEC `z` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN PROVE_TAC []);

val IS_PREFIX_BUTLAST = Q.store_thm ("IS_PREFIX_BUTLAST",
   `!x y. IS_PREFIX (x::y) (FRONT (x::y))`,
   REPEAT GEN_TAC
   THEN Q.SPEC_TAC (`x`, `x`)
   THEN Q.SPEC_TAC (`y`, `y`)
   THEN INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [FRONT_CONS, IS_PREFIX]);

val IS_PREFIX_LENGTH = Q.store_thm ("IS_PREFIX_LENGTH",
   `!x y. IS_PREFIX y x ==> LENGTH x <= LENGTH y`,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [LENGTH, ZERO_LESS_EQ]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, LENGTH, LESS_EQ_MONO]);

Theorem IS_PREFIX_LENGTH_ANTI:
   !x y. IS_PREFIX y x /\ (LENGTH x = LENGTH y) <=> (x = y)
Proof
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN1 PROVE_TAC [LENGTH_NIL, IS_PREFIX_REFL]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THENL [ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, LENGTH, LESS_EQ_MONO]
          THEN PROVE_TAC [NOT_CONS_NIL],
          ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, LENGTH, CONS_11]
          THEN PROVE_TAC [numTheory.INV_SUC, IS_PREFIX_REFL]]
QED

Theorem IS_PREFIX_SNOC:
   !x y z. IS_PREFIX (SNOC x y) z <=> IS_PREFIX y z \/ (z = SNOC x y)
Proof
   GEN_TAC
   THEN GEN_TAC
   THEN Q.SPEC_TAC (`x`, `x`)
   THEN Q.SPEC_TAC (`y`, `y`)
   THEN INDUCT_THEN list_INDUCT ASSUME_TAC
   THENL [REPEAT GEN_TAC
          THEN MP_TAC (Q.SPEC `z` list_CASES)
          THEN STRIP_TAC
          THEN ASM_SIMP_TAC boolSimps.bool_ss
                 [SNOC, IS_PREFIX_NIL, IS_PREFIX, CONS_11,
                  NOT_CONS_NIL]
          THEN PROVE_TAC [],
          REPEAT GEN_TAC
          THEN MP_TAC (Q.SPEC `z` list_CASES)
          THEN STRIP_TAC
          THEN ASM_SIMP_TAC boolSimps.bool_ss
                 [SNOC, IS_PREFIX_NIL, IS_PREFIX, CONS_11,
                  NOT_CONS_NIL]
          THEN PROVE_TAC []]
QED

val IS_PREFIX_APPEND1 = Q.store_thm ("IS_PREFIX_APPEND1",
   `!a b c. IS_PREFIX c (APPEND a b) ==> IS_PREFIX c a`,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, APPEND]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `c` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN PROVE_TAC []);

val IS_PREFIX_APPEND2 = Q.store_thm ("IS_PREFIX_APPEND2",
   `!a b c. IS_PREFIX (APPEND b c) a ==> IS_PREFIX b a \/ IS_PREFIX a b`,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `b` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, APPEND]
   THEN PROVE_TAC []);

Theorem IS_PREFIX_APPENDS[simp]:
   !a b c. IS_PREFIX (APPEND a c) (APPEND a b) <=> IS_PREFIX c b
Proof
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [APPEND, IS_PREFIX]
QED

(* |- !a c. a <<= a ++ c *)
val IS_PREFIX_APPEND3 = save_thm("IS_PREFIX_APPEND3",
  IS_PREFIX_APPENDS |> SPEC_ALL |> Q.INST [`b` |-> `[]`]
                    |> REWRITE_RULE [IS_PREFIX, APPEND_NIL]
                    |> Q.GENL [`c`, `a`])
val _ = export_rewrites ["IS_PREFIX_APPEND3"]

val prefixes_is_prefix_total = Q.store_thm("prefixes_is_prefix_total",
  `!l l1 l2.
    IS_PREFIX l l1 /\ IS_PREFIX l l2 ==> IS_PREFIX l2 l1 \/ IS_PREFIX l1 l2`,
  Induct THEN SIMP_TAC(srw_ss())[IS_PREFIX_NIL] THEN
  GEN_TAC THEN Cases THEN SIMP_TAC(srw_ss())[] THEN
  Cases THEN SRW_TAC[][])

(* ----------------------------------------------------------------------
    longest_prefix

    longest string that is a prefix of all elements of a set. If the set
    is empty, return []
   ---------------------------------------------------------------------- *)

val common_prefixes_def = new_definition(
  "common_prefixes_def",
  “common_prefixes s = { p | !m. m IN s ==> p <<= m}”
);

val common_prefixes_BIGINTER = Q.store_thm(
  "common_prefixes_BIGINTER",
  ‘common_prefixes s = BIGINTER (IMAGE (\l. { p | p <<= l }) s)’,
  simp[EXTENSION, common_prefixes_def] >> gen_tac >> eq_tac >> rw[]
  >- metis_tac[] >>
  first_x_assum (Q.SPEC_THEN ‘{ y | y <<= m }’ mp_tac) >> simp[] >>
  disch_then irule >> Q.EXISTS_TAC ‘m’ >> simp[]);

val FINITE_prefix = Q.store_thm(
  "FINITE_prefix",
  ‘FINITE { a | a <<= b }’,
  Induct_on ‘b’ >> simp[isPREFIX_CONSR] >> Q.X_GEN_TAC ‘a’ >>
  Q.MATCH_ABBREV_TAC ‘FINITE s’ >>
  ‘s = {[]} UNION IMAGE (CONS a) { xs | xs <<= b }’ suffices_by simp[] >>
  simp[Abbr‘s’, EXTENSION]);

val FINITE_common_prefixes = Q.store_thm(
  "FINITE_common_prefixes[simp]",
  ‘s <> {} ==> FINITE (common_prefixes s)’,
  strip_tac >> simp[common_prefixes_BIGINTER] >> irule FINITE_BIGINTER >>
  simp[PULL_EXISTS,FINITE_prefix] >> metis_tac[IN_INSERT,SET_CASES]);

val common_prefixes_NONEMPTY = Q.store_thm(
  "common_prefixes_NONEMPTY[simp]",
  ‘common_prefixes s <> {}’,
  ‘[] IN common_prefixes s’ by simp[common_prefixes_def] >> strip_tac >> fs[]);

val longest_prefix_def = new_definition(
  "longest_prefix_def",
  “longest_prefix s =
     if s = {} then []
     else @x. is_measure_maximal LENGTH (common_prefixes s) x”
);

val two_common_prefixes = Q.store_thm(
  "two_common_prefixes",
  ‘s <> {} /\ p1 IN common_prefixes s /\ p2 IN common_prefixes s ==>
   p1 <<= p2 \/ p2 <<= p1’,
  rw[common_prefixes_def] >> Cases_on ‘s’ >> fs[] >>
  metis_tac[prefixes_is_prefix_total]);

val longest_prefix_UNIQUE = Q.store_thm(
  "longest_prefix_UNIQUE",
  ‘s <> {} /\ is_measure_maximal LENGTH (common_prefixes s) x /\
   is_measure_maximal LENGTH (common_prefixes s) y ==> (x = y)’,
  rw[is_measure_maximal_def] >>
  ‘LENGTH x = LENGTH y’ by metis_tac[arithmeticTheory.LESS_EQUAL_ANTISYM] >>
  dxrule_all_then strip_assume_tac two_common_prefixes >>
  metis_tac[IS_PREFIX_LENGTH_ANTI]);

val common_prefixes_NIL = Q.store_thm(
  "common_prefixes_NIL",
  ‘[] IN s ==> (common_prefixes s = {[]})’,
  simp[common_prefixes_def, EXTENSION] >> rpt strip_tac >> eq_tac >> strip_tac
  >- (first_x_assum drule >> simp[]) >> simp[]);

val longest_prefix_NIL = Q.store_thm(
  "longest_prefix_NIL",
  ‘[] IN s ==> (longest_prefix s = [])’,
  rw[longest_prefix_def, common_prefixes_NIL] >> SELECT_ELIM_TAC >>
  simp[is_measure_maximal_def]);

val NIL_IN_common_prefixes = Q.store_thm(
  "NIL_IN_common_prefixes[simp]",
  ‘[] IN common_prefixes s’,
  simp[common_prefixes_def]);

val longest_prefix_EMPTY = Q.store_thm(
  "longest_prefix_EMPTY[simp]",
  ‘longest_prefix {} = []’,
  simp[longest_prefix_def]);

val longest_prefix_SING = Q.store_thm(
  "longest_prefix_SING[simp]",
  ‘longest_prefix {s} = s’,
  simp[longest_prefix_def] >> SELECT_ELIM_TAC >> conj_tac
  >- (irule FINITE_is_measure_maximal >> simp[]) >>
  simp[is_measure_maximal_def, common_prefixes_def] >> rw[] >>
  metis_tac[IS_PREFIX_LENGTH_ANTI, LESS_EQUAL_ANTISYM, IS_PREFIX_LENGTH]);

val common_prefixes_PAIR = Q.store_thm(
  "common_prefixes_PAIR[simp]",
  ‘(common_prefixes {[]; x} = {[]}) /\ (common_prefixes {x; []} = {[]}) /\
   (common_prefixes {a::xs; b::ys} =
      [] INSERT (if a = b then IMAGE (CONS a) (common_prefixes {xs; ys})
                 else {}))’,
  simp[common_prefixes_NIL] >> rw[common_prefixes_def] >>
  simp[EXTENSION, DISJ_IMP_THM, FORALL_AND_THM, isPREFIX_CONSR] >>
  rw[EQ_IMP_THM]);

val longest_prefix_PAIR = Q.store_thm(
  "longest_prefix_PAIR",
  ‘(longest_prefix {[]; ys} = []) /\ (longest_prefix {xs; []} = []) /\
   (longest_prefix {x::xs; y::ys} =
      if x = y then x :: longest_prefix {xs; ys} else [])’,
  simp[longest_prefix_NIL] >> reverse (rw[])
  >- simp[longest_prefix_def] >>
  simp[longest_prefix_def] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (irule FINITE_is_measure_maximal >> simp[]) >>
  Q.X_GEN_TAC ‘m’ >>
  Q.ABBREV_TAC ‘cset = IMAGE (CONS x) (common_prefixes {xs;ys})’ >>
  ‘?c. c IN cset /\ LENGTH ([]:'a list) < LENGTH c’
    by (simp[Abbr‘cset’, PULL_EXISTS] >> Q.EXISTS_TAC ‘[]’ >> simp[]) >>
  drule_all_then assume_tac is_measure_maximal_INSERT >>
  simp[] >> SELECT_ELIM_TAC >> conj_tac
  >- (irule FINITE_is_measure_maximal >> simp[]) >>
  rw[is_measure_maximal_def, Abbr‘cset’]  >> fs[PULL_EXISTS] >>
  Q.RENAME_TAC [‘a = b’, ‘a IN common_prefixes {xs;ys}’,
                ‘b IN common_prefixes {xs;ys}’] >>
  ‘LENGTH a = LENGTH b’ by metis_tac[DECIDE “a <= b /\ b <= a ==> (a = b)”] >>
  ‘{xs;ys} <> {}’ by simp[] >>
  ‘a <<= b \/ b <<= a’ by metis_tac[two_common_prefixes] >>
  metis_tac[IS_PREFIX_LENGTH_ANTI])

(*---------------------------------------------------------------------------
   A list of numbers
 ---------------------------------------------------------------------------*)

val COUNT_LIST_GENLIST = Q.store_thm ("COUNT_LIST_GENLIST",
   `!n. COUNT_LIST n = GENLIST I n`,
   Induct_on `n`
   THEN1 SIMP_TAC std_ss [GENLIST, COUNT_LIST_def]
   THEN ASM_SIMP_TAC std_ss
          [COUNT_LIST_def, GENLIST_CONS, MAP_GENLIST]);

val LENGTH_COUNT_LIST = Q.store_thm ("LENGTH_COUNT_LIST",
   `!n. LENGTH (COUNT_LIST n) = n`,
   SIMP_TAC std_ss [COUNT_LIST_GENLIST, LENGTH_GENLIST]);

val EL_COUNT_LIST = Q.store_thm ("EL_COUNT_LIST",
   `!m n. m < n ==> (EL m (COUNT_LIST n) = m)`,
   SIMP_TAC std_ss [COUNT_LIST_GENLIST, EL_GENLIST]);

Theorem MEM_COUNT_LIST:
   !m n. MEM m (COUNT_LIST n) <=> m < n
Proof
   SIMP_TAC (std_ss++boolSimps.CONJ_ss)
     [MEM_EL, EL_COUNT_LIST, LENGTH_COUNT_LIST, EL_COUNT_LIST]
QED

val COUNT_LIST_SNOC = Q.store_thm ("COUNT_LIST_SNOC",
   `(COUNT_LIST 0 = []) /\
    (!n. COUNT_LIST (SUC n) = SNOC n (COUNT_LIST n))`,
   SIMP_TAC std_ss [COUNT_LIST_GENLIST, GENLIST]);

val COUNT_LIST_COUNT = Q.store_thm ("COUNT_LIST_COUNT",
   `!n. LIST_TO_SET (COUNT_LIST n) = count n`,
   Induct_on `n`
   THEN1 SIMP_TAC std_ss
           [pred_setTheory.COUNT_ZERO, COUNT_LIST_def,
            LIST_TO_SET_THM]
   THEN ASM_SIMP_TAC std_ss
          [COUNT_LIST_SNOC, pred_setTheory.COUNT_SUC,
           LIST_TO_SET_APPEND, SNOC_APPEND,
           LIST_TO_SET_THM]
   THEN SIMP_TAC std_ss
          [pred_setTheory.IN_UNION, pred_setTheory.IN_SING,
           pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT]
   THEN PROVE_TAC []);

val COUNT_LIST_ADD = Q.store_thm ("COUNT_LIST_ADD",
   `!n m. COUNT_LIST (n + m) =
          COUNT_LIST n ++ MAP (\n'. n' + n) (COUNT_LIST m)`,
   Induct_on `n`
   THEN1 SIMP_TAC std_ss [COUNT_LIST_def, APPEND, MAP_ID]
   THEN GEN_TAC
   THEN REWRITE_TAC [COUNT_LIST_SNOC]
   THEN `SUC n + m = n + SUC m` by DECIDE_TAC
   THEN ASM_SIMP_TAC std_ss
          [COUNT_LIST_def, MAP, MAP_MAP_o, combinTheory.o_DEF,
           SNOC_APPEND, GSYM APPEND_ASSOC, APPEND]
   THEN SIMP_TAC std_ss [arithmeticTheory.ADD_CLAUSES]);

Theorem MAP_COUNT_LIST:
  MAP f (COUNT_LIST n) = GENLIST f n
Proof  rw[COUNT_LIST_GENLIST,MAP_GENLIST]
QED

Theorem SUM_IMAGE_count_SUM_GENLIST:
  SIGMA f (count n) = SUM (GENLIST f n)
Proof
  Induct_on ‘n’ >>
  simp[SUM_IMAGE_THM, COUNT_SUC, GENLIST, SUM_SNOC]
QED

Theorem SUM_IMAGE_count_MULT:
  (!m. m < n ==> (g m = SIGMA (\x. f (x + k * m)) (count k))) ==>
  (SIGMA f (count (k * n)) = SIGMA g (count n))
Proof
  simp[SUM_IMAGE_count_SUM_GENLIST] >>
  Induct_on ‘n’ >- simp[] >>
  simp[MULT_SUC, GENLIST_APPEND, GENLIST,
       SUM_APPEND,
       SUM_SNOC]
QED

Theorem sum_of_sums:
  SIGMA (\m. SIGMA (f m) (count a)) (count b) =
  SIGMA (\m. f (m DIV a) (m MOD a)) (count (a * b))
Proof
Cases_on ‘a=0’ THEN SRW_TAC [][SUM_IMAGE_THM,SUM_IMAGE_ZERO] THEN
Cases_on ‘b=0’ THEN SRW_TAC [][SUM_IMAGE_THM,SUM_IMAGE_ZERO] THEN
MATCH_MP_TAC EQ_SYM THEN
MATCH_MP_TAC SUM_IMAGE_count_MULT THEN
SRW_TAC [][] THEN
MATCH_MP_TAC SUM_IMAGE_CONG THEN
SRW_TAC [][] THEN
METIS_TAC [ADD_SYM,MULT_SYM,DIV_MULT,MOD_MULT]
QED

(*---------------------------------------------------------------------------
   General theorems about lists. From Anthony Fox's and Thomas Tuerk's theories.
   Added by Thomas Tuerk
 ---------------------------------------------------------------------------*)

val SNOC_EL_TAKE = Q.store_thm ("SNOC_EL_TAKE",
   `!n l. n < LENGTH l ==> (SNOC (EL n l) (TAKE n l) = TAKE (SUC n) l)`,
   Induct_on `n` THEN Cases_on `l` THEN ASM_SIMP_TAC list_ss [SNOC, TAKE]);

val ZIP_TAKE_LEQ = Q.store_thm ("ZIP_TAKE_LEQ",
  `!n a b.
     n <= LENGTH a /\ LENGTH a <= LENGTH b ==>
     (ZIP (TAKE n a, TAKE n b) = TAKE n (ZIP (a, TAKE (LENGTH a) b)))`,
  Induct_on `n`
  THEN ASM_SIMP_TAC list_ss [TAKE]
  THEN Cases_on `a`
  THEN Cases_on `b`
  THEN ASM_SIMP_TAC list_ss [TAKE, ZIP]);

val ZIP_TAKE = Q.store_thm ("ZIP_TAKE",
   `!n a b.
      n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
      (ZIP (TAKE n a, TAKE n b) = TAKE n (ZIP (a, b)))`,
  SIMP_TAC arith_ss [ZIP_TAKE_LEQ, TAKE_LENGTH_ID]);

val ZIP_APPEND = Q.store_thm ("ZIP_APPEND",
  `!a b c d.
      (LENGTH a = LENGTH b) /\ (LENGTH c = LENGTH d) ==>
      (ZIP (a, b) ++ ZIP (c, d) = ZIP (a ++ c, b ++ d))`,
  Induct_on `b` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
  THEN Induct_on `d` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
  THEN Induct_on `a` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
  THEN Induct_on `c` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
  THEN MAP_EVERY Q.X_GEN_TAC [`h1`,`h2`,`h3`,`h4`]
  THEN RW_TAC list_ss []
  THEN `LENGTH (h1::c) = LENGTH (h3::d)` by ASM_SIMP_TAC list_ss []
  THEN `ZIP (a, b) ++ ZIP (h1::c, h3::d) = ZIP (a ++ h1::c, b ++ h3::d)`
    by ASM_SIMP_TAC list_ss []
  THEN FULL_SIMP_TAC list_ss []);

val APPEND_ASSOC_CONS = Q.store_thm ("APPEND_ASSOC_CONS",
   `!l1 h l2 l3. (l1 ++ (h::l2) ++ l3 = l1 ++ h::(l2 ++ l3))`,
   REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]);

val APPEND_SNOC1 = Q.store_thm ("APPEND_SNOC1",
   `!l1 x l2. SNOC x l1 ++ l2 = l1 ++ x::l2`,
   PROVE_TAC [SNOC_APPEND, CONS_APPEND, APPEND_ASSOC]);

val FOLDL_MAP2 = Q.store_thm ("FOLDL_MAP2",
   `!f e g l. FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l`,
   GEN_TAC
   THEN GEN_TAC
   THEN GEN_TAC
   THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC [MAP, FOLDL, FOLDL_SNOC, MAP_SNOC, FOLDR]
   THEN BETA_TAC
   THEN REWRITE_TAC []);

val SPLITP_EVERY = Q.store_thm ("SPLITP_EVERY",
   `!P l. EVERY (\x. ~P x) l ==> (SPLITP P l = (l, []))`,
   Induct_on `l` THEN SRW_TAC [] [SPLITP]);

val MEM_FRONT = Q.store_thm ("MEM_FRONT",
   `!l e y. MEM y (FRONT (e::l)) ==> MEM y (e::l)`,
   Induct_on `l` THEN FULL_SIMP_TAC list_ss [DISJ_IMP_THM, MEM]);

Theorem MEM_FRONT_NOT_NIL :
    !l y. l <> [] /\ MEM y (FRONT l) ==> MEM y l
Proof
    rpt STRIP_TAC
 >> Cases_on ‘l’ >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC MEM_FRONT >> ASM_REWRITE_TAC []
QED

val FRONT_APPEND = Q.store_thm ("FRONT_APPEND",
   `!l1 l2 e. FRONT (l1 ++ e::l2) = l1 ++ FRONT (e::l2)`,
   Induct_on `l1` THEN ASM_SIMP_TAC list_ss [FRONT_DEF])

Theorem FRONT_APPEND_NOT_NIL :
    !l1 l2. l2 <> [] ==> FRONT (l1 ++ l2) = l1 ++ FRONT l2
Proof
    rpt STRIP_TAC
 >> Cases_on ‘l2’
 >> FULL_SIMP_TAC std_ss [FRONT_APPEND]
QED

Theorem LAST_APPEND_NOT_NIL :
    !l1 l2. l2 <> [] ==> LAST (l1 ++ l2) = LAST l2
Proof
    rpt STRIP_TAC
 >> Cases_on ‘l2’
 >> FULL_SIMP_TAC std_ss [LAST_APPEND_CONS]
QED

val EL_FRONT = Q.store_thm ("EL_FRONT",
   `!l n. n < LENGTH (FRONT l) /\ ~NULL l ==> (EL n (FRONT l) = EL n l)`,
   Induct_on `l`
   THEN REWRITE_TAC [NULL]
   THEN Cases_on `l`
   THEN FULL_SIMP_TAC list_ss [NULL, LENGTH_FRONT]
   THEN Cases_on `n`
   THEN ASM_SIMP_TAC list_ss []);

val MEM_LAST = Q.store_thm ("MEM_LAST",
   `!e l. MEM (LAST (e::l)) (e::l)`,
   Induct_on `l` THEN ASM_SIMP_TAC arith_ss [LAST_CONS, Once MEM]);

Theorem MEM_LAST_NOT_NIL :
    !e l. l <> [] ==> MEM (LAST l) l
Proof
    rpt STRIP_TAC
 >> Cases_on ‘l’ >> FULL_SIMP_TAC std_ss [MEM_LAST]
QED

val DROP_CONS_EL = Q.store_thm ("DROP_CONS_EL",
   `!n l. n < LENGTH l ==> (DROP n l = EL n l :: DROP (SUC n) l)`,
   Induct_on `l`
   THEN1 SIMP_TAC list_ss []
   THEN Cases_on `n`
   THEN ASM_SIMP_TAC list_ss []);

val MEM_LAST_FRONT = Q.store_thm ("MEM_LAST_FRONT",
   `!e l h. MEM e l /\ ~(e = LAST (h::l)) ==> MEM e (FRONT (h::l))`,
   Induct_on `l`
   THEN FULL_SIMP_TAC list_ss
          [COND_RATOR, COND_RAND, FRONT_DEF, LAST_DEF]
   THEN PROVE_TAC []);

(*---------------------------------------------------------------------------
   LIST_ELEM_COUNT
   Added by Thomas Tuerk
 ---------------------------------------------------------------------------*)

val LIST_ELEM_COUNT_THM = Q.store_thm ("LIST_ELEM_COUNT_THM",
   `(!e. LIST_ELEM_COUNT e [] = 0) /\
    (!e l1 l2.
       LIST_ELEM_COUNT e (l1++l2) =
       LIST_ELEM_COUNT e l1 + LIST_ELEM_COUNT e l2) /\
    (!e h l.
       (h = e) ==> (LIST_ELEM_COUNT e (h::l) = SUC (LIST_ELEM_COUNT e l))) /\
    (!e h l. ~(h = e) ==> (LIST_ELEM_COUNT e (h::l) = LIST_ELEM_COUNT e l))`,
   SIMP_TAC list_ss [LIST_ELEM_COUNT_DEF, FILTER_APPEND]);

val LIST_ELEM_COUNT_MEM = Q.store_thm ("LIST_ELEM_COUNT_MEM",
   `!e l. (LIST_ELEM_COUNT e l > 0) = (MEM e l)`,
   Induct_on `l`
   THEN FULL_SIMP_TAC list_ss [LIST_ELEM_COUNT_DEF, COND_RAND, COND_RATOR]
   THEN PROVE_TAC []);

(*---------------------------------------------------------------------------*)
(* Various lemmas from the CakeML project https://cakeml.org                 *)
(*---------------------------------------------------------------------------*)

local
  val rw = SRW_TAC []
  val metis_tac = METIS_TAC
  val fs = FULL_SIMP_TAC (srw_ss())
  val rfs = REV_FULL_SIMP_TAC (srw_ss())
  fun simpss() = srw_ss()++boolSimps.LET_ss++numSimps.ARITH_ss
  fun simp ths = asm_simp_tac (simpss()) ths
  fun dsimp ths = asm_simp_tac (simpss() ++ boolSimps.DNF_ss) ths
  val decide_tac = numLib.DECIDE_TAC
  open pred_setTheory open listTheory pairTheory;
in

val LIST_TO_SET_EQ_SING = Q.store_thm("LIST_TO_SET_EQ_SING",
   `!x ls. (set ls = {x}) <=> ls <> [] /\ EVERY ($= x) ls`,
   GEN_TAC
   >> Induct
   >> simp[]
   >> simp[Once EXTENSION,EVERY_MEM]
   >> metis_tac[])

val REPLICATE_GENLIST = Q.store_thm("REPLICATE_GENLIST",
   `!n x. REPLICATE n x = GENLIST (K x) n`,
   Induct THEN SRW_TAC[][REPLICATE,GENLIST_CONS])

val EL_REPLICATE = Q.store_thm ("EL_REPLICATE",
   `!n1 n2 x. n1 < n2 ==> (EL n1 (REPLICATE n2 x) = x)`,
   Induct_on `n2`
   >> rw []
   >> Cases_on `n1 = n2`
   >> fs [REPLICATE, EL]
   >> Cases_on `n1`
   >> rw []
   >> fs [REPLICATE, EL]);

Theorem EVERY_REPLICATE[simp]:
   !f n x. EVERY f (REPLICATE n x) <=> (n = 0) \/ f x
Proof Induct_on `n` >> rw [] >> metis_tac []
QED

(* ALL_DISTINCT_DROP is already in listTheory *)
Theorem ALL_DISTINCT_TAKE :
    !ls n. ALL_DISTINCT ls ==> ALL_DISTINCT (TAKE n ls)
Proof
    Induct >> simp[TAKE_def] >> rw[]
 >> METIS_TAC [MEM_TAKE]
QED

Theorem ALL_DISTINCT_FRONT :
    !l. l <> [] /\ ALL_DISTINCT l ==> ALL_DISTINCT (FRONT l)
Proof
    rpt STRIP_TAC
 >> ‘ALL_DISTINCT l = ALL_DISTINCT (SNOC (LAST l) (FRONT l))’
      by rw [SNOC_LAST_FRONT]
 >> FULL_SIMP_TAC std_ss [ALL_DISTINCT_SNOC]
QED

val MAP_SND_FILTER_NEQ = Q.store_thm("MAP_SND_FILTER_NEQ",
   `MAP SND (FILTER (\(x,y). y <> z) ls) = FILTER ($<> z) (MAP SND ls)`,
   Q.ISPECL_THEN [`$<> z`, `SND:('b#'a)->'a`, `ls`] MP_TAC FILTER_MAP
   >> rw[]
   >> AP_TERM_TAC
   >> AP_THM_TAC
   >> AP_TERM_TAC
   >> simp[FUN_EQ_THM,FORALL_PROD,EQ_IMP_THM])

val MEM_SING_APPEND = Q.store_thm("MEM_SING_APPEND",
   `(!a c. d <> a ++ [b] ++ c) <=> ~MEM b d`,
   rw[EQ_IMP_THM]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> fs[]
   >> fs[MEM_EL]
   >> FIRST_X_ASSUM(Q.SPECL_THEN[`TAKE n d`,`DROP (n+1) d`]MP_TAC)
   >> rw[LIST_EQ_REWRITE]
   >> Cases_on`x<n`
   >> simp[EL_APPEND1,EL_TAKE]
   >> Cases_on`x=n`
   >> simp[EL_APPEND1,EL_APPEND2,EL_TAKE]
   >> simp[EL_DROP])

val EL_LENGTH_APPEND_rwt = Q.store_thm("EL_LENGTH_APPEND_rwt",
   `~NULL l2 /\ (n = LENGTH l1) ==> (EL n (l1++l2) = HD l2)`,
   metis_tac[EL_LENGTH_APPEND])

val MAP_FST_funs = Q.store_thm("MAP_FST_funs",
   `MAP (\(x,y,z). x) funs = MAP FST funs`,
   rw[MAP_EQ_f,FORALL_PROD])

val TAKE_PRE_LENGTH = Q.store_thm("TAKE_PRE_LENGTH",
   `!ls. ls <> [] ==> (TAKE (PRE (LENGTH ls)) ls = FRONT ls)`,
   Induct
   THEN SRW_TAC[][LENGTH_NIL,TAKE_def]
   THEN FULL_SIMP_TAC(srw_ss())[FRONT_DEF,PRE_SUB1])

val DROP_LENGTH_NIL_rwt = Q.store_thm("DROP_LENGTH_NIL_rwt",
   `!l m. (m = LENGTH l) ==> (DROP m l = [])`,
   rw[DROP_LENGTH_NIL])

val DROP_EL_CONS = Q.store_thm("DROP_EL_CONS",
   `!ls n. n < LENGTH ls ==> (DROP n ls = EL n ls :: DROP (n + 1) ls)`,
   Induct
   >> rw[EL_CONS,PRE_SUB1,DROP_def]
   >> FULL_SIMP_TAC arith_ss []
   >> `0 < n` by RW_TAC arith_ss []
   >> rw [EL_CONS, PRE_SUB1]);

val TAKE_EL_SNOC = Q.store_thm("TAKE_EL_SNOC",
   `!ls n. n < LENGTH ls ==> (TAKE (n + 1) ls = SNOC (EL n ls) (TAKE n ls))`,
   HO_MATCH_MP_TAC SNOC_INDUCT
   THEN CONJ_TAC
   THEN1 SRW_TAC[][]
   THEN REPEAT STRIP_TAC
   THEN Cases_on`n = LENGTH ls`
   THEN1 (rw[EL_LENGTH_SNOC,TAKE_SNOC,TAKE_APPEND1,EL_APPEND1,EL_APPEND2,
             TAKE_APPEND2]
          THEN FULL_SIMP_TAC arith_ss [])
   THEN `n < LENGTH ls` by FULL_SIMP_TAC arith_ss [ADD1, LENGTH_SNOC]
   THEN rw[TAKE_SNOC,TAKE_APPEND1,EL_APPEND1]
   THEN FULL_SIMP_TAC arith_ss [ADD1, LENGTH_SNOC, TAKE_APPEND1, SNOC_APPEND])

val REVERSE_DROP = Q.store_thm("REVERSE_DROP",
   `!ls n. n <= LENGTH ls ==>
           (REVERSE (DROP n ls) = REVERSE (LASTN (LENGTH ls - n) ls))`,
   HO_MATCH_MP_TAC SNOC_INDUCT
   THEN SRW_TAC[][LASTN]
   THEN Cases_on`n = SUC (LENGTH ls)`
   THEN1 (rw[DROP_LENGTH_NIL_rwt,ADD1,LASTN])
   THEN `n <= LENGTH ls` by RW_TAC arith_ss []
   THEN rw[DROP_APPEND1,LASTN_APPEND1]
   THEN `LENGTH [x] <= LENGTH ls + 1 - n` by RW_TAC arith_ss [LENGTH]
   THEN RW_TAC arith_ss [LASTN_APPEND1, LENGTH]);

val LENGTH_FILTER_LESS = Q.store_thm("LENGTH_FILTER_LESS",
   `!P ls. EXISTS ($~ o P) ls ==> LENGTH (FILTER P ls) < LENGTH ls`,
   GEN_TAC
   THEN Induct
   THEN SRW_TAC[][]
   THEN MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC
   THEN MATCH_ACCEPT_TAC LENGTH_FILTER_LEQ)

val EVERY2_APPEND = save_thm(
  "EVERY2_APPEND", LIST_REL_APPEND);

val EVERY2_APPEND_suff = save_thm(
  "EVERY2_APPEND_suff", LIST_REL_APPEND_suff);

Theorem EVERY2_DROP:
  !R l1 l2 n.
    EVERY2 R l1 l2 ==> EVERY2 R (DROP n l1) (DROP n l2)
Proof
  Induct_on ‘n’ >> simp[] >> Induct_on ‘l1’ >> dsimp[]
QED

Theorem EVERY2_TAKE:
  !P xs ys n. EVERY2 P xs ys ==> EVERY2 P (TAKE n xs) (TAKE n ys)
Proof
  Induct_on ‘n’ >> simp[] >> Induct_on ‘xs’ >>
  asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) []
QED

Theorem LIST_REL_APPEND_SING[simp]:
  LIST_REL R (l1 ++ [x1]) (l2 ++ [x2]) <=> LIST_REL R l1 l2 /\ R x1 x2
Proof
  simp_tac (srw_ss() ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss)
           [LIST_REL_EL_EQN, EL_APPEND1, EL_APPEND2,
            ARITH_PROVE “x < y + 1 <=> x = y \/ x < y”,
            AC CONJ_COMM CONJ_ASSOC]
QED

val LIST_REL_GENLIST = store_thm("LIST_REL_GENLIST",
  ``EVERY2 P (GENLIST f l) (GENLIST g l) <=>
    !i. i < l ==> P (f i) (g i)``,
  Induct_on `l`
  >> fs [GENLIST,LIST_REL_APPEND_SING,SNOC_APPEND]
  >> fs [DECIDE ``i < SUC n <=> i < n \/ (i = n)``] >> METIS_TAC []);

val ALL_DISTINCT_MEM_ZIP_MAP = Q.store_thm("ALL_DISTINCT_MEM_ZIP_MAP",
   `!f x ls.
     ALL_DISTINCT ls ==>
     (MEM x (ZIP (ls, MAP f ls)) <=> MEM (FST x) ls /\ (SND x = f (FST x)))`,
   GEN_TAC
   THEN Cases
   THEN SRW_TAC[][MEM_ZIP,FORALL_PROD]
   THEN SRW_TAC[][EQ_IMP_THM]
   THEN SRW_TAC[][EL_MAP,MEM_EL]
   THEN FULL_SIMP_TAC (srw_ss()) [EL_ALL_DISTINCT_EL_EQ,MEM_EL]
   THEN METIS_TAC[EL_MAP])

val REVERSE_ZIP = Q.store_thm("REVERSE_ZIP",
   `!l1 l2. (LENGTH l1 = LENGTH l2) ==>
            (REVERSE (ZIP (l1,l2)) = ZIP (REVERSE l1, REVERSE l2))`,
   Induct
   THEN SRW_TAC[][LENGTH_NIL_SYM]
   THEN Cases_on `l2`
   THEN FULL_SIMP_TAC(srw_ss())[]
   THEN SRW_TAC[][GSYM ZIP_APPEND])

Theorem EVERY2_REVERSE1:
   !l1 l2. EVERY2 R l1 (REVERSE l2) <=> EVERY2 R (REVERSE l1) l2
Proof
   REPEAT GEN_TAC
   >> EQ_TAC
   >> simp[EVERY2_EVERY]
   >> REPEAT STRIP_TAC
   >> drule (iffRL EVERY_REVERSE)
   >> simp[REVERSE_ZIP, Excl "EVERY_REVERSE"]
QED

val LIST_REL_REVERSE_EQ = Q.store_thm(
  "LIST_REL_REVERSE_EQ[simp]",
  ‘LIST_REL R (REVERSE l1) (REVERSE l2) <=> LIST_REL R l1 l2’,
  simp[EVERY2_REVERSE1]);

val every_count_list = Q.store_thm ("every_count_list",
   `!P n. EVERY P (COUNT_LIST n) = (!m. m < n ==> P m)`,
   Induct_on `n`
   >> rw [COUNT_LIST_def, EVERY_MAP]
   >> EQ_TAC
   >> rw []
   >> Cases_on `m`
   >> rw []
   >> `n' < n` by RW_TAC arith_ss []
   >> metis_tac []);

val count_list_sub1 = Q.store_thm ("count_list_sub1",
   `!n. n <> 0 ==> (COUNT_LIST n = 0::MAP SUC (COUNT_LIST (n - 1)))`,
   Induct_on `n` >> ONCE_REWRITE_TAC [COUNT_LIST_def] >> fs []);

val el_map_count = Q.store_thm ("el_map_count",
   `!n f m. n < m ==> (EL n (MAP f (COUNT_LIST m)) = f n)`,
   Induct_on `n`
   >> rw []
   >> Cases_on `m`
   >> fs [COUNT_LIST_def]
   >> `n < SUC n'` by RW_TAC arith_ss []
   >> RES_TAC
   >> fs [COUNT_LIST_def]
   >> POP_ASSUM (fn _ => ALL_TAC)
   >> POP_ASSUM (MP_TAC o GSYM o Q.SPEC `f o SUC`)
   >> rw [MAP_MAP_o]);

val ZIP_COUNT_LIST = Q.store_thm("ZIP_COUNT_LIST",
   `(n = LENGTH l1) ==>
    (ZIP (l1,COUNT_LIST n) = GENLIST (\n. (EL n l1, n)) (LENGTH l1))`,
   simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_ZIP,EL_COUNT_LIST])

Theorem map_replicate[simp]:
   !f n x. MAP f (REPLICATE n x) = REPLICATE n (f x)
Proof Induct_on `n` >> rw [REPLICATE]
QED

Theorem REPLICATE_NIL[simp]:  REPLICATE x y = [] <=> x = 0
Proof Cases_on`x` >> rw[]
QED

val REPLICATE_APPEND = Q.store_thm("REPLICATE_APPEND",
  `REPLICATE n a ++ REPLICATE m a = REPLICATE (n+m) a`,
  simp[LIST_EQ_REWRITE,LENGTH_REPLICATE] >> rw[] >>
  Cases_on`x < n` >> simp[EL_APPEND1,LENGTH_REPLICATE,EL_REPLICATE,EL_APPEND2])

Theorem DROP_REPLICATE[simp]:
  DROP n (REPLICATE m a) = REPLICATE (m-n) a
Proof simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,EL_REPLICATE,EL_DROP]
QED

Theorem LIST_REL_REPLICATE_same:
  LIST_REL P (REPLICATE n x) (REPLICATE n y) <=> (0 < n ==> P x y)
Proof
  Induct_on ‘n’>> asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss)[]
QED

Theorem SNOC_REPLICATE[simp]:
  !n x. SNOC x (REPLICATE n x) = REPLICATE (SUC n) x
Proof  Induct \\ fs [REPLICATE]
QED

Theorem REVERSE_REPLICATE[simp]:
  !n x. REVERSE (REPLICATE n x) = REPLICATE n x
Proof
  Induct \\ fs [REPLICATE] \\ fs [GSYM REPLICATE,GSYM SNOC_REPLICATE]
QED

Theorem SUM_REPLICATE[simp]:
  !n k. SUM (REPLICATE n k) = n * k
Proof
  Induct >>
  full_simp_tac(srw_ss())[REPLICATE,MULT_CLAUSES,AC ADD_COMM ADD_ASSOC]
QED

Theorem LENGTH_FLAT_REPLICATE[simp]:
  !n. LENGTH (FLAT (REPLICATE n ls)) = n * LENGTH ls
Proof  Induct >> simp[REPLICATE,MULT]
QED

val take_drop_partition = Q.store_thm ("take_drop_partition",
   `!n m l. m <= n ==> (TAKE m l ++ TAKE (n - m) (DROP m l) = TAKE n l)`,
   Induct_on `m`
   >> rw []
   >> Cases_on `l`
   >> rw [TAKE_def]
   THEN1 RW_TAC arith_ss []
   >> FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n - 1`, `t`])
   >> rw []
   >> FULL_SIMP_TAC arith_ss [ADD1]);

val all_distinct_count_list = Q.store_thm ("all_distinct_count_list",
   `!n. ALL_DISTINCT (COUNT_LIST n)`,
   Induct_on `n`
   >> rw [COUNT_LIST_def, MEM_MAP]
   >> MATCH_MP_TAC ALL_DISTINCT_MAP_INJ
   >> rw []);

Theorem list_rel_lastn:
  !f l1 l2 n.
    n <= LENGTH l1 /\ LIST_REL f l1 l2 ==>
    LIST_REL f (LASTN n l1) (LASTN n l2)
Proof
  simp[LASTN_DROP_UNCOND] >> rpt strip_tac >>
  drule LIST_REL_LENGTH >> simp[EVERY2_DROP]
QED

Theorem list_rel_butlastn:
  !f l1 l2 n.
    n <= LENGTH l1 /\ LIST_REL f l1 l2 ==>
    LIST_REL f (BUTLASTN n l1) (BUTLASTN n l2)
Proof
  rpt strip_tac >> drule_then assume_tac LIST_REL_LENGTH >>
  simp[BUTLASTN_TAKE, EVERY2_TAKE]
QED

end
(* end CakeML lemmas *)

local open listTheory in

Theorem nub_GENLIST:
  nub (GENLIST f n) =
    MAP f (FILTER (\i. !j. (i < j) /\ (j < n) ==> f i <> f j) (COUNT_LIST n))
Proof
  simp[COUNT_LIST_GENLIST]
  \\ Q.ID_SPEC_TAC`f`
  \\ Induct_on`n` \\ simp[]
  \\ simp[GENLIST_CONS]
  \\ simp[nub_def]
  \\ gen_tac
  \\ simp[MEM_GENLIST]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`COND b1`
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`MAP f (COND b2 _ _)`
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`f 0 :: r1`
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`0 :: r2`
  \\ `b2 = ~b1`
  by (
    rw[Abbr`b1`, Abbr`b2`, EQ_IMP_THM]
    >- (
      CCONTR_TAC \\ fs[]
      \\ first_x_assum(Q.SPEC_THEN`SUC m`mp_tac)
      \\ simp[] )
    \\ first_x_assum(Q.SPEC_THEN`PRE j`mp_tac)
    \\ simp[]
    \\ metis_tac[SUC_PRE] )
  \\ `r1 = MAP f r2`
  by (
    simp[Abbr`r1`, Abbr`r2`]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC`FILTER f2`
    \\ `f2 = (\i. !j. i <= j /\ (j < n) ==> f i <> f (SUC j)) o SUC`
    by (
      simp[Abbr`f2`, FUN_EQ_THM]
      \\ simp[LESS_EQ] )
    \\ simp[GSYM MAP_MAP_o, GSYM FILTER_MAP]
    \\ simp[MAP_GENLIST]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ simp[FUN_EQ_THM]
    \\ gen_tac
    \\ CONV_TAC(RAND_CONV(Ho_Rewrite.ONCE_REWRITE_CONV[FORALL_NUM]))
    \\ simp[LESS_EQ] )
  \\ rw[]
QED

end

(* alternative definition of UNIQUE *)
val UNIQUE_LIST_ELEM_COUNT = store_thm (
   "UNIQUE_LIST_ELEM_COUNT", ``!e L. UNIQUE e L = (LIST_ELEM_COUNT e L = 1)``,
    rpt GEN_TAC
 >> REWRITE_TAC [LIST_ELEM_COUNT_DEF]
 >> Q_TAC KNOW_TAC `(\x. x = e) = ($= e)`
 >- ( REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC >> BETA_TAC \\
      METIS_TAC [] )
 >> DISCH_TAC >> ASM_REWRITE_TAC []
 >> RW_TAC std_ss [UNIQUE_LENGTH_FILTER]);

Theorem LIST_ELEM_COUNT_CARD_EL:
  !ls. LIST_ELEM_COUNT x ls = CARD { n | n < LENGTH ls /\ (EL n ls = x) }
Proof
  Induct
  \\ rw[LIST_ELEM_COUNT_THM]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`_ = CARD B`
  \\ Q.MATCH_ASMSUB_ABBREV_TAC`_ = CARD A`
  \\ `A SUBSET count (LENGTH ls)` by simp[Abbr`A`, SUBSET_DEF]
  \\ `B SUBSET count (SUC (LENGTH ls))` by simp[Abbr`B`, SUBSET_DEF]
  \\ `FINITE A /\ FINITE B` by metis_tac[SUBSET_FINITE, FINITE_COUNT]
  \\ `B = IMAGE SUC A UNION (if x = h then {0} else {})`
    by ( simp[Abbr`A`, Abbr`B`, EXTENSION] \\ Cases \\ rw[] )
  \\ Cases_on`x = h`
  \\ simp[LIST_ELEM_COUNT_THM, CARD_UNION_EQN, ADD1, CARD_INJ_IMAGE]
  \\ `IMAGE SUC A INTER {0} = {}` by rw[EXTENSION]
  \\ simp[]
QED

(*---------------------------------------------------------------------------*)
(* Add evaluation theorems to computeLib.the_compset                         *)
(*---------------------------------------------------------------------------*)

val COUNT_LIST_AUX = Q.prove(
   `!n l1 l2. COUNT_LIST_AUX n l1 ++ l2 = COUNT_LIST_AUX n (l1 ++ l2)`,
   Induct THEN SRW_TAC [] [COUNT_LIST_AUX_def]);

val COUNT_LIST_compute = Q.store_thm ("COUNT_LIST_compute",
   `!n. COUNT_LIST n = COUNT_LIST_AUX n []`,
   Induct
   THEN SRW_TAC [] [COUNT_LIST_GENLIST, GENLIST, COUNT_LIST_AUX_def]
   THEN FULL_SIMP_TAC (srw_ss()) [COUNT_LIST_GENLIST, COUNT_LIST_AUX]);

val SPLITP_AUX_lem1 = Q.prove(
   `!P acc l h.
     ~P h ==> (h::FST (SPLITP_AUX acc P l) = FST (SPLITP_AUX (h::acc) P l))`,
   Induct_on `l` THEN SRW_TAC [] [SPLITP_AUX_def]);

val SPLITP_AUX_lem2 = Q.prove(
   `!P acc1 acc2 l. SND (SPLITP_AUX acc1 P l) = SND (SPLITP_AUX acc2 P l)`,
   Induct_on `l` THEN SRW_TAC [] [SPLITP_AUX_def]);

val SPLITP_AUX = Q.prove(
   `!P l. SPLITP P l = SPLITP_AUX [] P l`,
   Induct_on `l`
   THEN SRW_TAC [] [SPLITP_AUX_def, SPLITP, SPLITP_AUX_lem1]
   THEN metisLib.METIS_TAC [SPLITP_AUX_lem2, pairTheory.PAIR]);

val SPLITP_compute = save_thm ("SPLITP_compute",
   REWRITE_RULE [GSYM FUN_EQ_THM] SPLITP_AUX);

val IS_SUFFIX_compute = save_thm ("IS_SUFFIX_compute", GSYM IS_PREFIX_REVERSE);

val SEG_compute = save_thm ("SEG_compute", numLib.SUC_RULE SEG);

val BUTLASTN_compute = Q.store_thm ("BUTLASTN_compute",
   `!n l.
      BUTLASTN n l =
      let m = LENGTH l in
        if n <= m then TAKE (m - n) l
        else FAIL BUTLASTN ^(mk_var ("longer than list", bool)) n l`,
   SRW_TAC [boolSimps.LET_ss] [combinTheory.FAIL_THM, BUTLASTN_TAKE]);

val LASTN_compute = Q.store_thm ("LASTN_compute",
   `!n l.
      LASTN n l =
      let m = LENGTH l in
        if n <= m then DROP (m - n) l
        else FAIL LASTN ^(mk_var ("longer than list", bool)) n l`,
   SRW_TAC [boolSimps.LET_ss] [combinTheory.FAIL_THM, LASTN_DROP]);

(* ======================================================================== *)

local
   fun alias (s1, s2) =
      let
         val tm = Term.prim_mk_const {Thy = "list", Name = s2}
      in
         Parse.overload_on (s1, tm); Parse.overload_on (s2, tm)
      end
   val mem_t = ``\x:'a l:'a list. x IN LIST_TO_SET l``
in
   val () = List.app alias
     [("ALL_EL", "EVERY"),
      ("SOME_EL", "EXISTS"),
      ("FIRSTN", "TAKE"),
      ("BUTFIRSTN", "DROP"),
      ("BUTLAST", "FRONT")]
   val _ = overload_on("IS_EL", mem_t)
   val _ = overload_on("MEM", mem_t)
end

(* moved here from examples/CCS/CCSScript.sml, originally by Chun Tian *)
Definition DELETE_ELEMENT :
    (DELETE_ELEMENT e [] = []) /\
    (DELETE_ELEMENT e (x :: l) = if (e = x) then DELETE_ELEMENT e l
                                 else x :: DELETE_ELEMENT e l)
End

Theorem NOT_IN_DELETE_ELEMENT :
    !e L. ~MEM e (DELETE_ELEMENT e L)
Proof
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT, MEM]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT]
 >> Cases_on `e = h` >> fs []
QED

Theorem DELETE_ELEMENT_FILTER :
    !e L. DELETE_ELEMENT e L = FILTER ((<>) e) L
Proof
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT, FILTER]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT, FILTER]
 >> Cases_on `e = h` >> fs []
QED

Theorem LENGTH_DELETE_ELEMENT_LEQ :
    !e L. LENGTH (DELETE_ELEMENT e L) <= LENGTH L
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> MP_TAC (Q.SPECL [`\y. e <> y`, `\y. T`] LENGTH_FILTER_LEQ_MONO)
 >> BETA_TAC >> simp []
QED

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;

Theorem LENGTH_DELETE_ELEMENT_LE :
    !e L. MEM e L ==> LENGTH (DELETE_ELEMENT e L) < LENGTH L
Proof
    rpt GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [MEM]
 >> GEN_TAC >> REWRITE_TAC [MEM, DELETE_ELEMENT]
 >> Cases_on `e = h` >> fs []
 >> MP_TAC (Q.SPECL [`h`, `L`] LENGTH_DELETE_ELEMENT_LEQ)
 >> KILL_TAC >> RW_TAC arith_ss []
QED

Theorem EVERY_DELETE_ELEMENT :
    !e L P. P e /\ EVERY P (DELETE_ELEMENT e L) ==> EVERY P L
Proof
    GEN_TAC >> Induct_on `L`
 >- RW_TAC std_ss [DELETE_ELEMENT]
 >> rpt GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT]
 >> Cases_on `e = h` >> fs []
QED

Theorem DELETE_ELEMENT_APPEND :
    !a L L'. DELETE_ELEMENT a (L ++ L') =
             DELETE_ELEMENT a L ++ DELETE_ELEMENT a L'
Proof
    REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> REWRITE_TAC [GSYM FILTER_APPEND_DISTRIB]
QED

(* ------------------------------------------------------------------------ *)

local
   val alias =
      [
       ("ALL_EL_BUTFIRSTN", "EVERY_DROP"),
       ("ALL_EL_BUTLASTN", "EVERY_BUTLASTN"),
       ("ALL_EL_FIRSTN", "EVERY_TAKE"),
       ("ALL_EL_FOLDL", "EVERY_FOLDL"),
       ("ALL_EL_FOLDL_MAP", "EVERY_FOLDL_MAP"),
       ("ALL_EL_FOLDR", "EVERY_FOLDR"),
       ("ALL_EL_FOLDR_MAP", "EVERY_FOLDR_MAP"),
       ("ALL_EL_LASTN", "EVERY_LASTN"),
       ("ALL_EL_REPLICATE", "EVERY_REPLICATE"),
       ("ALL_EL_REVERSE", "EVERY_REVERSE"),
       ("ALL_EL_SEG", "EVERY_SEG"),
       ("APPEND_BUTLASTN_BUTFIRSTN", "APPEND_BUTLASTN_DROP"),
       ("APPEND_FIRSTN_LASTN", "APPEND_TAKE_LASTN"),
       ("BUTFIRSTN", "DROP"),
       ("BUTFIRSTN_APPEND1", "DROP_APPEND1"),
       ("BUTFIRSTN_APPEND2", "DROP_APPEND2"),
       ("BUTFIRSTN_BUTFIRSTN", "DROP_DROP"),
       ("BUTFIRSTN_CONS_EL", "DROP_CONS_EL"),
       ("BUTFIRSTN_LASTN", "DROP_LASTN"),
       ("BUTFIRSTN_LENGTH_APPEND", "DROP_LENGTH_APPEND"),
       ("BUTFIRSTN_LENGTH_NIL", "DROP_LENGTH_NIL"),
       ("BUTFIRSTN_REVERSE", "DROP_REVERSE"),
       ("BUTFIRSTN_SEG", "DROP_SEG"),
       ("BUTFIRSTN_SNOC", "DROP_SNOC"),
       ("BUTLASTN_BUTLAST", "BUTLASTN_FRONT"),
       ("BUTLASTN_FIRSTN", "BUTLASTN_TAKE"),
       ("BUTLASTN_SUC_BUTLAST", "BUTLASTN_SUC_FRONT"),
       ("ELL_IS_EL", "ELL_MEM"),
       ("EL_BUTFIRSTN", "EL_DROP"),
       ("EL_FIRSTN", "EL_TAKE"),
       ("EL_IS_EL", "EL_MEM"),
       ("FIRSTN", "TAKE"),
       ("FIRSTN_APPEND1", "TAKE_APPEND1"),
       ("FIRSTN_APPEND2", "TAKE_APPEND2"),
       ("FIRSTN_BUTLASTN", "TAKE_BUTLASTN"),
       ("FIRSTN_FIRSTN", "TAKE_TAKE"),
       ("FIRSTN_LENGTH_APPEND", "TAKE_LENGTH_APPEND"),
       ("FIRSTN_REVERSE", "TAKE_REVERSE"),
       ("FIRSTN_SEG", "TAKE_SEG"),
       ("FIRSTN_SNOC", "TAKE_SNOC"),
       ("IS_EL_BUTFIRSTN", "MEM_DROP_IMP"),
       ("IS_EL_BUTLASTN", "MEM_BUTLASTN"),
       ("IS_EL_DEF", "MEM_EXISTS"),
       ("IS_EL_FIRSTN", "MEM_TAKE"),
       ("IS_EL_FOLDL", "MEM_FOLDL"),
       ("IS_EL_FOLDL_MAP", "MEM_FOLDL_MAP"),
       ("IS_EL_FOLDR", "MEM_FOLDR"),
       ("IS_EL_FOLDR_MAP", "MEM_FOLDR_MAP"),
       ("IS_EL_LASTN", "MEM_LASTN"),
       ("IS_EL_REPLICATE", "MEM_REPLICATE"),
       ("IS_EL_SEG", "MEM_SEG"),
       ("IS_EL_SOME_EL", "MEM_EXISTS"),
       ("LASTN_BUTFIRSTN", "LASTN_DROP"),
       ("LENGTH_BUTLAST", "LENGTH_FRONT"),
       ("SNOC_EL_FIRSTN", "SNOC_EL_TAKE"),
       ("SOME_EL_BUTFIRSTN", "EXISTS_DROP"),
       ("SOME_EL_BUTLASTN", "EXISTS_BUTLASTN"),
       ("SOME_EL_DISJ", "EXISTS_DISJ"),
       ("SOME_EL_FIRSTN", "EXISTS_TAKE"),
       ("SOME_EL_FOLDL", "EXISTS_FOLDL"),
       ("SOME_EL_FOLDL_MAP", "EXISTS_FOLDL_MAP"),
       ("SOME_EL_FOLDR", "EXISTS_FOLDR"),
       ("SOME_EL_FOLDR_MAP", "EXISTS_FOLDR_MAP"),
       ("SOME_EL_LASTN", "EXISTS_LASTN"),
       ("SOME_EL_REVERSE", "EXISTS_REVERSE"),
       ("SOME_EL_SEG", "EXISTS_SEG"),
       ("ZIP_FIRSTN", "ZIP_TAKE"),
       ("ZIP_FIRSTN_LEQ", "ZIP_TAKE_LEQ")
      ]
   val moved =
      [
       ("ALL_DISTINCT_SNOC", "ALL_DISTINCT_SNOC"),
       ("ALL_EL", "EVERY_DEF"),
       ("ALL_EL_APPEND", "EVERY_APPEND"),
       ("ALL_EL_CONJ", "EVERY_CONJ"),
       ("ALL_EL_SNOC", "EVERY_SNOC"),
       ("APPEND", "APPEND"),
       ("APPEND_11_LENGTH", "APPEND_11_LENGTH"),
       ("APPEND_ASSOC", "APPEND_ASSOC"),
       ("APPEND_BUTLAST_LAST", "APPEND_FRONT_LAST"),
       ("APPEND_FIRSTN_BUTFIRSTN", "TAKE_DROP"),
       ("APPEND_LENGTH_EQ", "APPEND_LENGTH_EQ"),
       ("APPEND_SNOC", "APPEND_SNOC"),
       ("BUTLAST", "FRONT_SNOC"),
       ("BUTLAST_CONS", "FRONT_CONS"),
       ("CONS", "CONS"),
       ("CONS_11", "CONS_11"),
       ("EL", "EL"),
       ("EL_DROP", "EL_DROP"),
       ("EL_GENLIST", "EL_GENLIST"),
       ("EL_LENGTH_SNOC", "EL_LENGTH_SNOC"),
       ("EL_MAP", "EL_MAP"),
       ("EL_REVERSE", "EL_REVERSE"),
       ("EL_SNOC", "EL_SNOC"),
       ("EL_TAKE", "EL_TAKE"),
       ("EQ_LIST", "EQ_LIST"),
       ("EVERY_GENLIST", "EVERY_GENLIST"),
       ("EXISTS_GENLIST", "EXISTS_GENLIST"),
       ("FILTER", "FILTER"),
       ("FILTER_APPEND", "FILTER_APPEND_DISTRIB"),
       ("FILTER_REVERSE", "FILTER_REVERSE"),
       ("FIRSTN_LENGTH_ID", "TAKE_LENGTH_ID"),
       ("FLAT", "FLAT"),
       ("FLAT_APPEND", "FLAT_APPEND"),
       ("FOLDL", "FOLDL"),
       ("FOLDL_SNOC", "FOLDL_SNOC"),
       ("FOLDR", "FOLDR"),
       ("GENLIST", "GENLIST"),
       ("GENLIST_APPEND", "GENLIST_APPEND"),
       ("GENLIST_CONS", "GENLIST_CONS"),
       ("GENLIST_FUN_EQ", "GENLIST_FUN_EQ"),
       ("HD", "HD"),
       ("HD_GENLIST", "HD_GENLIST"),
       ("IS_EL", "MEM"),
       ("IS_EL_APPEND", "MEM_APPEND"),
       ("IS_EL_FILTER", "MEM_FILTER"),
       ("IS_EL_REVERSE", "MEM_REVERSE"),
       ("IS_EL_SNOC", "MEM_SNOC"),
       ("LAST", "LAST_SNOC"),
       ("LAST_APPEND", "LAST_APPEND_CONS"),
       ("LAST_CONS", "LAST_CONS"),
       ("LENGTH", "LENGTH"),
       ("LENGTH_APPEND", "LENGTH_APPEND"),
       ("LENGTH_BUTFIRSTN", "LENGTH_DROP"),
       ("LENGTH_CONS", "LENGTH_CONS"),
       ("LENGTH_EQ_NIL", "LENGTH_EQ_NIL"),
       ("LENGTH_FIRSTN", "LENGTH_TAKE"),
       ("LENGTH_GENLIST", "LENGTH_GENLIST"),
       ("LENGTH_MAP", "LENGTH_MAP"),
       ("LENGTH_NIL", "LENGTH_NIL"),
       ("LENGTH_REVERSE", "LENGTH_REVERSE"),
       ("LENGTH_SNOC", "LENGTH_SNOC"),
       ("LENGTH_ZIP", "LENGTH_ZIP"),
       ("LIST_NOT_EQ", "LIST_NOT_EQ"),
       ("MAP", "MAP"),
       ("MAP2", "MAP2"),
       ("MAP2_ZIP", "MAP2_ZIP"),
       ("MAP_APPEND", "MAP_APPEND"),
       ("MAP_EQ_f", "MAP_EQ_f"),
       ("MAP_GENLIST", "MAP_GENLIST"),
       ("MAP_MAP_o", "MAP_MAP_o"),
       ("MAP_SNOC", "MAP_SNOC"),
       ("MAP_o", "MAP_o"),
       ("NOT_ALL_EL_SOME_EL", "NOT_EVERY"),
       ("NOT_CONS_NIL", "NOT_CONS_NIL"),
       ("NOT_EQ_LIST", "NOT_EQ_LIST"),
       ("NOT_NIL_CONS", "NOT_NIL_CONS"),
       ("NOT_SOME_EL_ALL_EL", "NOT_EXISTS"),
       ("NULL", "NULL"),
       ("NULL_DEF", "NULL_DEF"),
       ("NULL_EQ_NIL", "NULL_EQ"),
    (* removed due to conflicts with Tactical.REVERSE:
       ("REVERSE", "REVERSE_SNOC_DEF"),
     *)
       ("REVERSE_APPEND", "REVERSE_APPEND"),
       ("REVERSE_EQ_NIL", "REVERSE_EQ_NIL"),
       ("REVERSE_REVERSE", "REVERSE_REVERSE"),
       ("REVERSE_SNOC", "REVERSE_SNOC"),
       ("SNOC", "SNOC"),
       ("SNOC_11", "SNOC_11"),
       ("SNOC_APPEND", "SNOC_APPEND"),
       ("SNOC_Axiom", "SNOC_Axiom"),
       ("SNOC_CASES", "SNOC_CASES"),
       ("SNOC_INDUCT", "SNOC_INDUCT"),
       ("SOME_EL", "EXISTS_DEF"),
       ("SOME_EL_APPEND", "EXISTS_APPEND"),
       ("SOME_EL_MAP", "EXISTS_MAP"),
       ("SOME_EL_SNOC", "EXISTS_SNOC"),
       ("SUM", "SUM"),
       ("SUM_APPEND", "SUM_APPEND"),
       ("SUM_SNOC", "SUM_SNOC"),
       ("TL", "TL"),
       ("TL_GENLIST", "TL_GENLIST"),
       ("UNZIP", "UNZIP"),
       ("UNZIP_ZIP", "UNZIP_ZIP"),
       ("ZIP", "ZIP"),
       ("ZIP_GENLIST", "ZIP_GENLIST"),
       ("ZIP_UNZIP", "ZIP_UNZIP")
      ]
   val B = PP.block PP.CONSISTENT 0
in
   val () = Theory.adjoin_to_theory {
      sig_ps = SOME
        (fn _ =>
           let
              fun S s = PP.add_string ("val " ^ s ^ " : thm")
           in
             B (
               [PP.add_string "(* Aliases for legacy theorem names *)", PP.NL] @
               PP.pr_list S [PP.add_break(1,0)]
                          (Lib.sort (Lib.curry String.<)
                                    (List.map fst (alias @ moved)))
             )
           end),
      struct_ps = SOME
        (fn _ =>
           let
              fun S p (s1, s2) =
                PP.add_string ("val " ^ s1 ^ " = " ^ p ^ s2)
              fun L p l = B (PP.pr_list (S p) [PP.NL] l)
           in
              B [L "listTheory." moved, PP.add_break(1,0), L "" alias]
           end)}
end

(* ------------------------------------------------------------------------ *)

val () = computeLib.add_persistent_funs
   [
    "BUTLASTN_compute",
    "COUNT_LIST_compute",
    "IS_SUBLIST",
    "IS_SUFFIX_compute",
    "LASTN_compute",
    "SEG_compute",
    "SPLITP_compute"
   ]

(*

val conv = EVAL

   conv ``AND_EL [T;T;T]``;
   conv ``BUTLASTN 3 [1n;2;3;4;5]``;
   conv ``COUNT_LIST 4``;
   conv ``ELL 4 [1n;2;3;4;5;6]``;
   conv ``IS_SUBLIST [1n;2;3;4;5] [2;3]``;
   conv ``IS_SUFFIX [1n;2;3;4;5] [4;5]``;
   conv ``LASTN 3 [1n;2;3;4;5]``;
   conv ``LIST_ELEM_COUNT 2 [1n;2;2;3]``;
   conv ``OR_EL [T;F;T]``;
   conv ``PREFIX (\x. x < 4) [1n;2;3;4;5;6]``;
   conv ``REPLICATE 4 [1n;2;3;4;5;6]``;
   conv ``SCANL (+) 1 [1n;2;3;4;5;6]``;
   conv ``SCANR (+) 1 [1n;2;3;4;5;6]``;
   conv ``SEG 2 3 [1n;2;3;4;5]``;
   conv ``SPLITL (\x. x > 4) [1n;2;3;4;5;6]``;
   conv ``SPLITP (\x. x > 4) [1n;2;3;4;5;6]``;
   conv ``SPLITR (\x. x > 4) [1n;2;3;4;5;6]``;
   conv ``SUFFIX (\x. x < 4) [1n;2;3]`` (* ??? *);
   conv ``TL_T ([]: 'a list)``;
   conv ``UNZIP_FST [(1n, 2n); (3, 4)]``;
   conv ``UNZIP_SND [(1n, 2n); (3, 4)]``;

*)

val () = export_theory ()
