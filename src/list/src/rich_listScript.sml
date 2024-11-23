(* ===================================================================== *)
(* FILE          : rich_listScript.sml                                   *)
(* DESCRIPTION   : Enriched Theory of Lists                              *)
(* ===================================================================== *)

open HolKernel Parse boolLib BasicProvers;

open numLib metisLib simpLib combinTheory arithmeticTheory prim_recTheory
     pred_setTheory listTheory pairTheory markerLib TotalDefn;

local open listSimps pred_setSimps in end;

val FILTER_APPEND = FILTER_APPEND_DISTRIB
val REVERSE = REVERSE_SNOC_DEF
val decide_tac = numLib.DECIDE_TAC;

val () = new_theory "rich_list"

(* ------------------------------------------------------------------------ *)

val list_ss = arith_ss ++ listSimps.LIST_ss ++ pred_setSimps.PRED_SET_ss
val metis_tac = METIS_TAC
val rw = SRW_TAC[numSimps.ARITH_ss]
fun simp thl = ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) thl
fun fs thl = FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) thl
fun rfs thl = REV_FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) thl;
val qabbrev_tac = Q.ABBREV_TAC;
val qexists_tac = Q.EXISTS_TAC;
val qspecl_then = Q.SPECL_THEN;
val qid_spec_tac = Q.ID_SPEC_TAC;

val DEF0 = Lib.with_flag (boolLib.def_suffix, "") TotalDefn.Define
val DEF = Lib.with_flag (boolLib.def_suffix, "_DEF") TotalDefn.Define

val zDefine =
   Lib.with_flag (computeLib.auto_import_definitions, false) TotalDefn.Define

val list_INDUCT = Q.prove(
   `!P. P [] /\ (!l. P l ==> !x. P (CONS x l)) ==> !l. P l`,
   REWRITE_TAC [list_INDUCT]);

val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;
val SNOC_INDUCT_TAC = Prim_rec.INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

fun wrap a = [a];
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;

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

val MAP_REVERSE = save_thm ("MAP_REVERSE", MAP_REVERSE);

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

Theorem TAKE_FRONT :
    !l n. l <> [] /\ n < LENGTH l ==> TAKE n (FRONT l) = TAKE n l
Proof
    HO_MATCH_MP_TAC SNOC_INDUCT
 >> CONJ_TAC >- SRW_TAC [][]
 >> RW_TAC arith_ss [FRONT_SNOC, LENGTH_SNOC]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC TAKE_SNOC
 >> RW_TAC arith_ss []
QED

val SNOC_EL_TAKE = Q.store_thm ("SNOC_EL_TAKE",
   `!n l. n < LENGTH l ==> (SNOC (EL n l) (TAKE n l) = TAKE (SUC n) l)`,
   Induct_on `n` THEN Cases_on `l` THEN ASM_SIMP_TAC list_ss [SNOC, TAKE]);

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

Theorem DROP_LENGTH_NIL = listTheory.DROP_LENGTH_NIL
Theorem DROP_APPEND = listTheory.DROP_APPEND
Theorem DROP_APPEND1 = listTheory.DROP_APPEND1
Theorem DROP_APPEND2 = listTheory.DROP_APPEND2

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

(* from examples/lambda/basics/appFOLDLScript.sml *)
Theorem DROP_PREn_LAST_CONS :
    !l n. 0 < n /\ n <= LENGTH l ==>
          (DROP (n - 1) l = LAST (TAKE n l) :: DROP n l)
Proof
  Induct THEN SRW_TAC [numSimps.ARITH_ss][TAKE_def, DROP_def] THENL [
    `n = 1` by numLib.DECIDE_TAC THEN SRW_TAC [][],
    `n = 1` by numLib.DECIDE_TAC THEN SRW_TAC [][],
    `(l = []) \/ ?h t0. l = h :: t0` by METIS_TAC [list_CASES] THEN
    FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [] ]
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

(* |- !x. [] <<= x /\ (x <<= [] <=> x = []) *)
Theorem IS_PREFIX_NIL = isPREFIX_NIL

(* |- !x. x <<= x *)
Theorem IS_PREFIX_REFL[simp] = isPREFIX_REFL

(* |- !x y. x <<= y /\ y <<= x ==> x = y *)
Theorem IS_PREFIX_ANTISYM = isPREFIX_ANTISYM

(* |- !x y z. y <<= x /\ z <<= y ==> z <<= x *)
Theorem IS_PREFIX_TRANS :
    !x y z. IS_PREFIX x y /\ IS_PREFIX y z ==> IS_PREFIX x z
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC isPREFIX_TRANS
 >> Q.EXISTS_TAC ‘y’ >> rw []
QED

val IS_PREFIX_BUTLAST = Q.store_thm ("IS_PREFIX_BUTLAST",
   `!x y. IS_PREFIX (x::y) (FRONT (x::y))`,
   REPEAT GEN_TAC
   THEN Q.SPEC_TAC (`x`, `x`)
   THEN Q.SPEC_TAC (`y`, `y`)
   THEN INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [FRONT_CONS, IS_PREFIX]);

Theorem IS_PREFIX_BUTLAST' :
    !l. l <> [] ==> IS_PREFIX l (FRONT l)
Proof
    Q.X_GEN_TAC ‘l’
 >> Cases_on ‘l’ >- SRW_TAC[][]
 >> SRW_TAC[][IS_PREFIX_BUTLAST]
QED

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

(* |- !x y z. z <<= SNOC x y <=> z <<= y \/ z = SNOC x y *)
Theorem IS_PREFIX_SNOC = isPREFIX_SNOC

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

(* NOTE: By using LENGTH_TAKE, this ‘n’ is actually ’LENGTH l1’ *)
Theorem IS_PREFIX_EQ_TAKE :
    !l l1. l1 <<= l <=> ?n. n <= LENGTH l /\ l1 = TAKE n l
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (STRIP_TAC \\
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
                     [SYM (Q.SPECL [‘n’, ‘l’] TAKE_DROP)] \\
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) \\
     PROVE_TAC [IS_PREFIX_APPEND])
 (* stage work *)
 >> Induct_on ‘l1’ using SNOC_INDUCT
 >- (rw [] >> Q.EXISTS_TAC ‘0’ >> rw [])
 >> rw [SNOC_APPEND]
 >> Q.PAT_X_ASSUM ‘l1 <<= l ==> P’ MP_TAC
 >> ‘l1 <<= l’ by PROVE_TAC [IS_PREFIX_APPEND1]
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘TAKE n l ++ [x] <<= l’ MP_TAC
 >> rw [IS_PREFIX_APPEND]
 >> Q.EXISTS_TAC ‘SUC n’
 >> CONJ_ASM1_TAC
 >- (POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) >> rw [])
 (* applying SNOC_EL_TAKE *)
 >> Know ‘TAKE (SUC n) l = SNOC (EL n l) (TAKE n l)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC SNOC_EL_TAKE >> rw [])
 >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
 >> Suff ‘EL n l = x’ >- rw [SNOC_APPEND]
 >> Q.PAT_X_ASSUM ‘l = _’ (fn th => ONCE_REWRITE_TAC [th])
 (* applying el_append3, fortunately *)
 >> Q.ABBREV_TAC ‘l1 = TAKE n l’
 >> ‘n = LENGTH l1’ by rw [Abbr ‘l1’, LENGTH_TAKE]
 >> POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
 >> rw [el_append3]
QED

(* ‘n <= LENGTH l’ can be removed from RHS *)
Theorem IS_PREFIX_EQ_TAKE' :
    !l l1. l1 <<= l <=> ?n. l1 = TAKE n l
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- (rw [IS_PREFIX_EQ_TAKE] \\
     Q.EXISTS_TAC ‘n’ >> REWRITE_TAC [])
 >> STRIP_TAC
 >> Cases_on ‘n <= LENGTH l’
 >- (rw [IS_PREFIX_EQ_TAKE] \\
     Q.EXISTS_TAC ‘n’ >> ASM_REWRITE_TAC [])
 >> ‘LENGTH l <= n’ by rw []
 >> rw [TAKE_LENGTH_TOO_LONG]
QED

(* NOTE: This theorem can also be proved by IS_PREFIX_LENGTH_ANTI and
   prefixes_is_prefix_total, but IS_PREFIX_EQ_TAKE is more natural.
 *)
Theorem IS_PREFIX_EQ_REWRITE :
    !l1 l2 l. l1 <<= l /\ l2 <<= l ==> (l1 = l2 <=> LENGTH l1 = LENGTH l2)
Proof
    rw [IS_PREFIX_EQ_TAKE]
 >> rw [LENGTH_TAKE, TAKE_EQ_REWRITE]
QED

Theorem IS_PREFIX_ALL_DISTINCT :
    !l l1. l1 <<= l /\ ALL_DISTINCT l ==> ALL_DISTINCT l1
Proof
    rw [IS_PREFIX_EQ_TAKE']
 >> MATCH_MP_TAC ALL_DISTINCT_TAKE >> rw []
QED

Theorem IS_PREFIX_FRONT_MONO :
    !l1 l2. l1 <> [] /\ l2 <> [] /\ l1 <<= l2 ==> FRONT l1 <<= FRONT l2
Proof
    rw [IS_PREFIX_EQ_TAKE]
 >> Cases_on ‘n = 0’ >> fs []
 >> ‘0 < LENGTH l2’ by rw []
 >> rw [LENGTH_FRONT, FRONT_TAKE]
 >> Q.EXISTS_TAC ‘n - 1’ >> rw []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC TAKE_FRONT
 >> rw []
QED

Theorem IS_PREFIX_FRONT_CASES :
    !l l1. l <> [] ==> (l1 <<= l <=> l = l1 \/ l1 <<= FRONT l)
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> reverse EQ_TAC
 >- (STRIP_TAC >- rw [IS_PREFIX_REFL] \\
     MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘FRONT l’ >> rw [] \\
     MATCH_MP_TAC IS_PREFIX_BUTLAST' >> rw [])
 >> rw [IS_PREFIX_EQ_TAKE, LENGTH_FRONT]
 >> ‘n = LENGTH l \/ n < LENGTH l’ by rw []
 >- (DISJ1_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     rw [TAKE_LENGTH_ID_rwt2])
 >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘n’
 >> rw [TAKE_FRONT]
QED

(* |- !f m n. GENLIST f m <<= GENLIST f n <=> m <= n *)
Theorem IS_PREFIX_GENLIST = isPREFIX_GENLIST

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

(*---------------------------------------------------------------------------
   chunks: split a list into equal-sized lists
 ---------------------------------------------------------------------------*)

Definition chunks_def:
  chunks n ls =
  if LENGTH ls <= n \/ n = 0
  then [ls]
  else CONS (TAKE n ls) (chunks n (DROP n ls))
Termination
  Q.EXISTS_TAC`measure (LENGTH o SND)` \\ rw[LENGTH_DROP]
End

val chunks_ind = theorem"chunks_ind";

Theorem chunks_NIL[simp]:
  chunks n [] = [[]]
Proof
  rw[Once chunks_def]
QED

Theorem chunks_0[simp]:
  chunks 0 ls = [ls]
Proof
  rw[Once chunks_def]
QED

Theorem FLAT_chunks[simp]:
  FLAT (chunks n ls) = ls
Proof
  completeInduct_on`LENGTH ls` \\ rw[]
  \\ rw[Once chunks_def]
QED

Theorem divides_EVERY_LENGTH_chunks:
  !n ls. ls <> [] /\ divides n (LENGTH ls) ==>
    EVERY ($= n o LENGTH) (chunks n ls)
Proof
  ho_match_mp_tac chunks_ind
  \\ rw[]
  \\ rw[Once chunks_def] \\ fs[]
  \\ fs[dividesTheory.divides_def]
  \\ REV_FULL_SIMP_TAC(srw_ss())[]
  >- ( Cases_on`q = 0` \\ fs[] )
  \\ first_x_assum irule
  \\ Q.EXISTS_TAC`PRE q`
  \\ Cases_on`q` \\ fs[ADD1]
QED

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

(* ALL_DISTINCT_{DROP,TAKE} are already in listTheory; keep this binding
   here for backwards compatibility *)
Theorem ALL_DISTINCT_TAKE = listTheory.ALL_DISTINCT_TAKE

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
  \\ Q.MATCH_ABBREV_TAC`_ = CARD B`
  \\ Q.MATCH_ASSUM_ABBREV_TAC`_ = CARD A`
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

(* ------------------------------------------------------------------------- *)
(* More List Theorems from examples/algebra                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: l <> [] ==> (l = SNOC (LAST l) (FRONT l)) *)
(* Proof:
     l
   = FRONT l ++ [LAST l]      by APPEND_FRONT_LAST, l <> []
   = SNOC (LAST l) (FRONT l)  by SNOC_APPEND
 *)
val SNOC_LAST_FRONT' = store_thm(
   "SNOC_LAST_FRONT'",
  ``!l. l <> [] ==> (l = SNOC (LAST l) (FRONT l))``,
  rw[APPEND_FRONT_LAST]);

(* Theorem: REVERSE [x] = [x] *)
(* Proof:
      REVERSE [x]
    = [] ++ [x]       by REVERSE_DEF
    = [x]             by APPEND
*)
val REVERSE_SING = store_thm(
  "REVERSE_SING",
  ``!x. REVERSE [x] = [x]``,
  rw[]);

(* Theorem: ls <> [] ==> (HD (REVERSE ls) = LAST ls) *)
(* Proof:
      HD (REVERSE ls)
    = HD (REVERSE (SNOC (LAST ls) (FRONT ls)))   by SNOC_LAST_FRONT
    = HD (LAST ls :: (REVERSE (FRONT ls))        by REVERSE_SNOC
    = LAST ls                                    by HD
*)
Theorem REVERSE_HD:
  !ls. ls <> [] ==> (HD (REVERSE ls) = LAST ls)
Proof
  metis_tac[SNOC_LAST_FRONT, REVERSE_SNOC, HD]
QED

(* Theorem: ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls)) *)
(* Proof:
      TL (REVERSE ls)
    = TL (REVERSE (SNOC (LAST ls) (FRONT ls)))   by SNOC_LAST_FRONT
    = TL (LAST ls :: (REVERSE (FRONT ls))        by REVERSE_SNOC
    = REVERSE (FRONT ls)                         by TL
*)
Theorem REVERSE_TL:
  !ls. ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls))
Proof
  metis_tac[SNOC_LAST_FRONT, REVERSE_SNOC, TL]
QED

(* Theorem: EL (LENGTH ls) (ls ++ h::t) = h *)
(* Proof:
   Let l2 = h::t.
   Note ~NULL l2                      by NULL
     so EL (LENGTH ls) (ls ++ h::t)
      = EL (LENGTH ls) (ls ++ l2)     by notation
      = HD l2                         by EL_LENGTH_APPEND
      = HD (h::t) = h                 by notation
*)
val EL_LENGTH_APPEND_0 = store_thm(
  "EL_LENGTH_APPEND_0",
  ``!ls h t. EL (LENGTH ls) (ls ++ h::t) = h``,
  rw[EL_LENGTH_APPEND]);

(* Theorem: EL (LENGTH ls + 1) (ls ++ h::k::t) = k *)
(* Proof:
   Let l1 = ls ++ [h].
   Then LENGTH l1 = LENGTH ls + 1    by LENGTH
   Note ls ++ h::k::t = l1 ++ k::t   by APPEND
        EL (LENGTH ls + 1) (ls ++ h::k::t)
      = EL (LENGTH l1) (l1 ++ k::t)  by above
      = k                            by EL_LENGTH_APPEND_0
*)
val EL_LENGTH_APPEND_1 = store_thm(
  "EL_LENGTH_APPEND_1",
  ``!ls h k t. EL (LENGTH ls + 1) (ls ++ h::k::t) = k``,
  rpt strip_tac >>
  qabbrev_tac `l1 = ls ++ [h]` >>
  `LENGTH l1 = LENGTH ls + 1` by rw[Abbr`l1`] >>
  `ls ++ h::k::t = l1 ++ k::t` by rw[Abbr`l1`] >>
  metis_tac[EL_LENGTH_APPEND_0]);

(* Theorem: 0 < LENGTH ls <=> (ls = HD ls::TL ls) *)
(* Proof:
   If part: 0 < LENGTH ls ==> (ls = HD ls::TL ls)
      Note LENGTH ls <> 0                       by arithmetic
        so ~(NULL l)                            by NULL_LENGTH
        or ls = HD ls :: TL ls                  by CONS
   Only-if part: (ls = HD ls::TL ls) ==> 0 < LENGTH ls
      Note LENGTH ls = SUC (LENGTH (TL ls))     by LENGTH
       but 0 < SUC (LENGTH (TL ls))             by SUC_POS
*)
val LIST_HEAD_TAIL = store_thm(
  "LIST_HEAD_TAIL",
  ``!ls. 0 < LENGTH ls <=> (ls = HD ls::TL ls)``,
  metis_tac[LIST_NOT_NIL, NOT_NIL_EQ_LENGTH_NOT_0]);

(* Theorem: p <> [] /\ q <> [] ==> ((p = q) <=> ((HD p = HD q) /\ (TL p = TL q))) *)
(* Proof: by cases on p and cases on q, CONS_11 *)
val LIST_EQ_HEAD_TAIL = store_thm(
  "LIST_EQ_HEAD_TAIL",
  ``!p q. p <> [] /\ q <> [] ==>
         ((p = q) <=> ((HD p = HD q) /\ (TL p = TL q)))``,
  (Cases_on `p` >> Cases_on `q` >> fs[]));

(* Theorem: [x] = [y] <=> x = y *)
(* Proof: by EQ_LIST and notation. *)
val LIST_SING_EQ = store_thm(
  "LIST_SING_EQ",
  ``!x y. ([x] = [y]) <=> (x = y)``,
  rw_tac bool_ss[]);

(* Theorem: LENGTH [x] = 1 *)
(* Proof: by LENGTH, ONE. *)
val LENGTH_SING = store_thm(
  "LENGTH_SING",
  ``!x. LENGTH [x] = 1``,
  rw_tac bool_ss[LENGTH, ONE]);

(* Theorem: ls <> [] ==> LENGTH (TL ls) < LENGTH ls *)
(* Proof: by LENGTH_TL, LENGTH_EQ_0 *)
val LENGTH_TL_LT = store_thm(
  "LENGTH_TL_LT",
  ``!ls. ls <> [] ==> LENGTH (TL ls) < LENGTH ls``,
  metis_tac[LENGTH_TL, LENGTH_EQ_0, NOT_ZERO_LT_ZERO, DECIDE``n <> 0 ==> n - 1 < n``]);

(* Theorem: MAP f [x] = [f x] *)
(* Proof: by MAP *)
val MAP_SING = store_thm(
  "MAP_SING",
  ``!f x. MAP f [x] = [f x]``,
  rw[]);

(* listTheory.MAP_TL  |- !l f. MAP f (TL l) = TL (MAP f l) *)

(* Theorem: ls <> [] ==> HD (MAP f ls) = f (HD ls) *)
(* Proof:
   Note 0 < LENGTH ls              by LENGTH_NON_NIL
        HD (MAP f ls)
      = EL 0 (MAP f ls)            by EL
      = f (EL 0 ls)                by EL_MAP, 0 < LENGTH ls
      = f (HD ls)                  by EL
*)
Theorem MAP_HD:
  !ls f. ls <> [] ==> HD (MAP f ls) = f (HD ls)
Proof
  metis_tac[EL_MAP, EL, LENGTH_NON_NIL]
QED

(*
LAST_EL  |- !ls. ls <> [] ==> LAST ls = EL (PRE (LENGTH ls)) ls
*)

(* Theorem: t <> [] ==> (LAST t = EL (LENGTH t) (h::t)) *)
(* Proof:
   Note LENGTH t <> 0                      by LENGTH_EQ_0
     or 0 < LENGTH t
        LAST t
      = EL (PRE (LENGTH t)) t              by LAST_EL
      = EL (SUC (PRE (LENGTH t))) (h::t)   by EL
      = EL (LENGTH t) (h::t)               bu SUC_PRE, 0 < LENGTH t
*)
val LAST_EL_CONS = store_thm(
  "LAST_EL_CONS",
  ``!h t. t <> [] ==> (LAST t = EL (LENGTH t) (h::t))``,
  rpt strip_tac >>
  `0 < LENGTH t` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `LAST t = EL (PRE (LENGTH t)) t` by rw[LAST_EL] >>
  `_ = EL (SUC (PRE (LENGTH t))) (h::t)` by rw[] >>
  metis_tac[SUC_PRE]);

(* Theorem alias *)
val FRONT_LENGTH = save_thm ("FRONT_LENGTH", LENGTH_FRONT);
(* val FRONT_LENGTH = |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l)): thm *)

(* Theorem: l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l) *)
(* Proof: by EL_FRONT, NULL *)
val FRONT_EL = store_thm(
  "FRONT_EL",
  ``!l n. l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l)``,
  metis_tac[EL_FRONT, NULL, list_CASES]);

(* Theorem: (LENGTH l = 1) ==> (FRONT l = []) *)
(* Proof:
   Note ?x. l = [x]     by LENGTH_EQ_1
     FRONT l
   = FRONT [x]          by above
   = []                 by FRONT_DEF
*)
val FRONT_EQ_NIL = store_thm(
  "FRONT_EQ_NIL",
  ``!l. (LENGTH l = 1) ==> (FRONT l = [])``,
  rw[LENGTH_EQ_1] >>
  rw[FRONT_DEF]);

(* Theorem: 1 < LENGTH l ==> FRONT l <> [] *)
(* Proof:
   Note LENGTH l <> 0          by 1 < LENGTH l
   Thus ?h s. l = h::s         by list_CASES
     or 1 < 1 + LENGTH s
     so 0 < LENGTH s           by arithmetic
   Thus ?k t. s = k::t         by list_CASES
      FRONT l
    = FRONT (h::k::t)
    = h::FRONT (k::t)          by FRONT_CONS
    <> []                      by list_CASES
*)
val FRONT_NON_NIL = store_thm(
  "FRONT_NON_NIL",
  ``!l. 1 < LENGTH l ==> FRONT l <> []``,
  rpt strip_tac >>
  `LENGTH l <> 0` by decide_tac >>
  `?h s. l = h::s` by metis_tac[list_CASES, LENGTH_EQ_0] >>
  `LENGTH l = 1 + LENGTH s` by rw[] >>
  `LENGTH s <> 0` by decide_tac >>
  `?k t. s = k::t` by metis_tac[list_CASES, LENGTH_EQ_0] >>
  `FRONT l = h::FRONT (k::t)` by fs[FRONT_CONS] >>
  fs[]);

(* Theorem: ls <> [] ==> MEM (HD ls) ls *)
(* Proof:
   Note ls = h::t      by list_CASES
        MEM (HD (h::t)) (h::t)
    <=> MEM h (h::t)   by HD
    <=> T              by MEM
*)
val HEAD_MEM = store_thm(
  "HEAD_MEM",
  ``!ls. ls <> [] ==> MEM (HD ls) ls``,
  (Cases_on `ls` >> simp[]));

(* Theorem: ls <> [] ==> MEM (LAST ls) ls *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MEM (LAST []) []
      True by [] <> [] = F.
   Step: ls <> [] ==> MEM (LAST ls) ls ==>
         !h. h::ls <> [] ==> MEM (LAST (h::ls)) (h::ls)
      If ls = [],
             MEM (LAST [h]) [h]
         <=> MEM h [h]          by LAST_DEF
         <=> T                  by MEM
      If ls <> [],
             MEM (LAST [h::ls]) (h::ls)
         <=> MEM (LAST ls) (h::ls)             by LAST_DEF
         <=> LAST ls = h \/ MEM (LAST ls) ls   by MEM
         <=> LAST ls = h \/ T                  by induction hypothesis
         <=> T                                 by logical or
*)
val LAST_MEM = store_thm(
  "LAST_MEM",
  ``!ls. ls <> [] ==> MEM (LAST ls) ls``,
  Induct >-
  decide_tac >>
  (Cases_on `ls = []` >> rw[LAST_DEF]));

(* Idea: the last equals the head when there is no tail. *)

(* Theorem: ~MEM h t /\ LAST (h::t) = h <=> t = [] *)
(* Proof:
   If part: ~MEM h t /\ LAST (h::t) = h ==> t = []
      By contradiction, suppose t <> [].
      Then h = LAST (h::t) = LAST t            by LAST_CONS_cond, t <> []
        so MEM h t                             by LAST_MEM
      This contradicts ~MEM h t.
   Only-if part: t = [] ==> ~MEM h t /\ LAST (h::t) = h
      Note MEM h [] = F, so ~MEM h [] = T      by MEM
       and LAST [h] = h                        by LAST_CONS
*)
Theorem LAST_EQ_HD:
  !h t. ~MEM h t /\ LAST (h::t) = h <=> t = []
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  metis_tac[LAST_CONS_cond, LAST_MEM]
QED

(* Theorem: ls <> [] /\ ALL_DISTINCT ls ==> ~MEM (LAST ls) (FRONT ls) *)
(* Proof:
   Let k = LENGTH ls.
   Then 0 < k                                  by LENGTH_EQ_0, NOT_ZERO
    and LENGTH (FRONT ls) = PRE k              by LENGTH_FRONT, ls <> []
     so ?n. n < PRE k /\
        LAST ls = EL n (FRONT ls)              by MEM_EL
                = EL n ls                      by FRONT_EL, ls <> []
    but LAST ls = EL (PRE k) ls                by LAST_EL, ls <> []
   Thus n = PRE k                              by ALL_DISTINCT_EL_IMP
   This contradicts n < PRE k                  by arithmetic
*)
Theorem MEM_FRONT_NOT_LAST:
  !ls. ls <> [] /\ ALL_DISTINCT ls ==> ~MEM (LAST ls) (FRONT ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH ls` >>
  `0 < k` by metis_tac[LENGTH_EQ_0, NOT_ZERO] >>
  `LENGTH (FRONT ls) = PRE k` by fs[LENGTH_FRONT, Abbr`k`] >>
  fs[MEM_EL] >>
  `LAST ls = EL n ls` by fs[FRONT_EL] >>
  `LAST ls = EL (PRE k) ls` by rfs[LAST_EL, Abbr`k`] >>
  `n < k /\ PRE k < k` by decide_tac >>
  `n = PRE k` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  decide_tac
QED

(* Theorem: ls = [] <=> !x. ~MEM x ls *)
(* Proof:
   If part: !x. ~MEM x [], true    by MEM
   Only-if part: !x. ~MEM x ls ==> ls = []
      By contradiction, suppose ls <> [].
      Then ?h t. ls = h::t         by list_CASES
       and MEM h ls                by MEM
      which contradicts !x. ~MEM x ls.
*)
Theorem NIL_NO_MEM:
  !ls. ls = [] <=> !x. ~MEM x ls
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  metis_tac[list_CASES, MEM]
QED

(*
el_append3
|- !l1 x l2. EL (LENGTH l1) (l1 ++ [x] ++ l2) = x
*)

(* Theorem: MEM h (l1 ++ [x] ++ l2) <=> MEM h (x::(l1 ++ l2)) *)
(* Proof:
       MEM h (l1 ++ [x] ++ l2)
   <=> MEM h l1 \/ h = x \/ MEM h l2     by MEM, MEM_APPEND
   <=> h = x \/ MEM h l1 \/ MEM h l2
   <=> h = x \/ MEM h (l1 ++ l2)         by MEM_APPEND
   <=> MEM h (x::(l1 + l2))              by MEM
*)
Theorem MEM_APPEND_3:
  !l1 x l2 h. MEM h (l1 ++ [x] ++ l2) <=> MEM h (x::(l1 ++ l2))
Proof
  rw[] >>
  metis_tac[]
QED

(* Theorem: DROP 1 (h::t) = t *)
(* Proof: DROP_def *)
val DROP_1 = store_thm(
  "DROP_1",
  ``!h t. DROP 1 (h::t) = t``,
  rw[]);

(* Theorem: FRONT [x] = [] *)
(* Proof: FRONT_def *)
val FRONT_SING = store_thm(
  "FRONT_SING",
  ``!x. FRONT [x] = []``,
  rw[]);

(* Theorem: ls <> [] ==> (TL ls = DROP 1 ls) *)
(* Proof:
   Note ls = h::t        by list_CASES
     so TL (h::t)
      = t                by TL
      = DROP 1 (h::t)    by DROP_def
*)
val TAIL_BY_DROP = store_thm(
  "TAIL_BY_DROP",
  ``!ls. ls <> [] ==> (TL ls = DROP 1 ls)``,
  Cases_on `ls` >-
  decide_tac >>
  rw[]);

(* Theorem: ls <> [] ==> (FRONT ls = TAKE (LENGTH ls - 1) ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> FRONT [] = TAKE (LENGTH [] - 1) []
      True by [] <> [] = F.
   Step: ls <> [] ==> FRONT ls = TAKE (LENGTH ls - 1) ls ==>
         !h. h::ls <> [] ==> FRONT (h::ls) = TAKE (LENGTH (h::ls) - 1) (h::ls)
      If ls = [],
           FRONT [h]
         = []                          by FRONT_SING
         = TAKE 0 [h]                  by TAKE_0
         = TAKE (LENGTH [h] - 1) [h]   by LENGTH_SING
      If ls <> [],
           FRONT (h::ls)
         = h::FRONT ls                        by FRONT_DEF
         = h::TAKE (LENGTH ls - 1) ls         by induction hypothesis
         = TAKE (LENGTH (h::ls) - 1) (h::ls)  by TAKE_def
*)
val FRONT_BY_TAKE = store_thm(
  "FRONT_BY_TAKE",
  ``!ls. ls <> [] ==> (FRONT ls = TAKE (LENGTH ls - 1) ls)``,
  Induct >-
  decide_tac >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `LENGTH ls <> 0` by rw[] >>
  rw[FRONT_DEF]);

(* Theorem: HD (h::t ++ ls) = h *)
(* Proof:
     HD (h::t ++ ls)
   = HD (h::(t ++ ls))     by APPEND
   = h                     by HD
*)
Theorem HD_APPEND:
  !h t ls. HD (h::t ++ ls) = h
Proof
  simp[]
QED

(* Theorem: 0 <> n ==> (EL (n-1) t = EL n (h::t)) *)
(* Proof:
   Note n = SUC k for some k         by num_CASES
     so EL k t = EL (SUC k) (h::t)   by EL_restricted
*)
Theorem EL_TAIL:
  !h t n. 0 <> n ==> (EL (n-1) t = EL n (h::t))
Proof
  rpt strip_tac >>
  `n = SUC (n - 1)` by decide_tac >>
  metis_tac[EL_restricted]
QED

(* Idea: If all elements are the same, the set is SING. *)

(* Theorem: ls <> [] /\ EVERY ($= c) ls ==> SING (set ls) *)
(* Proof:
   Note set ls = {c}       by LIST_TO_SET_EQ_SING
   thus SING (set ls)      by SING_DEF
*)
Theorem MONOLIST_SET_SING:
  !c ls. ls <> [] /\ EVERY ($= c) ls ==> SING (set ls)
Proof
  metis_tac[LIST_TO_SET_EQ_SING, SING_DEF]
QED

(*
> EVAL ``set [3;3;3]``;
val it = |- set [3; 3; 3] = set [3; 3; 3]: thm
*)

(* Put LIST_TO_SET into compute
(* Near: put to helperList *)
Theorem LIST_TO_SET_EVAL[compute] = LIST_TO_SET |> GEN_ALL;
(* val LIST_TO_SET_EVAL = |- !t h. set [] = {} /\ set (h::t) = h INSERT set t: thm *)
(* cannot add to computeLib directly LIST_TO_SET, which is not in current theory. *)
 *)

(*
> EVAL ``set [3;3;3]``;
val it = |- set [3; 3; 3] = {3}: thm
*)

(* Theorem: set ls = count n ==> !j. j < LENGTH ls ==> EL j ls < n *)
(* Proof:
   Note MEM (EL j ls) ls       by EL_MEM
     so EL j ls IN (count n)   by set ls = count n
     or EL j ls < n            by IN_COUNT
*)
Theorem set_list_eq_count:
  !ls n. set ls = count n ==> !j. j < LENGTH ls ==> EL j ls < n
Proof
  metis_tac[EL_MEM, IN_COUNT]
QED

(* Theorem: set ls = IMAGE (\j. EL j ls) (count (LENGTH ls)) *)
(* Proof:
   Let f = \j. EL j ls, n = LENGTH ls.
       x IN IMAGE f (count n)
   <=> ?j. x = f j /\ j IN (count n)     by IN_IMAGE
   <=> ?j. x = EL j ls /\ j < n          by notation, IN_COUNT
   <=> MEM x ls                          by MEM_EL
   <=> x IN set ls                       by notation
   Thus set ls = IMAGE f (count n)       by EXTENSION
*)
Theorem list_to_set_eq_el_image:
  !ls. set ls = IMAGE (\j. EL j ls) (count (LENGTH ls))
Proof
  rw[EXTENSION] >>
  metis_tac[MEM_EL]
QED

(* Theorem: ALL_DISTINCT ls ==> INJ (\j. EL j ls) (count (LENGTH ls)) univ(:num) *)
(* Proof:
   By INJ_DEF this is to show:
   (1) EL j ls IN univ(:'a), true  by IN_UNIV, function type
   (2) !x y. x < LENGTH ls /\ y < LENGTH ls /\ EL x ls = EL y ls ==> x = y
       This is true                by ALL_DISTINCT_EL_IMP, ALL_DISTINCT ls
*)
Theorem all_distinct_list_el_inj:
  !ls. ALL_DISTINCT ls ==> INJ (\j. EL j ls) (count (LENGTH ls)) univ(:'a)
Proof
  rw[INJ_DEF, ALL_DISTINCT_EL_IMP]
QED

(* MAP_ZIP_SAME  |- !ls f. MAP f (ZIP (ls,ls)) = MAP (\x. f (x,x)) ls *)

(* Theorem: ZIP ((MAP f ls), (MAP g ls)) = MAP (\x. (f x, g x)) ls *)
(* Proof:
     ZIP ((MAP f ls), (MAP g ls))
   = MAP (\(x, y). (f x, y)) (ZIP (ls, (MAP g ls)))                    by ZIP_MAP
   = MAP (\(x, y). (f x, y)) (MAP (\(x, y). (x, g y)) (ZIP (ls, ls)))  by ZIP_MAP
   = MAP (\(x, y). (f x, y)) (MAP (\j. (\(x, y). (x, g y)) (j,j)) ls)  by MAP_ZIP_SAME
   = MAP (\(x, y). (f x, y)) o (\j. (\(x, y). (x, g y)) (j,j)) ls      by MAP_COMPOSE
   = MAP (\x. (f x, g x)) ls                                           by FUN_EQ_THM
*)
val ZIP_MAP_MAP = store_thm(
  "ZIP_MAP_MAP",
  ``!ls f g. ZIP ((MAP f ls), (MAP g ls)) = MAP (\x. (f x, g x)) ls``,
  rw[ZIP_MAP, MAP_COMPOSE] >>
  qabbrev_tac `f1 = \p. (f (FST p),SND p)` >>
  qabbrev_tac `f2 = \x. (x,g x)` >>
  qabbrev_tac `f3 = \x. (f x,g x)` >>
  `f1 o f2 = f3` by rw[FUN_EQ_THM, Abbr`f1`, Abbr`f2`, Abbr`f3`] >>
  rw[]);

(* Theorem: MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls *)
(* Proof:
   Let k = LENGTH ls.
     Note LENGTH (MAP g1 ls) = k      by LENGTH_MAP
      and LENGTH (MAP g2 ls) = k      by LENGTH_MAP
     MAP2 f (MAP g1 ls) (MAP g2 ls)
   = MAP (UNCURRY f) (ZIP ((MAP g1 ls), (MAP g2 ls)))      by MAP2_MAP
   = MAP (UNCURRY f) (MAP (\x. (g1 x, g2 x)) ls)           by ZIP_MAP_MAP
   = MAP ((UNCURRY f) o (\x. (g1 x, g2 x))) ls             by MAP_COMPOSE
   = MAP (\x. f (g1 x) (g2 y)) ls                          by FUN_EQ_THM
*)
val MAP2_MAP_MAP = store_thm(
  "MAP2_MAP_MAP",
  ``!ls f g1 g2. MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls``,
  rw[MAP2_MAP, ZIP_MAP_MAP, MAP_COMPOSE] >>
  qabbrev_tac `f1 = UNCURRY f o (\x. (g1 x,g2 x))` >>
  qabbrev_tac `f2 = \x. f (g1 x) (g2 x)` >>
  `f1 = f2` by rw[FUN_EQ_THM, Abbr`f1`, Abbr`f2`] >>
  rw[]);

(* Theorem: EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2 *)
(* Proof: by EL_APPEND1, EL_APPEND2 *)
val EL_APPEND = store_thm(
  "EL_APPEND",
  ``!n l1 l2. EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2``,
  rw[EL_APPEND1, EL_APPEND2]);

(* Theorem: j < LENGTH ls ==> ?l1 l2. ls = l1 ++ (EL j ls)::l2 *)
(* Proof:
   Let x = EL j ls.
   Then MEM x ls                   by EL_MEM, j < LENGTH ls
     so ?l1 l2. l = l1 ++ x::l2    by MEM_SPLIT
   Pick these l1 and l2.
*)
Theorem EL_SPLIT:
  !ls j. j < LENGTH ls ==> ?l1 l2. ls = l1 ++ (EL j ls)::l2
Proof
  metis_tac[EL_MEM, MEM_SPLIT]
QED

(* Theorem: j < k /\ k < LENGTH ls ==>
            ?l1 l2 l3. ls = l1 ++ (EL j ls)::l2 ++ (EL k ls)::l3 *)
(* Proof:
   Let a = EL j ls,
       b = EL k ls.
   Note j < LENGTH ls          by j < k, k < LENGTH ls
     so MEM a ls /\ MEM b ls   by MEM_EL

    Now ls
      = TAKE k ls ++ DROP k ls                 by TAKE_DROP
      = TAKE k ls ++ b::(DROP (k+1) ls)        by DROP_EL_CONS
    Let lt = TAKE k ls.
    Then LENGTH lt = k                         by LENGTH_TAKE
     and a = EL j lt                           by EL_TAKE
     and lt
       = TAKE j lt ++ DROP j lt                by TAKE_DROP
       = TAKE j lt ++ a::(DROP (j+1) lt)       by DROP_EL_CONS
    Pick l1 = TAKE j lt, l2 = DROP (j+1) lt, l3 = DROP (k+1) ls.
*)
Theorem EL_SPLIT_2:
  !ls j k. j < k /\ k < LENGTH ls ==>
           ?l1 l2 l3. ls = l1 ++ (EL j ls)::l2 ++ (EL k ls)::l3
Proof
  rpt strip_tac >>
  qabbrev_tac `a = EL j ls` >>
  qabbrev_tac `b = EL k ls` >>
  `j < LENGTH ls` by decide_tac >>
  `MEM a ls /\ MEM b ls` by metis_tac[MEM_EL] >>
  `ls = TAKE k ls ++ b::(DROP (k+1) ls)` by metis_tac[TAKE_DROP, DROP_EL_CONS] >>
  qabbrev_tac `lt = TAKE k ls` >>
  `LENGTH lt = k` by simp[Abbr`lt`] >>
  `a = EL j lt` by simp[EL_TAKE, Abbr`a`, Abbr`lt`] >>
  `lt = TAKE j lt ++ a::(DROP (j+1) lt)` by metis_tac[TAKE_DROP, DROP_EL_CONS] >>
  metis_tac[]
QED

(* Theorem: (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2) *)
(* Proof:
   By APPEND_EQ_APPEND,
   ?l. (l1 = m1 ++ l) /\ (m2 = l ++ l2) \/ ?l. (m1 = l1 ++ l) /\ (l2 = l ++ m2).
   Thus this is to show:
   (1) LENGTH (m1 ++ l) = LENGTH m1 ==> m1 ++ l = m1, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (2) LENGTH (m1 ++ l) = LENGTH m1 ==> l2 = l ++ l2, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (3) LENGTH l1 = LENGTH (l1 ++ l) ==> l1 = l1 ++ l, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (4) LENGTH l1 = LENGTH (l1 ++ l) ==> l ++ m2 = m2, true since l = [] by LENGTH_APPEND, LENGTH_NIL
*)
val APPEND_EQ_APPEND_EQ = store_thm(
  "APPEND_EQ_APPEND_EQ",
  ``!l1 l2 m1 m2. (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2)``,
  rw[APPEND_EQ_APPEND] >>
  rw[EQ_IMP_THM] >-
  fs[] >-
  fs[] >-
 (fs[] >>
  `LENGTH l = 0` by decide_tac >>
  fs[]) >>
  fs[] >>
  `LENGTH l = 0` by decide_tac >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* More about DROP and TAKE                                                  *)
(* ------------------------------------------------------------------------- *)

(* listTheory.HD_DROP  |- !n l. n < LENGTH l ==> HD (DROP n l) = EL n l *)

(* Theorem: n < LENGTH ls ==> TL (DROP n ls) = DROP n (TL ls) *)
(* Proof:
   Note 0 < LENGTH ls, so ls <> []             by LENGTH_NON_NIL
     so ?h t. ls = h::t                        by NOT_NIL_CONS
        TL (DROP n ls)
      = TL (EL n ls::DROP (SUC n) ls)          by DROP_CONS_EL
      = DROP (SUC n) ls                        by TL
      = DROP (SUC n) (h::t)                    by above
      = DROP n t                               by DROP
      = DROP n (TL ls)                         by TL
*)
Theorem TL_DROP:
  !ls n. n < LENGTH ls ==> TL (DROP n ls) = DROP n (TL ls)
Proof
  rpt strip_tac >>
  `0 < LENGTH ls` by decide_tac >>
  `TL (DROP n ls) = TL (EL n ls::DROP (SUC n) ls)` by simp[DROP_CONS_EL] >>
  `_ = DROP (SUC n) ls` by simp[] >>
  `_ = DROP (SUC n) (HD ls::TL ls)` by metis_tac[LIST_HEAD_TAIL] >>
  simp[]
QED

(* Theorem: x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x) *)
(* Proof:
   x <> [] means ?h t. x = h::t    by list_CASES
     TAKE 1 (x ++ y)
   = TAKE 1 ((h::t) ++ y)
   = TAKE 1 (h:: t ++ y)      by APPEND
   = h::TAKE 0 (t ++ y)       by TAKE_def
   = h::TAKE 0 t              by TAKE_0
   = TAKE 1 (h::t)            by TAKE_def
*)
val TAKE_1_APPEND = store_thm(
  "TAKE_1_APPEND",
  ``!x y. x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x)``,
  Cases_on `x`>> rw[]);

(* Theorem: x <> [] ==> (DROP 1 (x ++ y) = (DROP 1 x) ++ y) *)
(* Proof:
   x <> [] means ?h t. x = h::t    by list_CASES
     DROP 1 (x ++ y)
   = DROP 1 ((h::t) ++ y)
   = DROP 1 (h:: t ++ y)      by APPEND
   = DROP 0 (t ++ y)          by DROP_def
   = t ++ y                   by DROP_0
   = (DROP 1 (h::t)) ++ y     by DROP_def
*)
val DROP_1_APPEND = store_thm(
  "DROP_1_APPEND",
  ``!x y. x <> [] ==> (DROP 1 (x ++ y) = (DROP 1 x) ++ y)``,
  Cases_on `x` >> rw[]);

(* Theorem: DROP (SUC n) x = DROP 1 (DROP n x) *)
(* Proof:
   By induction on x.
   Base case: !n. DROP (SUC n) [] = DROP 1 (DROP n [])
     LHS = DROP (SUC n) []  = []  by DROP_def
     RHS = DROP 1 (DROP n [])
         = DROP 1 []              by DROP_def
         = [] = LHS               by DROP_def
   Step case: !n. DROP (SUC n) x = DROP 1 (DROP n x) ==>
              !h n. DROP (SUC n) (h::x) = DROP 1 (DROP n (h::x))
     If n = 0,
     LHS = DROP (SUC 0) (h::x)
         = DROP 1 (h::x)          by ONE
     RHS = DROP 1 (DROP 0 (h::x))
         = DROP 1 (h::x) = LHS    by DROP_0
     If n <> 0,
     LHS = DROP (SUC n) (h::x)
         = DROP n x               by DROP_def
     RHS = DROP 1 (DROP n (h::x)
         = DROP 1 (DROP (n-1) x)  by DROP_def
         = DROP (SUC (n-1)) x     by induction hypothesis
         = DROP n x = LHS         by SUC (n-1) = n, n <> 0.
*)
val DROP_SUC = store_thm(
  "DROP_SUC",
  ``!n x. DROP (SUC n) x = DROP 1 (DROP n x)``,
  Induct_on `x` >>
  rw[DROP_def] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[]);

(* Theorem: TAKE (SUC n) x = (TAKE n x) ++ (TAKE 1 (DROP n x)) *)
(* Proof:
   By induction on x.
   Base case: !n. TAKE (SUC n) [] = TAKE n [] ++ TAKE 1 (DROP n [])
     LHS = TAKE (SUC n) [] = []    by TAKE_def
     RHS = TAKE n [] ++ TAKE 1 (DROP n [])
         = [] ++ TAKE 1 []         by TAKE_def, DROP_def
         = TAKE 1 []               by APPEND
         = [] = LHS                by TAKE_def
   Step case: !n. TAKE (SUC n) x = TAKE n x ++ TAKE 1 (DROP n x) ==>
              !h n. TAKE (SUC n) (h::x) = TAKE n (h::x) ++ TAKE 1 (DROP n (h::x))
     If n = 0,
     LHS = TAKE (SUC 0) (h::x)
         = TAKE 1 (h::x)           by ONE
     RHS = TAKE 0 (h::x) ++ TAKE 1 (DROP 0 (h::x))
         = [] ++ TAKE 1 (h::x)     by TAKE_def, DROP_def
         = TAKE 1 (h::x) = LHS     by APPEND
     If n <> 0,
     LHS = TAKE (SUC n) (h::x)
         = h :: TAKE n x           by TAKE_def
     RHS = TAKE n (h::x) ++ TAKE 1 (DROP n (h::x))
         = (h:: TAKE (n-1) x) ++ TAKE 1 (DROP (n-1) x)   by TAKE_def, DROP_def, n <> 0.
         = h :: (TAKE (n-1) x ++ TAKE 1 (DROP (n-1) x))  by APPEND
         = h :: TAKE (SUC (n-1)) x  by induction hypothesis
         = h :: TAKE n x            by SUC (n-1) = n, n <> 0.
*)
val TAKE_SUC = store_thm(
  "TAKE_SUC",
  ``!n x. TAKE (SUC n) x = (TAKE n x) ++ (TAKE 1 (DROP n x))``,
  Induct_on `x` >>
  rw[TAKE_def, DROP_def] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[]);

(* Theorem: k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x)) *)
(* Proof:
   By induction on k.
   Base case: !x. 0 < LENGTH x ==> (TAKE (SUC 0) x = SNOC (EL 0 x) (TAKE 0 x))
         0 < LENGTH x
     ==> ?h t. x = h::t   by LENGTH_NIL, list_CASES
     LHS = TAKE (SUC 0) x
         = TAKE 1 (h::t)   by ONE
         = h::TAKE 0 t     by TAKE_def
         = h::[]           by TAKE_0
         = [h]
         = SNOC h []       by SNOC
         = SNOC h (TAKE 0 (h::t))             by TAKE_0
         = SNOC (EL 0 (h::t)) (TAKE 0 (h::t)) by EL
         = RHS
   Step case: !x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x)) ==>
     !x. SUC k < LENGTH x ==> (TAKE (SUC (SUC k)) x = SNOC (EL (SUC k) x) (TAKE (SUC k) x))
     Since 0 < SUC k                        by prim_recTheory.LESS_0
           0 < LENGTH x                     by LESS_TRANS
       ==> ?h t. x = h::t                   by LENGTH_NIL, list_CASES
       and LENGTH (h::t) = SUC (LENGTH t)   by LENGTH
     hence k < LENGTH t                     by LESS_MONO_EQ
     LHS = TAKE (SUC (SUC k)) (h::t)
         = h :: TAKE (SUC k) t              by TAKE_def
         = h :: SNOC (EL k t) (TAKE k t)    by induction hypothesis, k < LENGTH t.
         = SNOC (EL k t) (h :: TAKE k t)    by SNOC
         = SNOC (EL (SUC k) (h::t)) (h :: TAKE k t)         by EL_restricted
         = SNOC (EL (SUC k) (h::t)) (TAKE (SUC k) (h::t))   by TAKE_def
         = RHS
*)
val TAKE_SUC_BY_TAKE = store_thm(
  "TAKE_SUC_BY_TAKE",
  ``!k x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x))``,
  Induct_on `k` >| [
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    rw[],
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `k < LENGTH t` by metis_tac[LENGTH, LESS_MONO_EQ] >>
    rw_tac std_ss[TAKE_def, SNOC, EL_restricted]
  ]);

(* Theorem: k < LENGTH x ==> (DROP k x = (EL k x) :: (DROP (SUC k) x)) *)
(* Proof:
   By induction on k.
   Base case: !x. 0 < LENGTH x ==> (DROP 0 x = EL 0 x::DROP (SUC 0) x)
         0 < LENGTH x
     ==> ?h t. x = h::t   by LENGTH_NIL, list_CASES
     LHS = DROP 0 (h::t)
         = h::t                            by DROP_0
         = (EL 0 (h::t))::t                by EL
         = (EL 0 (h::t))::(DROP 1 (h::t))  by DROP_def
         = EL 0 x::DROP (SUC 0) x          by ONE
         = RHS
   Step case: !x. k < LENGTH x ==> (DROP k x = EL k x::DROP (SUC k) x) ==>
              !x. SUC k < LENGTH x ==> (DROP (SUC k) x = EL (SUC k) x::DROP (SUC (SUC k)) x)
     Since 0 < SUC k                        by prim_recTheory.LESS_0
           0 < LENGTH x                     by LESS_TRANS
       ==> ?h t. x = h::t                   by LENGTH_NIL, list_CASES
       and LENGTH (h::t) = SUC (LENGTH t)   by LENGTH
     hence k < LENGTH t                     by LESS_MONO_EQ
     LHS = DROP (SUC k) (h::t)
         = DROP k t                         by DROP_def
         = EL k x::DROP (SUC k) x           by induction hypothesis
         = EL k t :: DROP (SUC (SUC k)) (h::t)           by DROP_def
         = EL (SUC k) (h::t)::DROP (SUC (SUC k)) (h::t)  by EL
         = RHS
*)
val DROP_BY_DROP_SUC = store_thm(
  "DROP_BY_DROP_SUC",
  ``!k x. k < LENGTH x ==> (DROP k x = (EL k x) :: (DROP (SUC k) x))``,
  Induct_on `k` >| [
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    rw[],
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `k < LENGTH t` by metis_tac[LENGTH, LESS_MONO_EQ] >>
    rw[]
  ]);

(* Theorem: n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u *)
(* Proof:
   By induction on n.
   Base: !ls. 0 < LENGTH ls ==> ?u. DROP 0 ls = [EL 0 ls] ++ u
       Note LENGTH ls <> 0        by 0 < LENGTH ls
        ==> ls <> []              by LENGTH_NIL
        ==> ?h t. ls = h::t       by list_CASES
         DROP 0 ls
       = ls                       by DROP_0
       = [h] ++ t                 by ls = h::t, CONS_APPEND
       = [EL 0 ls] ++ t           by EL
       Take u = t.
   Step: !ls. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u ==>
         !ls. SUC n < LENGTH ls ==> ?u. DROP (SUC n) ls = [EL (SUC n) ls] ++ u
       Note LENGTH ls <> 0                  by SUC n < LENGTH ls
        ==> ?h t. ls = h::t                 by list_CASES, LENGTH_NIL
        Now LENGTH ls = SUC (LENGTH t)      by LENGTH
        ==> n < LENGTH t                    by SUC n < SUC (LENGTH t)
       Thus ?u. DROP n t = [EL n t] ++ u    by induction hypothesis

         DROP (SUC n) ls
       = DROP (SUC n) (h::t)                by ls = h::t
       = DROP n t                           by DROP_def
       = [EL n t] ++ u                      by above
       = [EL (SUC n) (h::t)] ++ u           by EL_restricted
       Take this u.
*)
val DROP_HEAD_ELEMENT = store_thm(
  "DROP_HEAD_ELEMENT",
  ``!ls n. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u``,
  Induct_on `n` >| [
    rpt strip_tac >>
    `LENGTH ls <> 0` by decide_tac >>
    `?h t. ls = h::t` by metis_tac[list_CASES, LENGTH_NIL] >>
    rw[],
    rw[] >>
    `LENGTH ls <> 0` by decide_tac >>
    `?h t. ls = h::t` by metis_tac[list_CASES, LENGTH_NIL] >>
    `LENGTH ls = SUC (LENGTH t)` by rw[] >>
    `n < LENGTH t` by decide_tac >>
    `?u. DROP n t = [EL n t] ++ u` by rw[] >>
    rw[]
  ]);

(* Theorem: DROP n (TAKE n ls) = [] *)
(* Proof:
   If n <= LENGTH ls,
      Then LENGTH (TAKE n ls) = n           by LENGTH_TAKE_EQ
      Thus DROP n (TAKE n ls) = []          by DROP_LENGTH_TOO_LONG
   If LENGTH ls < n
      Then LENGTH (TAKE n ls) = LENGTH ls   by LENGTH_TAKE_EQ
      Thus DROP n (TAKE n ls) = []          by DROP_LENGTH_TOO_LONG
*)
val DROP_TAKE_EQ_NIL = store_thm(
  "DROP_TAKE_EQ_NIL",
  ``!ls n. DROP n (TAKE n ls) = []``,
  rw[LENGTH_TAKE_EQ, DROP_LENGTH_TOO_LONG]);

(* Theorem: TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls) *)
(* Proof:
   If n <= LENGTH ls,
      Then LENGTH (TAKE n ls) = n                       by LENGTH_TAKE_EQ, n <= LENGTH ls
        DROP n (TAKE (n + m) ls)
      = DROP n (TAKE n ls ++ TAKE m (DROP n ls))        by TAKE_SUM
      = DROP n (TAKE n ls) ++ DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))  by DROP_APPEND
      = [] ++ DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))     by DROP_TAKE_EQ_NIL
      = DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))           by APPEND
      = DROP 0 (TAKE m (DROP n ls))                                  by above
      = TAKE m (DROP n ls)                                           by DROP_0
   If LENGTH ls < n,
      Then DROP n ls = []         by DROP_LENGTH_TOO_LONG
       and TAKE (n + m) ls = ls   by TAKE_LENGTH_TOO_LONG
        DROP n (TAKE (n + m) ls)
      = DROP n ls                 by TAKE_LENGTH_TOO_LONG
      = []                        by DROP_LENGTH_TOO_LONG
      = TAKE m []                 by TAKE_nil
      = TAKE m (DROP n ls)        by DROP_LENGTH_TOO_LONG
*)
val TAKE_DROP_SWAP = store_thm(
  "TAKE_DROP_SWAP",
  ``!ls m n. TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)``,
  rpt strip_tac >>
  Cases_on `n <= LENGTH ls` >| [
    qabbrev_tac `x = TAKE m (DROP n ls)` >>
    `DROP n (TAKE (n + m) ls) = DROP n (TAKE n ls ++ x)` by rw[TAKE_SUM, Abbr`x`] >>
    `_ = DROP n (TAKE n ls) ++ DROP (n - LENGTH (TAKE n ls)) x` by rw[DROP_APPEND] >>
    `_ = DROP (n - LENGTH (TAKE n ls)) x` by rw[DROP_TAKE_EQ_NIL] >>
    `_ = DROP 0 x` by rw[LENGTH_TAKE_EQ] >>
    rw[],
    `DROP n ls = []` by rw[DROP_LENGTH_TOO_LONG] >>
    `TAKE (n + m) ls = ls` by rw[TAKE_LENGTH_TOO_LONG] >>
    rw[]
  ]);

(* cf. TAKE_DROP |- !n l. TAKE n l ++ DROP n l = l *)
Theorem TAKE_DROP_SUC :
    !n l. n < LENGTH l ==> TAKE n l ++ [EL n l] ++ DROP (SUC n) l = l
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [GSYM APPEND_ASSOC, Once EQ_SYM_EQ]
 >> ‘l = TAKE n l ++ DROP n l’ by rw [TAKE_DROP]
 >> POP_ASSUM
      (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap)
 >> RW_TAC bool_ss [DROP_BY_DROP_SUC, GSYM CONS_APPEND]
QED

(* Theorem: TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1 *)
(* Proof:
      TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2))
    = TAKE (LENGTH l1) (l1 ++ LUPDATE x k l2)      by LUPDATE_APPEND2
    = l1                                           by TAKE_LENGTH_APPEND
*)
val TAKE_LENGTH_APPEND2 = store_thm(
  "TAKE_LENGTH_APPEND2",
  ``!l1 l2 x k. TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1``,
  rw_tac std_ss[LUPDATE_APPEND2, TAKE_LENGTH_APPEND]);

(* Theorem: LENGTH (TAKE n l) <= LENGTH l *)
(* Proof: by LENGTH_TAKE_EQ *)
val LENGTH_TAKE_LE = store_thm(
  "LENGTH_TAKE_LE",
  ``!n l. LENGTH (TAKE n l) <= LENGTH l``,
  rw[LENGTH_TAKE_EQ]);

(* Theorem: ALL_DISTINCT ls ==>
            !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F *)
(* Proof:
   By induction on ls.
   Base: ALL_DISTINCT [] ==> !k e. MEM e (TAKE k []) /\ MEM e (DROP k []) ==> F
         MEM e (TAKE k []) = MEM e [] = F      by TAKE_nil, MEM
         MEM e (DROP k []) = MEM e [] = F      by DROP_nil, MEM
   Step: ALL_DISTINCT ls ==>
             !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F ==>
         !h. ALL_DISTINCT (h::ls) ==>
             !k e. MEM e (TAKE k (h::ls)) /\ MEM e (DROP k (h::ls)) ==> F
         Note ~MEM h ls /\ ALL_DISTINCT ls     by ALL_DISTINCT
         If k = 0,
                MEM e (TAKE 0 (h::ls))
            <=> MEM e [] = F                   by TAKE_0, MEM
            hence true.
         If k <> 0,
                MEM e (TAKE k (h::ls))
            <=> MEM e (h::TAKE (k - 1) ls)       by TAKE_def, k <> 0
            <=> e = h \/ MEM e (TAKE (k - 1) ls) by MEM
              MEM e (DROP k (h::ls))
            <=> MEM e (DROP (k - 1) ls)          by DROP_def, k <> 0
            ==> MEM e ls                         by MEM_DROP_IMP
            If e = h,
               this contradicts ~MEM h ls.
            If MEM e (TAKE (k - 1) ls)
               this contradicts the induction hypothesis.
*)
Theorem ALL_DISTINCT_TAKE_DROP:
  !ls. ALL_DISTINCT ls ==>
   !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F
Proof
  Induct >-
  simp[] >>
  rw[] >>
  Cases_on `k = 0` >-
  fs[] >>
  spose_not_then strip_assume_tac >>
  rfs[] >-
  metis_tac[MEM_DROP_IMP] >>
  metis_tac[]
QED

(* Theorem: ALL_DISTINCT (x::y::ls) <=> ALL_DISTINCT (y::x::ls) *)
(* Proof:
   If x = y, this is trivial.
   If x <> y,
       ALL_DISTINCT (x::y::ls)
   <=> (x <> y /\ ~MEM x ls) /\ ~MEM y ls /\ ALL_DISTINCT ls   by ALL_DISTINCT
   <=> (y <> x /\ ~MEM y ls) /\ ~MEM x ls /\ ALL_DISTINCT ls
   <=> ALL_DISTINCT (y::x::ls)                                 by ALL_DISTINCT
*)
Theorem ALL_DISTINCT_SWAP:
  !ls x y. ALL_DISTINCT (x::y::ls) <=> ALL_DISTINCT (y::x::ls)
Proof
  rw[] >>
  metis_tac[]
QED

(* Theorem: ALL_DISTINCT ls /\ ls <> [] /\ j < LENGTH ls ==> (EL j ls = LAST ls <=> j + 1 = LENGTH ls) *)
(* Proof:
   Note 0 < LENGTH ls                          by LENGTH_EQ_0
       EL j ls = LAST ls
   <=> EL j ls = EL (PRE (LENGTH ls)) ls       by LAST_EL
   <=> j = PRE (LENGTH ls)                     by ALL_DISTINCT_EL_IMP, j < LENGTH ls
   <=> j + 1 = LENGTH ls                       by SUC_PRE, ADD1, 0 < LENGTH ls
*)
Theorem ALL_DISTINCT_LAST_EL_IFF:
  !ls j. ALL_DISTINCT ls /\ ls <> [] /\ j < LENGTH ls ==> (EL j ls = LAST ls <=> j + 1 = LENGTH ls)
Proof
  rw[LAST_EL] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO] >>
  `PRE (LENGTH ls) + 1 = LENGTH ls` by decide_tac >>
  `EL j ls = EL (PRE (LENGTH ls)) ls <=> j = PRE (LENGTH ls)` by fs[ALL_DISTINCT_EL_IMP] >>
  simp[]
QED

(* Theorem: ALL_DISTINCT ls /\ j < LENGTH ls /\ ls = l1 ++ [EL j ls] ++ l2 ==> j = LENGTH l1 *)
(* Proof:
   Note EL j ls = EL (LENGTH l1) ls            by el_append3
    and LENGTH l1 < LENGTH ls                  by LENGTH_APPEND
     so j = LENGTH l1                          by ALL_DISTINCT_EL_IMP
*)
Theorem ALL_DISTINCT_EL_APPEND:
  !ls l1 l2 j. ALL_DISTINCT ls /\ j < LENGTH ls /\ ls = l1 ++ [EL j ls] ++ l2 ==> j = LENGTH l1
Proof
  rpt strip_tac >>
  `EL j ls = EL (LENGTH l1) ls` by metis_tac[el_append3] >>
  `LENGTH ls = LENGTH l1 + 1 + LENGTH l2` by metis_tac[LENGTH_APPEND, LENGTH_SING] >>
  `LENGTH l1 < LENGTH ls` by decide_tac >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Theorem: ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2)) *)
(* Proof:
   By induction on l1.
   Base: ALL_DISTINCT ([] ++ [x] ++ l2) <=> ALL_DISTINCT (x::([] ++ l2))
             ALL_DISTINCT ([] ++ [x] ++ l2)
         <=> ALL_DISTINCT (x::l2)                  by APPEND_NIL
         <=> ALL_DISTINCT (x::([] ++ l2))          by APPEND_NIL
   Step: ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2)) ==>
         !h. ALL_DISTINCT (h::l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(h::l1 ++ l2))

             ALL_DISTINCT (h::l1 ++ [x] ++ l2)
         <=> ALL_DISTINCT (h::(l1 ++ [x] ++ l2))   by APPEND
         <=> ~MEM h (l1 ++ [x] ++ l2) /\
             ALL_DISTINCT (l1 ++ [x] ++ l2)        by ALL_DISTINCT
         <=> ~MEM h (l1 ++ [x] ++ l2) /\
             ALL_DISTINCT (x::(l1 ++ l2))          by induction hypothesis
         <=> ~MEM h (x::(l1 ++ l2)) /\
             ALL_DISTINCT (x::(l1 ++ l2))          by MEM_APPEND_3
         <=> ALL_DISTINCT (h::x::(l1 ++ l2))       by ALL_DISTINCT
         <=> ALL_DISTINCT (x::h::(l1 ++ l2))       by ALL_DISTINCT_SWAP
         <=> ALL_DISTINCT (x::(h::l1 ++ l2))       by APPEND
*)
Theorem ALL_DISTINCT_APPEND_3:
  !l1 x l2. ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2))
Proof
  rpt strip_tac >>
  Induct_on `l1` >-
  simp[] >>
  rpt strip_tac >>
  `ALL_DISTINCT (h::l1 ++ [x] ++ l2) <=> ALL_DISTINCT (h::(l1 ++ [x] ++ l2))` by rw[] >>
  `_ = (~MEM h (l1 ++ [x] ++ l2) /\ ALL_DISTINCT (l1 ++ [x] ++ l2))` by rw[] >>
  `_ = (~MEM h (l1 ++ [x] ++ l2) /\ ALL_DISTINCT (x::(l1 ++ l2)))` by rw[] >>
  `_ = (~MEM h (x::(l1 ++ l2)) /\ ALL_DISTINCT (x::(l1 ++ l2)))` by rw[MEM_APPEND_3] >>
  `_ = ALL_DISTINCT (h::x::(l1 ++ l2))` by rw[] >>
  `_ = ALL_DISTINCT (x::h::(l1 ++ l2))` by rw[ALL_DISTINCT_SWAP] >>
  `_ = ALL_DISTINCT (x::(h::l1 ++ l2))` by metis_tac[APPEND] >>
  simp[]
QED

(* Theorem: ALL_DISTINCT l ==> !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2 *)
(* Proof:
   If part: MEM x l ==> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
      Note ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p2    by MEM_SPLIT_APPEND_last
       Now ALL_DISTINCT (p1 ++ [x])              by ALL_DISTINCT_APPEND, ALL_DISTINCT l
       But MEM x [x]                             by MEM
        so ~MEM x p1                             by ALL_DISTINCT_APPEND

   Only-if part: MEM x (p1 ++ [x] ++ p2), true   by MEM_APPEND
*)
Theorem MEM_SPLIT_APPEND_distinct:
  !l. ALL_DISTINCT l ==> !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[MEM_SPLIT_APPEND_last, ALL_DISTINCT_APPEND, MEM] >>
  rw[]
QED

(* Theorem: MEM x ls <=>
            ?k. k < LENGTH ls /\ x = EL k ls /\
                ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (TAKE k ls) *)
(* Proof:
   If part: MEM x ls ==> ?k. k < LENGTH ls /\ x = EL k ls /\
                         ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (TAKE k ls)
      Note ?pfx sfx. ls = pfx ++ [x] ++ sfx /\ ~MEM x pfx
                                   by MEM_SPLIT_APPEND_first
      Take k = LENGTH pfx.
      Then k < LENGTH ls           by LENGTH_APPEND
       and EL k ls
         = EL k (pfx ++ [x] ++ sfx)
         = x                       by el_append3
       and TAKE k ls ++ x::DROP (k+1) ls
         = TAKE k (pfx ++ [x] ++ sfx) ++
           [x] ++
           DROP (k+1) ((pfx ++ [x] ++ sfx))
         = pfx ++ [x] ++           by TAKE_APPEND1
           (DROP (k+1)(pfx + [x])
           ++ sfx                  by DROP_APPEND1
         = pfx ++ [x] ++ sfx       by DROP_LENGTH_NIL
         = ls
       and TAKE k ls = pfx         by TAKE_APPEND1
   Only-if part: k < LENGTH ls /\ ls = TAKE k ls ++ [EL k ls] ++ DROP (k + 1) ls /\
                 ~MEM (EL k ls) (TAKE k ls) ==> MEM (EL k ls) ls
       This is true                by EL_MEM, just need k < LENGTH ls
*)
Theorem MEM_SPLIT_TAKE_DROP_first:
  !ls x. MEM x ls <=>
      ?k. k < LENGTH ls /\ x = EL k ls /\
          ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (TAKE k ls)
Proof
  rw[EQ_IMP_THM] >| [
    imp_res_tac MEM_SPLIT_APPEND_first >>
    qexists_tac `LENGTH pfx` >>
    rpt strip_tac >-
    fs[] >-
    fs[el_append3] >-
    fs[TAKE_APPEND1, DROP_APPEND1] >>
    `TAKE (LENGTH pfx) ls = pfx` by rw[TAKE_APPEND1] >>
    fs[],
    fs[EL_MEM]
  ]
QED

(* Theorem: MEM x ls <=>
            ?k. k < LENGTH ls /\ x = EL k ls /\
                ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (DROP (k+1) ls) *)
(* Proof:
   If part: MEM x ls ==> ?k. k < LENGTH ls /\ x = EL k ls /\
                         ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (DROP (k+1) ls)
      Note ?pfx sfx. ls = pfx ++ [x] ++ sfx /\ ~MEM x sfx
                                   by MEM_SPLIT_APPEND_last
      Take k = LENGTH pfx.
      Then k < LENGTH ls           by LENGTH_APPEND
       and EL k ls
         = EL k (pfx ++ [x] ++ sfx)
         = x                       by el_append3
       and TAKE k ls ++ x::DROP (k+1) ls
         = TAKE k (pfx ++ [x] ++ sfx) ++
           [x] ++
           DROP (k+1) ((pfx ++ [x] ++ sfx))
         = pfx ++ [x] ++           by TAKE_APPEND1
           (DROP (k+1)(pfx + [x])
           ++ sfx                  by DROP_APPEND1
         = pfx ++ [x] ++ sfx       by DROP_LENGTH_NIL
         = ls
       and DROP (k + 1) ls) = sfx  by DROP_APPEND1, DROP_LENGTH_NIL
   Only-if part: k < LENGTH ls /\ ls = TAKE k ls ++ [EL k ls] ++ DROP (k + 1) ls /\
                 ~MEM (EL k ls) (DROP (k+1) ls)) ==> MEM (EL k ls) ls
       This is true                by EL_MEM, just need k < LENGTH ls
*)
Theorem MEM_SPLIT_TAKE_DROP_last:
  !ls x. MEM x ls <=>
      ?k. k < LENGTH ls /\ x = EL k ls /\
          ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (DROP (k+1) ls)
Proof
  rw[EQ_IMP_THM] >| [
    imp_res_tac MEM_SPLIT_APPEND_last >>
    qexists_tac `LENGTH pfx` >>
    rpt strip_tac >-
    fs[] >-
    fs[el_append3] >-
    fs[TAKE_APPEND1, DROP_APPEND1] >>
    `DROP (LENGTH pfx + 1) ls = sfx` by rw[DROP_APPEND1] >>
    fs[],
    fs[EL_MEM]
  ]
QED

(* Theorem: ALL_DISTINCT ls ==>
           !x. MEM x ls <=>
           ?k. k < LENGTH ls /\ x = EL k ls /\
               ls = TAKE k ls ++ x::DROP (k+1) ls /\
               ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k+1) ls) *)
(* Proof:
   If part: MEM x ls ==> ?k. k < LENGTH ls /\ x = EL k ls /\
                         ls = TAKE k ls ++ x::DROP (k+1) ls /\
                          ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k+1) ls)
      Note ?p1 p2. ls = p1 ++ [x] ++ p2 /\ ~MEM x p1 /\ ~MEM x p2
                                   by MEM_SPLIT_APPEND_distinct
      Take k = LENGTH p1.
      Then k < LENGTH ls           by LENGTH_APPEND
       and EL k ls
         = EL k (p1 ++ [x] ++ p2)
         = x                       by el_append3
       and TAKE k ls ++ x::DROP (k+1) ls
         = TAKE k (p1 ++ [x] ++ p2) ++
           [x] ++
           DROP (k+1) ((p1 ++ [x] ++ p2))
         = p1 ++ [x] ++            by TAKE_APPEND1
           (DROP (k+1)(p1 + [x])
           ++ p2                   by DROP_APPEND1
         = p1 ++ [x] ++ p2         by DROP_LENGTH_NIL
         = ls
       and TAKE k ls = p1          by TAKE_APPEND1
       and DROP (k + 1) ls) = p2   by DROP_APPEND1, DROP_LENGTH_NIL
   Only-if part: k < LENGTH ls /\ ls = TAKE k ls ++ [EL k ls] ++ DROP (k + 1) ls /\
                  ~MEM (EL k ls) (TAKE k ls) /\ ~MEM (EL k ls) (DROP (k+1) ls)) ==> MEM (EL k ls) ls
       This is true                by EL_MEM, just need k < LENGTH ls
*)
Theorem MEM_SPLIT_TAKE_DROP_distinct:
  !ls. ALL_DISTINCT ls ==>
    !x. MEM x ls <=>
    ?k. k < LENGTH ls /\ x = EL k ls /\
        ls = TAKE k ls ++ x::DROP (k+1) ls /\
         ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k+1) ls)
Proof
  rw[EQ_IMP_THM] >| [
    `?p1 p2. ls = p1 ++ [x] ++ p2 /\ ~MEM x p1 /\ ~MEM x p2` by rw[GSYM MEM_SPLIT_APPEND_distinct] >>
    qexists_tac `LENGTH p1` >>
    rpt strip_tac >-
    fs[] >-
    fs[el_append3] >-
    fs[TAKE_APPEND1, DROP_APPEND1] >-
    rfs[TAKE_APPEND1] >>
    `DROP (LENGTH p1 + 1) ls = p2` by rw[DROP_APPEND1] >>
    fs[],
    fs[EL_MEM]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* More about List Filter.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea: the j-th element of FILTER must have j elements filtered beforehand. *)

(* Theorem: let fs = FILTER P ls in ls = l1 ++ x::l2 /\ P x ==>
            x = EL (LENGTH (FILTER P l1)) fs *)
(* Proof:
   Let l3 = x::l2, then ls = l1 ++ l3.
   Let j = LENGTH (FILTER P l1).
     EL j fs
   = EL j (FILTER P ls)                        by given
   = EL j (FILTER P l1 ++ FILTER P l3)         by FILTER_APPEND_DISTRIB
   = EL 0 (FILTER P l3)                        by EL_APPEND, j = LENGTH (FILTER P l1)
   = EL 0 (FILTER P (x::l2))                   by notation
   = EL 0 (x::FILTER P l2)                     by FILTER, P x
   = x                                         by HD
*)
Theorem FILTER_EL_IMP:
  !P ls l1 l2 x. let fs = FILTER P ls in ls = l1 ++ x::l2 /\ P x ==>
                 x = EL (LENGTH (FILTER P l1)) fs
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `l3 = x::l2` >>
  qabbrev_tac `j = LENGTH (FILTER P l1)` >>
  `EL j fs = EL j (FILTER P l1 ++ FILTER P l3)` by simp[FILTER_APPEND_DISTRIB, Abbr`fs`] >>
  `_ = EL 0 (FILTER P (x::l2))` by simp[EL_APPEND, Abbr`j`, Abbr`l3`] >>
  fs[]
QED

(* Theorem: let fs = FILTER P ls in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ j < LENGTH fs ==>
            (x = EL j fs <=> P x /\ j = LENGTH (FILTER P l1)) *)
(* Proof:
   Let k = LENGTH (FILTER P l1).
   If part: j < LENGTH fs /\ x = EL j fs ==> P x /\ j = k
      Note j < LENGTH fs /\ x = EL j fs        by given
       ==> MEM x fs                            by MEM_EL
       ==> P x                                 by MEM_FILTER
      Thus x = EL k fs                         by FILTER_EL_IMP
      Let l3 = x::l2, then ls = l1 ++ l3.
      Then FILTER P l3 = x :: FILTER P l2      by FILTER
        or FILTER P l3 <> []                   by NOT_NIL_CONS
        or LENGTH (FILTER P l3) <> 0           by LENGTH_EQ_0, [1]

           LENGTH fs
         = LENGTH (FILTER P ls)                by notation
         = LENGTH (FILTER P l1 ++ FILTER P l3) by FILTER_APPEND_DISTRIB
         = k + LENGTH (FILTER P l3)            by LENGTH_APPEND
      Thus k < LENGTH fs                       by [1]

      Note ALL_DISTINCT ls
       ==> ALL_DISTINCT fs                     by FILTER_ALL_DISTINCT
      With x = EL j fs = EL k fs               by above
       and j < LENGTH fs /\ k < LENGTH fs      by above
       ==>           j = k                     by ALL_DISTINCT_EL_IMP

   Only-if part: j < LENGTH fs /\ P x /\ j = k ==> x = EL j fs
      This is true                             by FILTER_EL_IMP
*)
Theorem FILTER_EL_IFF:
  !P ls l1 l2 x j. let fs = FILTER P ls in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ j < LENGTH fs ==>
                   (x = EL j fs <=> P x /\ j = LENGTH (FILTER P l1))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `k = LENGTH (FILTER P l1)` >>
  simp[EQ_IMP_THM] >>
  ntac 2 strip_tac >| [
    `MEM x fs` by metis_tac[MEM_EL] >>
    `P x` by fs[MEM_FILTER, Abbr`fs`] >>
    qabbrev_tac `ls = l1 ++ x::l2` >>
    `EL j fs = EL k fs` by metis_tac[FILTER_EL_IMP] >>
    qabbrev_tac `l3 = x::l2` >>
    `FILTER P l3 = x :: FILTER P l2` by simp[Abbr`l3`] >>
    `LENGTH (FILTER P l3) <> 0` by fs[] >>
    `fs = FILTER P l1 ++ FILTER P l3` by fs[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`ls`] >>
    `LENGTH fs = k + LENGTH (FILTER P l3)` by fs[Abbr`k`] >>
    `k < LENGTH fs` by decide_tac >>
    `ALL_DISTINCT fs` by simp[FILTER_ALL_DISTINCT, Abbr`fs`] >>
    metis_tac[ALL_DISTINCT_EL_IMP],
    metis_tac[FILTER_EL_IMP]
  ]
QED

(* Derive theorems for head = (EL 0 fs) *)

(* Theorem: ls = l1 ++ x::l2 /\ P x /\ FILTER P l1 = [] ==> x = HD (FILTER P ls) *)
(* Proof:
   Note FILTER P l1 = []           by given
    ==> LENGTH (FILTER P l1) = 0   by LENGTH
   Thus x = EL 0 (FILTER P ls)     by FILTER_EL_IMP
          = HD (FILTER P ls)       by EL
*)
Theorem FILTER_HD:
  !P ls l1 l2 x. ls = l1 ++ x::l2 /\ P x /\ FILTER P l1 = [] ==> x = HD (FILTER P ls)
Proof
  metis_tac[LENGTH, FILTER_EL_IMP, EL]
QED

(* Theorem: ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
            (x = HD (FILTER P ls) <=> FILTER P l1 = []) *)
(* Proof:
   Let fs = FILTER P ls.
   Note MEM x ls                   by MEM_APPEND, MEM
    and P x ==> fs <> []           by MEM_FILTER, NIL_NO_MEM
     so 0 < LENGTH fs              by LENGTH_EQ_0
   Thus x = HD fs
          = EL 0 fs                by EL
    <=> LENGTH (FILTER P l1) = 0   by FILTER_EL_IFF
    <=> FILTER P l1 = []           by LENGTH_EQ_0
*)
Theorem FILTER_HD_IFF:
  !P ls l1 l2 x. ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
                 (x = HD (FILTER P ls) <=> FILTER P l1 = [])
Proof
  rpt strip_tac >>
  qabbrev_tac `fs = FILTER P ls` >>
  `MEM x ls` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `0 < LENGTH fs` by metis_tac[NIL_NO_MEM, LENGTH_EQ_0, NOT_ZERO] >>
  metis_tac[FILTER_EL_IFF, EL, LENGTH_EQ_0]
QED

(* Derive theorems for last = (EL (LENGTH fs - 1) fs) *)

(* Theorem: ls = l1 ++ x::l2 /\ P x /\ FILTER P l2 = [] ==>
            x = LAST (FILTER P ls) *)
(* Proof:
   Let fs = FILTER P ls,
        k = LENGTH fs.
   Note MEM x ls                   by MEM_APPEND, MEM
    and P x ==> fs <> []           by MEM_FILTER, NIL_NO_MEM
     so 0 < LENGTH fs = k          by LENGTH_EQ_0

   Note FILTER P l2 = []           by given
    ==> LENGTH (FILTER P l2) = 0   by LENGTH
    k = LENGTH fs
      = LENGTH (FILTER P ls)       by notation
      = LENGTH (FILTER P l1) + 1   by FILTER_APPEND_DISTRIB, ONE
     or LENGTH (FILTER P l1) = PRE k
   Thus x = EL (PRE k) fs          by FILTER_EL_IMP
          = LAST fs                by LAST_EL, fs <> []
*)
Theorem FILTER_LAST:
  !P ls l1 l2 x. ls = l1 ++ x::l2 /\ P x /\ FILTER P l2 = [] ==>
                 x = LAST (FILTER P ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `fs = FILTER P ls` >>
  qabbrev_tac `k = LENGTH fs` >>
  `MEM x ls` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `fs <> [] /\ 0 < k` by metis_tac[NIL_NO_MEM, LENGTH_EQ_0, NOT_ZERO] >>
  `k = LENGTH (FILTER P l1) + 1` by fs[FILTER_APPEND_DISTRIB, Abbr`k`, Abbr`fs`] >>
  `LENGTH (FILTER P l1) = PRE k` by decide_tac >>
  metis_tac[FILTER_EL_IMP, LAST_EL]
QED

(* Theorem: ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
            (x = LAST (FILTER P ls) <=> FILTER P l2 = []) *)
(* Proof:
   Let fs = FILTER P ls,
        k = LENGTH fs,
        j = LENGTH (FILTER P l1).
   Note MEM x ls                   by MEM_APPEND, MEM
    and P x ==> fs <> []           by MEM_FILTER, NIL_NO_MEM
     so 0 < LENGTH fs = k          by LENGTH_EQ_0
    and PRE k < k                  by arithmetic

    k = LENGTH fs
      = LENGTH (FILTER P ls)                   by notation
      = j + 1 + LENGTH (FILTER P l2)           by FILTER_APPEND_DISTRIB, ONE
     so j = PRE k <=> LENGTH (FILTER P l2) = 0 by arithmetic

   Thus x = LAST fs
          = EL (PRE k) fs          by LAST_EL
    <=> PRE k = j                  by FILTER_EL_IFF
    <=> LENGTH (FILTER P l2) = 0   by above
    <=> FILTER P l2 = []           by LENGTH_EQ_0
*)
Theorem FILTER_LAST_IFF:
  !P ls l1 l2 x. ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
                 (x = LAST (FILTER P ls) <=> FILTER P l2 = [])
Proof
  rpt strip_tac >>
  qabbrev_tac `fs = FILTER P ls` >>
  qabbrev_tac `k = LENGTH fs` >>
  qabbrev_tac `j = LENGTH (FILTER P l1)` >>
  `MEM x ls` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `fs <> [] /\ 0 < k` by metis_tac[NIL_NO_MEM, LENGTH_EQ_0, NOT_ZERO] >>
  `k = j + 1 + LENGTH (FILTER P l2)` by fs[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`k`, Abbr`j`] >>
  `PRE k < k /\ (j = PRE k <=> LENGTH (FILTER P l2) = 0)` by decide_tac >>
  metis_tac[FILTER_EL_IFF, LAST_EL, LENGTH_EQ_0]
QED

(* Idea: for FILTER over a range, the range between successive filter elements is filtered. *)

(* Theorem: let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
            ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y /\ FILTER P l2 = [] ==>
            x = EL j fs /\ y = EL (j + 1) fs *)
(* Proof:
   Let l4 = y::l3, then
       ls = l1 ++ x::l2 ++ l4
          = l1 ++ x::(l2 ++ l4)                by APPEND_ASSOC_CONS
   Thus x = EL j fs                            by FILTER_EL_IMP

   Now let l5 = l1 ++ x::l2,
           k = LENGTH (FILTER P l5).
   Then ls = l5 ++ y::l3                       by APPEND_ASSOC
    and y = EL k fs                            by FILTER_EL_IMP

   Note FILTER P l5
      = FILTER P l1 ++ FILTER P (x::l2)        by FILTER_APPEND_DISTRIB
      = FILTER P l1 ++ x :: FILTER P l2        by FILTER
      = FILTER P l1 ++ [x]                     by FILTER P l2 = []
    and k = LENGTH (FILTER P l5)
          = LENGTH (FILTER P l1 ++ [x])        by above
          = j + 1                              by LENGTH_APPEND
*)
Theorem FILTER_EL_NEXT:
  !P ls l1 l2 l3 x y. let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
                      ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y /\ FILTER P l2 = [] ==>
                      x = EL j fs /\ y = EL (j + 1) fs
Proof
  rw_tac std_ss[] >| [
    qabbrev_tac `l4 = y::l3` >>
    qabbrev_tac `ls = l1 ++ x::l2 ++ l4` >>
    `ls = l1 ++ x::(l2 ++ l4)` by simp[Abbr`ls`] >>
    metis_tac[FILTER_EL_IMP],
    qabbrev_tac `l5 = l1 ++ x::l2` >>
    qabbrev_tac `ls = l5 ++ y::l3` >>
    `FILTER P l5 = FILTER P l1 ++ [x]` by fs[FILTER_APPEND_DISTRIB, Abbr`l5`] >>
    `LENGTH (FILTER P l5) = j + 1` by fs[Abbr`j`] >>
    metis_tac[FILTER_EL_IMP]
  ]
QED

(* Theorem: let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
             ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
             (x = EL j fs /\ y = EL (j + 1) fs <=> FILTER P l2 = []) *)
(* Proof:
   Note fs = FILTER P ls
           = FILTER P (l1 ++ x::l2 ++ y::l3)   by given
           = FILTER P l1 ++
             x :: FILTER P l2 ++
             y :: FILTER P l3                  by FILTER_APPEND_DISTRIB, FILTER
   Thus LENGTH fs
      = j + SUC (LENGTH (FILTER P l2))
          + SUC (LENGTH (FILTER P l3))         by LENGTH_APPEND
     or j + 2 <= LENGTH fs                     by arithmetic
     or j < LENGTH fs, j + 1 < LENGTH fs       by inequality

   Let l4 = y::l3, then
       ls = l1 ++ x::l2 ++ l4
          = l1 ++ x::(l2 ++ l4)                by APPEND_ASSOC_CONS
   Thus x = EL j fs                            by FILTER_EL_IFF, j < LENGTH fs

   Now let l5 = l1 ++ x::l2,
           k = LENGTH (FILTER P l5).
   Then ls = l5 ++ y::l3                       by APPEND_ASSOC
    and fs = FILTER P l5 ++
             y :: FILTER P l3                  by FILTER_APPEND_DISTRIB, FILTER
     so LENGTH fs = k + SUC (LENGTH P l3)      by LENGTH_APPEND
   Thus k < LENGTH fs
    and y = EL k fs                            by FILTER_EL_IFF

   Also FILTER P l5 = FILTER P l1 ++
                      x :: FILTER P l2         by FILTER_APPEND_DISTRIB, FILTER
     so k = j + SUC (LENGTH (FILTER P l2))     by LENGTH_APPEND
   Thus k = j + 1
    <=> LENGTH (FILTER P l2) = 0               by arithmetic

   Note ALL_DISTINCT fs                        by FILTER_ALL_DISTINCT
     so EL k fs = EL (j + 1) fs
    <=> k = j + 1
    <=> LENGTH (FILTER P l2) = 0               by above
    <=> FILTER P l2 = []                       by LENGTH_EQ_0
*)
Theorem FILTER_EL_NEXT_IFF:
  !P ls l1 l2 l3 x y. let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
                      ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
                      (x = EL j fs /\ y = EL (j + 1) fs <=> FILTER P l2 = [])
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ls = l1 ++ x::l2 ++ y::l3` >>
  `j + 2 <= LENGTH fs` by
  (`fs = FILTER P l1 ++ x::FILTER P l2 ++ y::FILTER P l3` by simp[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`ls`] >>
  `LENGTH fs = j + SUC (LENGTH (FILTER P l2)) + SUC (LENGTH (FILTER P l3))` by fs[Abbr`j`] >>
  decide_tac) >>
  `j < LENGTH fs` by decide_tac >>
  qabbrev_tac `l4 = y::l3` >>
  `ls = l1 ++ x::(l2 ++ l4)` by simp[Abbr`ls`] >>
  `x = EL j fs` by metis_tac[FILTER_EL_IFF] >>
  qabbrev_tac `l5 = l1 ++ x::l2` >>
  qabbrev_tac `k = LENGTH (FILTER P l5)` >>
  `ls = l5 ++ y::l3` by simp[Abbr`l5`, Abbr`ls`] >>
  `k < LENGTH fs /\ (k = j + 1 <=> FILTER P l2 = [])` by
    (`fs = FILTER P l5 ++ y::FILTER P l3` by rfs[FILTER_APPEND_DISTRIB, Abbr`fs`] >>
  `LENGTH fs = k + SUC (LENGTH (FILTER P l3))` by fs[Abbr`k`] >>
  `FILTER P l5 = FILTER P l1 ++ x :: FILTER P l2` by rfs[FILTER_APPEND_DISTRIB, Abbr`l5`] >>
  `k = j + SUC (LENGTH (FILTER P l2))` by fs[Abbr`k`, Abbr`j`] >>
  simp[]) >>
  `y = EL k fs` by metis_tac[FILTER_EL_IFF] >>
  `j + 1 < LENGTH fs` by decide_tac >>
  `ALL_DISTINCT fs` by simp[FILTER_ALL_DISTINCT, Abbr`fs`] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* ------------------------------------------------------------------------- *)
(* Unit-List and Mono-List                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (LENGTH l = 1) ==> SING (set l) *)
(* Proof:
   Since ?x. l = [x]   by LENGTH_EQ_1
         set l = {x}   by LIST_TO_SET_DEF
      or SING (set l)  by SING_DEF
*)
val SING_LIST_TO_SET = store_thm((* was: LIST_TO_SET_SING *)
  "SING_LIST_TO_SET",
  ``!l. (LENGTH l = 1) ==> SING (set l)``,
  rw[LENGTH_EQ_1, SING_DEF] >>
  `set [x] = {x}` by rw[] >>
  metis_tac[]);

(* Mono-list Theory: a mono-list is a list l with SING (set l) *)

(* Theorem: Two mono-lists are equal if their lengths and sets are equal.
            SING (set l1) /\ SING (set l2) ==>
            ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2)) *)
(* Proof:
   By induction on l1.
   Base case: !l2. SING (set []) /\ SING (set l2) ==>
              (([] = l2) <=> (LENGTH [] = LENGTH l2) /\ (set [] = set l2))
     True by SING (set []) is False, by SING_EMPTY.
   Step case: !l2. SING (set l1) /\ SING (set l2) ==>
              ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2)) ==>
              !h l2. SING (set (h::l1)) /\ SING (set l2) ==>
              ((h::l1 = l2) <=> (LENGTH (h::l1) = LENGTH l2) /\ (set (h::l1) = set l2))
     This is to show:
     (1) 1 = LENGTH l2 /\ {h} = set l2 ==>
         ([h] = l2) <=> (SUC (LENGTH []) = LENGTH l2) /\ (h INSERT set [] = set l2)
         If-part, l2 = [h],
              LENGTH l2 = 1 = SUC 0 = SUC (LENGTH [])   by LENGTH, ONE
          and set l2 = set [h] = {h} = h INSERT set []  by LIST_TO_SET
         Only-if part, LENGTH l2 = SUC 0 = 1            by ONE
            Then ?x. l2 = [x]                           by LENGTH_EQ_1
              so set l2 = {x} = {h}                     by LIST_TO_SET
              or x = h, hence l2 = [h]                  by EQUAL_SING
     (2) set l1 = {h} /\ SING (set l2) ==>
         (h::l1 = l2) <=> (SUC (LENGTH l1) = LENGTH l2) /\ (h INSERT set l1 = set l2)
         If part, h::l1 = l2.
            Then LENGTH l2 = LENGTH (h::l1) = SUC (LENGTH l1)  by LENGTH
             and set l2 = set (h::l1) = h INSERT set l1        by LIST_TO_SET
         Only-if part, SUC (LENGTH l1) = LENGTH l2.
            Since 0 < SUC (LENGTH l1)   by prim_recTheory.LESS_0
                  0 < LENGTH l2         by LESS_TRANS
               so ?k t. l2 = k::t       by LENGTH_NON_NIL, list_CASES
            Since LENGTH l2 = SUC (LENGTH t)   by LENGTH
                  LENGTH l1 = LENGTH t         by prim_recTheory.INV_SUC_EQ
              and set l2 = k INSERT set t      by LIST_TO_SET
            Given SING (set l2),
            either (set t = {}), or (set t = {k})  by SING_INSERT
            If set t = {},
               then t = []              by LIST_TO_SET_EQ_EMPTY
                and l1 = []             by LENGTH_NIL, LENGTH l1 = LENGTH t.
                 so set l1 = {}         by LIST_TO_SET_EQ_EMPTY
            contradicting set l1 = {h}  by NOT_SING_EMPTY
            If set t = {k},
               then set l2 = set t      by ABSORPTION, set l2 = k INSERT set {k}.
                 or k = h               by IN_SING
                 so l1 = t              by induction hypothesis
             giving l2 = h::l1
*)
Theorem MONOLIST_EQ:
  !l1 l2. SING (set l1) /\ SING (set l2) ==>
          ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2))
Proof
  Induct >> rw[NOT_SING_EMPTY, SING_INSERT] >| [
    Cases_on `l2` >> rw[] >>
    full_simp_tac (srw_ss()) [SING_INSERT, EQUAL_SING] >>
    rw[LENGTH_NIL, NOT_SING_EMPTY, EQUAL_SING] >> metis_tac[],
    Cases_on `l2` >> rw[] >>
    full_simp_tac (srw_ss()) [SING_INSERT, LENGTH_NIL, NOT_SING_EMPTY,
                              EQUAL_SING] >>
    metis_tac[]
  ]
QED

(* Theorem: A non-mono-list has at least one element in tail that is distinct from its head.
           ~SING (set (h::t)) ==> ?h'. h' IN set t /\ h' <> h *)
(* Proof:
   By SING_INSERT, this is to show:
      t <> [] /\ set t <> {h} ==> ?h'. MEM h' t /\ h' <> h
   Now, t <> [] ==> set t <> {}   by LIST_TO_SET_EQ_EMPTY
     so ?e. e IN set t            by MEMBER_NOT_EMPTY
     hence MEM e t,
       and MEM x t <=/=> (x = h)  by EXTENSION
   Therefore, e <> h, so take h' = e.
*)
val NON_MONO_TAIL_PROPERTY = store_thm(
  "NON_MONO_TAIL_PROPERTY",
  ``!l. ~SING (set (h::t)) ==> ?h'. h' IN set t /\ h' <> h``,
  rw[SING_INSERT] >>
  `set t <> {}` by metis_tac[LIST_TO_SET_EQ_EMPTY] >>
  `?e. e IN set t` by metis_tac[MEMBER_NOT_EMPTY] >>
  full_simp_tac (srw_ss())[EXTENSION] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* GENLIST Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GENLIST (K e) (SUC n) = e :: GENLIST (K e) n *)
(* Proof:
     GENLIST (K e) (SUC n)
   = (K e) 0::GENLIST ((K e) o SUC) n   by GENLIST_CONS
   = e :: GENLIST ((K e) o SUC) n       by K_THM
   = e :: GENLIST (K e) n               by K_o_THM
*)
val GENLIST_K_CONS = save_thm("GENLIST_K_CONS",
    SIMP_CONV (srw_ss()) [GENLIST_CONS]
      ``GENLIST (K e) (SUC n)`` |> GEN ``n:num`` |> GEN ``e``);
(* val GENLIST_K_CONS = |- !e n. GENLIST (K e) (SUC n) = e::GENLIST (K e) n: thm  *)

(* Theorem: GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n *)
(* Proof:
   Note (\t. e) = K e    by FUN_EQ_THM
     GENLIST (K e) (n + m)
   = GENLIST (K e) m ++ GENLIST (\t. (K e) (t + m)) n    by GENLIST_APPEND
   = GENLIST (K e) m ++ GENLIST (\t. e) n                by K_THM
   = GENLIST (K e) m ++ GENLIST (K e) n                  by above
*)
val GENLIST_K_ADD = store_thm(
  "GENLIST_K_ADD",
  ``!e n m. GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n``,
  rpt strip_tac >>
  `(\t. e) = K e` by rw[FUN_EQ_THM] >>
  rw[GENLIST_APPEND] >>
  metis_tac[]);

(* Theorem: (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n) *)
(* Proof:
   By induction on n.
   Base: GENLIST f 0 = GENLIST (K e) 0
        GENLIST f 0
      = []                          by GENLIST_0
      = GENLIST (K e) 0             by GENLIST_0
   Step: GENLIST f n = GENLIST (K e) n ==>
         GENLIST f (SUC n) = GENLIST (K e) (SUC n)
        GENLIST f (SUC n)
      = SNOC (f n) (GENLIST f n)    by GENLIST
      = SNOC e (GENLIST f n)        by applying f to n
      = SNOC e (GENLIST (K e) n)    by induction hypothesis
      = GENLIST (K e) (SUC n)       by GENLIST
*)
val GENLIST_K_LESS = store_thm(
  "GENLIST_K_LESS",
  ``!f e n. (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[GENLIST]);

(* Theorem: (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n) *)
(* Proof:
   Base: GENLIST (f o SUC) 0 = GENLIST (K e) 0
         GENLIST (f o SUC) 0
       = []                                by GENLIST_0
       = GENLIST (K e) 0                   by GENLIST_0
   Step: GENLIST (f o SUC) n = GENLIST (K e) n ==>
         GENLIST (f o SUC) (SUC n) = GENLIST (K e) (SUC n)
         GENLIST (f o SUC) (SUC n)
       = SNOC (f n) (GENLIST (f o SUC) n)  by GENLIST
       = SNOC e (GENLIST (f o SUC) n)      by applying f to n
       = SNOC e GENLIST (K e) n            by induction hypothesis
       = GENLIST (K e) (SUC n)             by GENLIST
*)
val GENLIST_K_RANGE = store_thm(
  "GENLIST_K_RANGE",
  ``!f e n. (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[GENLIST]);

(* Theorem: GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b) *)
(* Proof:
   Note (\t. c) = K c           by FUN_EQ_THM
     GENLIST (K c) (a + b)
   = GENLIST (K c) (b + a)                              by ADD_COMM
   = GENLIST (K c) a ++ GENLIST (\t. (K c) (t + a)) b   by GENLIST_APPEND
   = GENLIST (K c) a ++ GENLIST (\t. c) b               by applying constant function
   = GENLIST (K c) a ++ GENLIST (K c) b                 by GENLIST_FUN_EQ
*)
val GENLIST_K_APPEND = store_thm(
  "GENLIST_K_APPEND",
  ``!a b c. GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b)``,
  rpt strip_tac >>
  `(\t. c) = K c` by rw[FUN_EQ_THM] >>
  `GENLIST (K c) (a + b) = GENLIST (K c) (b + a)` by rw[] >>
  `_ = GENLIST (K c) a ++ GENLIST (\t. (K c) (t + a)) b` by rw[GENLIST_APPEND] >>
  rw[GENLIST_FUN_EQ]);

(* Theorem: GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n *)
(* Proof:
     GENLIST (K c) n ++ [c]
   = GENLIST (K c) n ++ GENLIST (K c) 1      by GENLIST_1
   = GENLIST (K c) (n + 1)                   by GENLIST_K_APPEND
   = GENLIST (K c) (1 + n)                   by ADD_COMM
   = GENLIST (K c) 1 ++ GENLIST (K c) n      by GENLIST_K_APPEND
   = [c] ++ GENLIST (K c) n                  by GENLIST_1
*)
val GENLIST_K_APPEND_K = store_thm(
  "GENLIST_K_APPEND_K",
  ``!c n. GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n``,
  metis_tac[GENLIST_K_APPEND, GENLIST_1, ADD_COMM, combinTheory.K_THM]);

(* Theorem: 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c)) *)
(* Proof:
       MEM x (GENLIST (K c) n
   <=> ?m. m < n /\ (x = (K c) m)    by MEM_GENLIST
   <=> ?m. m < n /\ (x = c)          by K_THM
   <=> (x = c)                       by taking m = 0, 0 < n
*)
Theorem GENLIST_K_MEM:
  !x c n. 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c))
Proof
  metis_tac[MEM_GENLIST, combinTheory.K_THM]
QED

(* Theorem: 0 < n ==> (set (GENLIST (K c) n) = {c}) *)
(* Proof:
   By induction on n.
   Base: 0 < 0 ==> (set (GENLIST (K c) 0) = {c})
      Since 0 < 0 = F, hence true.
   Step: 0 < n ==> (set (GENLIST (K c) n) = {c}) ==>
         0 < SUC n ==> (set (GENLIST (K c) (SUC n)) = {c})
      If n = 0,
        set (GENLIST (K c) (SUC 0)
      = set (GENLIST (K c) 1          by ONE
      = set [(K c) 0]                 by GENLIST_1
      = set [c]                       by K_THM
      = {c}                           by LIST_TO_SET
      If n <> 0, 0 < n.
        set (GENLIST (K c) (SUC n)
      = set (SNOC ((K c) n) (GENLIST (K c) n))     by GENLIST
      = set (SNOC c (GENLIST (K c) n)              by K_THM
      = c INSERT set (GENLIST (K c) n)             by LIST_TO_SET_SNOC
      = c INSERT {c}                               by induction hypothesis
      = {c}                                        by IN_INSERT
 *)
Theorem GENLIST_K_SET:
  !c n. 0 < n ==> (set (GENLIST (K c) n) = {c})
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  (Cases_on `n = 0` >> simp[]) >>
  `0 < n` by decide_tac >>
  simp[GENLIST, LIST_TO_SET_SNOC]
QED

(* Theorem: ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> (SING (set []) <=> ?c. [] = GENLIST (K c) (LENGTH []))
     Since [] <> [] = F, hence true.
   Step: ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls)) ==>
         !h. h::ls <> [] ==>
             (SING (set (h::ls)) <=> ?c. h::ls = GENLIST (K c) (LENGTH (h::ls)))
     Note h::ls <> [] = T.
     If part: SING (set (h::ls)) ==> ?c. h::ls = GENLIST (K c) (LENGTH (h::ls))
        Note SING (set (h::ls)) means
             set ls = {h}                by LIST_TO_SET_DEF, IN_SING
         Let n = LENGTH ls, 0 < n        by LENGTH_NON_NIL
        Note ls <> []                    by LIST_TO_SET, IN_SING, MEMBER_NOT_EMPTY
         and SING (set ls)               by SING_DEF
         ==> ?c. ls = GENLIST (K c) n    by induction hypothesis
          so set ls = {c}                by GENLIST_K_SET, 0 < n
         ==> h = c                       by IN_SING
           GENLIST (K c) (LENGTH (h::ls)
         = (K c) h :: ls                 by GENLIST_K_CONS
         = c :: ls                       by K_THM
         = h::ls                         by h = c
     Only-if part: ?c. h::ls = GENLIST (K c) (LENGTH (h::ls)) ==> SING (set (h::ls))
           set (h::ls)
         = set (GENLIST (K c) (LENGTH (h::ls)))        by given
         = set ((K c) h :: GENLIST (K c) (LENGTH ls))  by GENLIST_K_CONS
         = set (c :: GENLIST (K c) (LENGTH ls))        by K_THM
         = c INSERT set (GENLIST (K c) (LENGTH ls))    by LIST_TO_SET
         = c INSERT {c}                                by GENLIST_K_SET
         = {c}                                         by IN_INSERT
         Hence SING (set (h::ls))                      by SING_DEF
*)
Theorem LIST_TO_SET_SING_IFF:
  !ls. ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls))
Proof
  Induct >-
  simp[] >>
  (rw[EQ_IMP_THM] >> simp[]) >| [
    qexists_tac `h` >>
    qabbrev_tac `n = LENGTH ls` >>
    `ls <> []` by metis_tac[LIST_TO_SET, IN_SING, MEMBER_NOT_EMPTY] >>
    `SING (set ls)` by fs[SING_DEF] >>
    fs[] >>
    `0 < n` by metis_tac[LENGTH_NON_NIL] >>
    `h = c` by metis_tac[GENLIST_K_SET, IN_SING] >>
    simp[GENLIST_K_CONS],
    spose_not_then strip_assume_tac >>
    fs[GENLIST_K_CONS] >>
    `0 < LENGTH ls` by metis_tac[LENGTH_NON_NIL] >>
    metis_tac[GENLIST_K_SET]
  ]
QED

(* Theorem: ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x]) *)
(* Proof:
   If part: ALL_DISTINCT l /\ set l = {x} ==> l = [x]
      Note set l = {x}
       ==> l <> [] /\ EVERY ($= x) l   by LIST_TO_SET_EQ_SING
      Let P = (S= x).
      Note l <> [] ==> ?h t. l = h::t  by list_CASES
        so h = x /\ EVERY P t             by EVERY_DEF
       and ~(MEM h t) /\ ALL_DISTINCT t   by ALL_DISTINCT
      By contradiction, suppose l <> [x].
      Then t <> [] ==> ?u v. t = u::v     by list_CASES
       and MEM u t                        by MEM
       but u = h                          by EVERY_DEF
       ==> MEM h t, which contradicts ~(MEM h t).

   Only-if part: l = [x] ==> ALL_DISTINCT l /\ set l = {x}
       Note ALL_DISTINCT [x] = T     by ALL_DISTINCT_SING
        and set [x] = {x}            by MONO_LIST_TO_SET
*)
val DISTINCT_LIST_TO_SET_EQ_SING = store_thm(
  "DISTINCT_LIST_TO_SET_EQ_SING",
  ``!l x. ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x])``,
  rw[EQ_IMP_THM] >>
  qabbrev_tac `P = ($= x)` >>
  `!y. P y ==> (y = x)` by rw[Abbr`P`] >>
  `l <> [] /\ EVERY P l` by metis_tac[LIST_TO_SET_EQ_SING, Abbr`P`] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  `(h = x) /\ (EVERY P t)` by metis_tac[EVERY_DEF] >>
  `~(MEM h t) /\ ALL_DISTINCT t` by metis_tac[ALL_DISTINCT] >>
  spose_not_then strip_assume_tac >>
  `t <> []` by rw[] >>
  `?u v. t = u::v` by metis_tac[list_CASES] >>
  `MEM u t` by rw[] >>
  metis_tac[EVERY_DEF]);

(* ------------------------------------------------------------------------- *)
(* Maximum of a List                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define MAX of a list *)
val MAX_LIST_def = Define`
    (MAX_LIST [] = 0) /\
    (MAX_LIST (h::t) = MAX h (MAX_LIST t))
`;

(* export simple recursive definition *)
(* val _ = export_rewrites["MAX_LIST_def"]; *)

(* Theorem: MAX_LIST [] = 0 *)
(* Proof: by MAX_LIST_def *)
val MAX_LIST_NIL = save_thm("MAX_LIST_NIL", MAX_LIST_def |> CONJUNCT1);
(* val MAX_LIST_NIL = |- MAX_LIST [] = 0: thm *)

(* Theorem: MAX_LIST (h::t) = MAX h (MAX_LIST t) *)
(* Proof: by MAX_LIST_def *)
val MAX_LIST_CONS = save_thm("MAX_LIST_CONS", MAX_LIST_def |> CONJUNCT2);
(* val MAX_LIST_CONS = |- !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t): thm *)

(* export simple results *)
val _ = export_rewrites["MAX_LIST_NIL", "MAX_LIST_CONS"];

(* Theorem: MAX_LIST [x] = x *)
(* Proof:
     MAX_LIST [x]
   = MAX x (MAX_LIST [])   by MAX_LIST_CONS
   = MAX x 0               by MAX_LIST_NIL
   = x                     by MAX_0
*)
val MAX_LIST_SING = store_thm(
  "MAX_LIST_SING",
  ``!x. MAX_LIST [x] = x``,
  rw[]);

(* Theorem: (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l *)
(* Proof:
   By induction on l.
   Base: (MAX_LIST [] = 0) <=> EVERY (\x. x = 0) []
      LHS: MAX_LIST [] = 0, true           by MAX_LIST_NIL
      RHS: EVERY (\x. x = 0) [], true      by EVERY_DEF
   Step: (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l ==>
         !h. (MAX_LIST (h::l) = 0) <=> EVERY (\x. x = 0) (h::l)
          MAX_LIST (h::l) = 0
      <=> MAX h (MAX_LIST l) = 0           by MAX_LIST_CONS
      <=> (h = 0) /\ (MAX_LIST l = 0)      by MAX_EQ_0
      <=> (h = 0) /\ EVERY (\x. x = 0) l   by induction hypothesis
      <=> EVERY (\x. x = 0) (h::l)         by EVERY_DEF
*)
val MAX_LIST_EQ_0 = store_thm(
  "MAX_LIST_EQ_0",
  ``!l. (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l``,
  Induct >>
  rw[MAX_EQ_0]);

(* Theorem: l <> [] ==> MEM (MAX_LIST l) l *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> MEM (MAX_LIST []) []
      Trivially true by [] <> [] = F.
   Step: l <> [] ==> MEM (MAX_LIST l) l ==>
         !h. h::l <> [] ==> MEM (MAX_LIST (h::l)) (h::l)
      If l = [],
         Note MAX_LIST [h] = h         by MAX_LIST_SING
          and MEM h [h]                by MEM
         Hence true.
      If l <> [],
         Let x = MAX_LIST (h::l)
               = MAX h (MAX_LIST l)    by MAX_LIST_CONS
         ==> x = h \/ x = MAX_LIST l   by MAX_CASES
         If x = h, MEM x (h::l)        by MEM
         If x = MAX_LIST l, MEM x l    by induction hypothesis
*)
val MAX_LIST_MEM = store_thm(
  "MAX_LIST_MEM",
  ``!l. l <> [] ==> MEM (MAX_LIST l) l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw[] >>
  metis_tac[MAX_CASES]);

(* Theorem: MEM x l ==> x <= MAX_LIST l *)
(* Proof:
   By induction on l.
   Base: !x. MEM x [] ==> x <= MAX_LIST []
     Trivially true since MEM x [] = F             by MEM
   Step: !x. MEM x l ==> x <= MAX_LIST l ==> !h x. MEM x (h::l) ==> x <= MAX_LIST (h::l)
     Note MEM x (h::l) means (x = h) \/ MEM x l    by MEM
      and MAX_LIST (h::l) = MAX h (MAX_LIST l)     by MAX_LIST_CONS
     If x = h, x <= MAX h (MAX_LIST l)             by MAX_LE
     If MEM x l, x <= MAX_LIST l                   by induction hypothesis
     or          x <= MAX h (MAX_LIST l)           by MAX_LE, LESS_EQ_TRANS
*)
val MAX_LIST_PROPERTY = store_thm(
  "MAX_LIST_PROPERTY",
  ``!l x. MEM x l ==> x <= MAX_LIST l``,
  Induct >-
  rw[] >>
  rw[MAX_LIST_CONS] >-
  decide_tac >>
  rw[]);

(* Theorem: l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l) *)
(* Proof:
   Let m = MAX_LIST l.
   Since MEM x l /\ x <= m     by MAX_LIST_PROPERTY
     and MEM m l ==> m <= x    by MAX_LIST_MEM, implication, l <> []
   Hence x = m                 by EQ_LESS_EQ
*)
val MAX_LIST_TEST = store_thm(
  "MAX_LIST_TEST",
  ``!l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l)``,
  metis_tac[MAX_LIST_MEM, MAX_LIST_PROPERTY, EQ_LESS_EQ]);

(* Theorem: MAX_LIST t <= MAX_LIST (h::t) *)
(* Proof:
   Note MAX_LIST (h::t) = MAX h (MAX_LIST t)   by MAX_LIST_def
    and MAX_LIST t <= MAX h (MAX_LIST t)       by MAX_IS_MAX
   Thus MAX_LIST t <= MAX_LIST (h::t)
*)
val MAX_LIST_LE = store_thm(
  "MAX_LIST_LE",
  ``!h t. MAX_LIST t <= MAX_LIST (h::t)``,
  rw_tac std_ss[MAX_LIST_def]);

(* Theorem: (!x. f x <= g x) ==> !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: MAX_LIST (MAP f []) <= MAX_LIST (MAP g [])
      LHS = MAX_LIST (MAP f []) = MAX_LIST []    by MAP
      RHS = MAX_LIST (MAP g []) = MAX_LIST []    by MAP
      Hence true.
   Step: MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls) ==>
         !h. MAX_LIST (MAP f (h::ls)) <= MAX_LIST (MAP g (h::ls))
        MAX_LIST (MAP f (h::ls))
      = MAX_LIST (f h::MAP f ls)                 by MAP
      = MAX (f h) (MAX_LIST (MAP f ls))          by MAX_LIST_def
     <= MAX (f h) (MAX_LIST (MAP g ls))          by induction hypothesis
     <= MAX (g h) (MAX_LIST (MAP g ls))          by properties of f, g
      = MAX_LIST (g h::MAP g ls)                 by MAX_LIST_def
      = MAX_LIST (MAP g (h::ls))                 by MAP
*)
val MAX_LIST_MAP_LE = store_thm(
  "MAX_LIST_MAP_LE",
  ``!f g. (!x. f x <= g x) ==> !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Minimum of a List                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define MIN of a list *)
val MIN_LIST_def = Define`
    MIN_LIST (h::t) = if t = [] then h else MIN h (MIN_LIST t)
`;

(* Theorem: MIN_LIST [x] = x *)
(* Proof: by MIN_LIST_def *)
val MIN_LIST_SING = store_thm(
  "MIN_LIST_SING",
  ``!x. MIN_LIST [x] = x``,
  rw[MIN_LIST_def]);

(* Theorem: t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t)) *)
(* Proof: by MIN_LIST_def *)
val MIN_LIST_CONS = store_thm(
  "MIN_LIST_CONS",
  ``!h t. t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t))``,
  rw[MIN_LIST_def]);

(* export simple results *)
val _ = export_rewrites["MIN_LIST_SING", "MIN_LIST_CONS"];

(* Theorem: l <> [] ==> MEM (MIN_LIST l) l *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> MEM (MIN_LIST []) []
      Trivially true by [] <> [] = F.
   Step: l <> [] ==> MEM (MIN_LIST l) l ==>
         !h. h::l <> [] ==> MEM (MIN_LIST (h::l)) (h::l)
      If l = [],
         Note MIN_LIST [h] = h         by MIN_LIST_SING
          and MEM h [h]                by MEM
         Hence true.
      If l <> [],
         Let x = MIN_LIST (h::l)
               = MIN h (MIN_LIST l)    by MIN_LIST_CONS
         ==> x = h \/ x = MIN_LIST l   by MIN_CASES
         If x = h, MEM x (h::l)        by MEM
         If x = MIN_LIST l, MEM x l    by induction hypothesis
*)
val MIN_LIST_MEM = store_thm(
  "MIN_LIST_MEM",
  ``!l. l <> [] ==> MEM (MIN_LIST l) l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw[] >>
  metis_tac[MIN_CASES]);

(* Theorem: l <> [] ==> !x. MEM x l ==> (MIN_LIST l) <= x *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> ...
     Trivially true since [] <> [] = F
   Step: l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x ==>
         !h. h::l <> [] ==> !x. MEM x (h::l) ==> MIN_LIST (h::l) <= x
     Note MEM x (h::l) means (x = h) \/ MEM x l    by MEM
     If l = [],
        MEM x [h] means x = h                      by MEM
        and MIN_LIST [h] = h, hence true           by MIN_LIST_SING
     If l <> [],
        MIN_LIST (h::l) = MIN h (MIN_LIST l)       by MIN_LIST_CONS
        If x = h, MIN h (MIN_LIST l) <= x          by MIN_LE
        If MEM x l, MIN_LIST l <= x                by induction hypothesis
        or          MIN h (MIN_LIST l) <= x        by MIN_LE, LESS_EQ_TRANS
*)
val MIN_LIST_PROPERTY = store_thm(
  "MIN_LIST_PROPERTY",
  ``!l. l <> [] ==> !x. MEM x l ==> (MIN_LIST l) <= x``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  fs[MIN_LIST_SING, MEM] >>
  fs[MIN_LIST_CONS, MEM]);

(* Theorem: l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l) *)
(* Proof:
   Let m = MIN_LIST l.
   Since MEM x l /\ m <= x     by MIN_LIST_PROPERTY
     and MEM m l ==> x <= m    by MIN_LIST_MEM, implication, l <> []
   Hence x = m                 by EQ_LESS_EQ
*)
val MIN_LIST_TEST = store_thm(
  "MIN_LIST_TEST",
  ``!l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l)``,
  metis_tac[MIN_LIST_MEM, MIN_LIST_PROPERTY, EQ_LESS_EQ]);

(* Theorem: l <> [] ==> MIN_LIST l <= MAX_LIST l *)
(* Proof:
   Since MEM (MIN_LIST l) l          by MIN_LIST_MEM
      so MIN_LIST l <= MAX_LIST l    by MAX_LIST_PROPERTY
*)
val MIN_LIST_LE_MAX_LIST = store_thm(
  "MIN_LIST_LE_MAX_LIST",
  ``!l. l <> [] ==> MIN_LIST l <= MAX_LIST l``,
  rw[MIN_LIST_MEM, MAX_LIST_PROPERTY]);

(* Theorem: t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t *)
(* Proof:
   Note MIN_LIST (h::t) = MIN h (MIN_LIST t)   by MIN_LIST_def, t <> []
    and MIN h (MIN_LIST t) <= MIN_LIST t       by MIN_IS_MIN
   Thus MIN_LIST (h::t) <= MIN_LIST t
*)
val MIN_LIST_LE = store_thm(
  "MIN_LIST_LE",
  ``!h t. t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t``,
  rw_tac std_ss[MIN_LIST_def]);

(* Theorem: a <= b /\ c <= d ==> MIN a c <= MIN b d *)
(* Proof: by MIN_DEF *)
val MIN_LE_PAIR = prove(
  ``!a b c d. a <= b /\ c <= d ==> MIN a c <= MIN b d``,
  rw[]);

(* Theorem: (!x. f x <= g x) ==> !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: MIN_LIST (MAP f []) <= MIN_LIST (MAP g [])
      LHS = MIN_LIST (MAP f []) = MIN_LIST []    by MAP
      RHS = MIN_LIST (MAP g []) = MIN_LIST []    by MAP
      Hence true.
   Step: MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls) ==>
         !h. MIN_LIST (MAP f (h::ls)) <= MIN_LIST (MAP g (h::ls))
      If ls = [],
        MIN_LIST (MAP f [h])
      = MIN_LIST [f h]                           by MAP
      = f h                                      by MIN_LIST_def
     <= g h                                      by properties of f, g
      = MIN_LIST [g h]                           by MIN_LIST_def
      = MIN_LIST (MAP g [h])                     by MAP
      Otherwise ls <> [],
        MIN_LIST (MAP f (h::ls))
      = MIN_LIST (f h::MAP f ls)                 by MAP
      = MIN (f h) (MIN_LIST (MAP f ls))          by MIN_LIST_def
     <= MIN (g h) (MIN_LIST (MAP g ls))          by MIN_LE_PAIR, induction hypothesis
      = MIN_LIST (g h::MAP g ls)                 by MIN_LIST_def
      = MIN_LIST (MAP g (h::ls))                 by MAP
*)
val MIN_LIST_MAP_LE = store_thm(
  "MIN_LIST_MAP_LE",
  ``!f g. (!x. f x <= g x) ==> !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[MIN_LIST_def] >>
  rw[MIN_LIST_def, MIN_LE_PAIR]);

(* ------------------------------------------------------------------------- *)
(* Increasing and decreasing list bounds                                     *)
(* ------------------------------------------------------------------------- *)

(* Overload increasing list and decreasing list *)
val _ = overload_on("MONO_INC",
          ``\ls:num list. !m n. m <= n /\ n < LENGTH ls ==> EL m ls <= EL n ls``);
val _ = overload_on("MONO_DEC",
          ``\ls:num list. !m n. m <= n /\ n < LENGTH ls ==> EL n ls <= EL m ls``);

(* Theorem: MONO_INC []*)
(* Proof: no member to falsify. *)
Theorem MONO_INC_NIL:
  MONO_INC []
Proof
  simp[]
QED

(* Theorem: MONO_INC (h::t) ==> MONO_INC t *)
(* Proof:
   This is to show: m <= n /\ n < LENGTH t ==> EL m t <= EL n t
   Note m <= n <=> SUC m <= SUC n              by arithmetic
    and n < LENGTH t <=> SUC n < LENGTH (h::t) by LENGTH
   Thus EL (SUC m) (h::t) <= EL (SUC n) (h::t) by MONO_INC (h::t)
     or            EL m t <= EL n t            by EL
*)
Theorem MONO_INC_CONS:
  !h t. MONO_INC (h::t) ==> MONO_INC t
Proof
  rw[] >>
  first_x_assum (qspecl_then [`SUC m`, `SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO_INC (h::t) /\ MEM x t ==> h <= x *)
(* Proof:
   Note MEM x t
    ==> ?n. n < LENGTH t /\ x = EL n t         by MEM_EL
     or SUC n < SUC (LENGTH t)                 by inequality
    Now 0 < SUC n, or 0 <= SUC n,
    and SUC n < SUC (LENGTH t) = LENGTH (h::t) by LENGTH
     so EL 0 (h::t) <= EL (SUC n) (h::t)       by MONO_INC (h::t)
     or           h <= EL n t = x              by EL
*)
Theorem MONO_INC_HD:
  !h t x. MONO_INC (h::t) /\ MEM x t ==> h <= x
Proof
  rpt strip_tac >>
  fs[MEM_EL] >>
  last_x_assum (qspecl_then [`0`,`SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO_DEC []*)
(* Proof: no member to falsify. *)
Theorem MONO_DEC_NIL:
  MONO_DEC []
Proof
  simp[]
QED

(* Theorem: MONO_DEC (h::t) ==> MONO_DEC t *)
(* Proof:
   This is to show: m <= n /\ n < LENGTH t ==> EL n t <= EL m t
   Note m <= n <=> SUC m <= SUC n              by arithmetic
    and n < LENGTH t <=> SUC n < LENGTH (h::t) by LENGTH
   Thus EL (SUC n) (h::t) <= EL (SUC m) (h::t) by MONO_DEC (h::t)
     or            EL n t <= EL m t            by EL
*)
Theorem MONO_DEC_CONS:
  !h t. MONO_DEC (h::t) ==> MONO_DEC t
Proof
  rw[] >>
  first_x_assum (qspecl_then [`SUC m`, `SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO_DEC (h::t) /\ MEM x t ==> x <= h *)
(* Proof:
   Note MEM x t
    ==> ?n. n < LENGTH t /\ x = EL n t         by MEM_EL
     or SUC n < SUC (LENGTH t)                 by inequality
    Now 0 < SUC n, or 0 <= SUC n,
    and SUC n < SUC (LENGTH t) = LENGTH (h::t) by LENGTH
     so EL (SUC n) (h::t) <= EL 0 (h::t)       by MONO_DEC (h::t)
     or        x = EL n t <= h                 by EL
*)
Theorem MONO_DEC_HD:
  !h t x. MONO_DEC (h::t) /\ MEM x t ==> x <= h
Proof
  rpt strip_tac >>
  fs[MEM_EL] >>
  last_x_assum (qspecl_then [`0`,`SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: ls <> [] /\ (!m n. m <= n ==> EL m ls <= EL n ls) ==> (MAX_LIST ls = LAST ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_INC [] ==> MAX_LIST [] = LAST []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_INC ls ==> MAX_LIST ls = LAST ls ==>
         !h. h::ls <> [] /\ MONO_INC (h::ls) ==> MAX_LIST (h::ls) = LAST (h::ls)
       If ls = [],
         LHS = MAX_LIST [h] = h        by MAX_LIST_def
         RHS = LAST [h] = h = LHS      by LAST_DEF
       If ls <> [],
         Note h <= LAST ls             by LAST_EL_CONS, increasing property
          and MONO_INC ls              by EL, m <= n ==> SUC m <= SUC n
         MAX_LIST (h::ls)
       = MAX h (MAX_LIST ls)           by MAX_LIST_def
       = MAX h (LAST ls)               by induction hypothesis
       = LAST ls                       by MAX_DEF, h <= LAST ls
       = LAST (h::ls)                  by LAST_DEF
*)
val MAX_LIST_MONO_INC = store_thm(
  "MAX_LIST_MONO_INC",
  ``!ls. ls <> [] /\ MONO_INC ls ==> (MAX_LIST ls = LAST ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `h <= LAST ls` by
  (`LAST ls = EL (LENGTH ls) (h::ls)` by rw[LAST_EL_CONS] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `LENGTH ls < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= n``]) >>
  `MONO_INC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC m) (h::ls) <= EL (SUC n) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MAX_DEF, LAST_DEF]);

(* Theorem: ls <> [] /\ MONO_DEC ls ==> (MAX_LIST ls = HD ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_DEC [] ==> MAX_LIST [] = HD []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_DEC ls ==> MAX_LIST ls = HD ls ==>
         !h. h::ls <> [] /\ MONO_DEC (h::ls) ==> MAX_LIST (h::ls) = HD (h::ls)
       If ls = [],
         LHS = MAX_LIST [h] = h        by MAX_LIST_def
         RHS = HD [h] = h = LHS        by HD
       If ls <> [],
         Note HD ls <= h               by HD, decreasing property
          and MONO_DEC ls              by EL, m <= n ==> SUC m <= SUC n
         MAX_LIST (h::ls)
       = MAX h (MAX_LIST ls)           by MAX_LIST_def
       = MAX h (HD ls)                 by induction hypothesis
       = h                             by MAX_DEF, HD ls <= h
       = HD (h::ls)                    by HD
*)
val MAX_LIST_MONO_DEC = store_thm(
  "MAX_LIST_MONO_DEC",
  ``!ls. ls <> [] /\ MONO_DEC ls ==> (MAX_LIST ls = HD ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `HD ls <= h` by
  (`HD ls = EL 1 (h::ls)` by rw[] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `1 < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= 1``]) >>
  `MONO_DEC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC n) (h::ls) <= EL (SUC m) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MAX_DEF]);

(* Theorem: ls <> [] /\ MONO_INC ls ==> (MIN_LIST ls = HD ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_INC [] ==> MIN_LIST [] = HD []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_INC ls ==> MIN_LIST ls = HD ls ==>
         !h. h::ls <> [] /\ MONO_INC (h::ls) ==> MIN_LIST (h::ls) = HD (h::ls)
       If ls = [],
         LHS = MIN_LIST [h] = h        by MIN_LIST_def
         RHS = HD [h] = h = LHS        by HD
       If ls <> [],
         Note h <= HD ls               by HD, increasing property
          and MONO_INC ls              by EL, m <= n ==> SUC m <= SUC n
         MIN_LIST (h::ls)
       = MIN h (MIN_LIST ls)           by MIN_LIST_def
       = MIN h (HD ls)                 by induction hypothesis
       = h                             by MIN_DEF, h <= HD ls
       = HD (h::ls)                    by HD
*)
val MIN_LIST_MONO_INC = store_thm(
  "MIN_LIST_MONO_INC",
  ``!ls. ls <> [] /\ MONO_INC ls ==> (MIN_LIST ls = HD ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `h <= HD ls` by
  (`HD ls = EL 1 (h::ls)` by rw[] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `1 < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= 1``]) >>
  `MONO_INC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC m) (h::ls) <= EL (SUC n) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MIN_DEF]);

(* Theorem: ls <> [] /\ MONO_DEC ls ==> (MIN_LIST ls = LAST ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_DEC [] ==> MIN_LIST [] = LAST []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_DEC ls ==> MIN_LIST ls = LAST ls ==>
         !h. h::ls <> [] /\ MONO_DEC (h::ls) ==> MAX_LIST (h::ls) = LAST (h::ls)
       If ls = [],
         LHS = MIN_LIST [h] = h        by MIN_LIST_def
         RHS = LAST [h] = h = LHS      by LAST_DEF
       If ls <> [],
         Note LAST ls <= h             by LAST_EL_CONS, decreasing property
          and MONO_DEC ls              by EL, m <= n ==> SUC m <= SUC n
         MIN_LIST (h::ls)
       = MIN h (MIN_LIST ls)           by MIN_LIST_def
       = MIN h (LAST ls)               by induction hypothesis
       = LAST ls                       by MIN_DEF, LAST ls <= h
       = LAST (h::ls)                  by LAST_DEF
*)
val MIN_LIST_MONO_DEC = store_thm(
  "MIN_LIST_MONO_DEC",
  ``!ls. ls <> [] /\ MONO_DEC ls ==> (MIN_LIST ls = LAST ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `LAST ls <= h` by
  (`LAST ls = EL (LENGTH ls) (h::ls)` by rw[LAST_EL_CONS] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `LENGTH ls < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= n``]) >>
  `MONO_DEC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC n) (h::ls) <= EL (SUC m) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MIN_DEF, LAST_DEF]);

(* ------------------------------------------------------------------------- *)
(* Sublist: an order-preserving portion of a list                            *)
(* ------------------------------------------------------------------------- *)

(* Definition of sublist *)
val sublist_def = Define`
    (sublist [] x = T) /\
    (sublist (h1::t1) [] = F) /\
    (sublist (h1::t1) (h2::t2) <=>
       ((h1 = h2) /\ sublist t1 t2 \/ ~(h1 = h2) /\ sublist (h1::t1) t2))
`;

(* Overload sublist by infix operator *)
val _ = temp_overload_on ("<=", ``sublist``);
(*
> sublist_def;
val it = |- (!x. [] <= x <=> T) /\ (!t1 h1. h1::t1 <= [] <=> F) /\
             !t2 t1 h2 h1. h1::t1 <= h2::t2 <=>
                (h1 = h2) /\ t1 <= t2 \/ h1 <> h2 /\ h1::t1 <= t2: thm
*)

(* Theorem: [] <= p *)
(* Proof: by sublist_def *)
val sublist_nil = store_thm(
  "sublist_nil",
  ``!p. [] <= p``,
  rw[sublist_def]);

(* Theorem: p <= q <=> h::p <= h::q *)
(* Proof: by sublist_def *)
val sublist_cons = store_thm(
  "sublist_cons",
  ``!h p q. p <= q <=> h::p <= h::q``,
  rw[sublist_def]);

(* Theorem: p <= [] <=> (p = []) *)
(* Proof:
   If p = [], then [] <= []           by sublist_nil
   If p = h::t, then h::t <= [] = F   by sublist_def
*)
val sublist_of_nil = store_thm(
  "sublist_of_nil",
  ``!p. p <= [] <=> (p = [])``,
  (Cases_on `p` >> rw[sublist_def]));

(* Theorem: (!p q. (h::p) <= q ==> p <= q) = (!p q. p <= q ==> p <= (h::q)) *)
(* Proof:
   If part: (!p q. (h::p) <= q ==> p <= q) ==> (!p q. p <= q ==> p <= (h::q))
               p <= q
        ==> h::p <= h::q     by sublist_cons
        ==>    p <= h::q     by implication
   Only-if part: (!p q. p <= q ==> p <= (h::q)) ==> (!p q. (h::p) <= q ==> p <= q)
            (h::p) <= q
        ==> (h::p) <= (h::q) by implication
        ==>      p <= q      by sublist_cons
*)
val sublist_cons_eq = store_thm(
  "sublist_cons_eq",
  ``!h. (!p q. (h::p) <= q ==> p <= q) = (!p q. p <= q ==> p <= (h::q))``,
  rw[EQ_IMP_THM] >>
  metis_tac[sublist_cons]);

(* Theorem: h::p <= q ==> p <= q *)
(* Proof:
   By induction on q.
   Base: !h p. h::p <= [] ==> p <= []
        True since h::p <= [] = F    by sublist_def

   Step: !h p. h::p <= q ==> p <= q ==>
         !h h' p. h'::p <= h::q ==> p <= h::q
        If p = [], true        by sublist_nil
        If p = h''::t,
            p <= h::q
        <=> (h'' = h) /\ t <= q \/ h'' <> h /\ h''::t <= q   by sublist_def
        If h'' = h, then t <= q        by sublist_def, induction hypothesis
        If h'' <> h, then h''::t <= q  by sublist_def, induction hypothesis
*)
val sublist_cons_remove = store_thm(
  "sublist_cons_remove",
  ``!h p q. h::p <= q ==> p <= q``,
  Induct_on `q` >-
  rw[sublist_def] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[sublist_def]) >>
  (Cases_on `h'' = h` >> metis_tac[sublist_def]));

(* Theorem: p <= q ==> p <= h::q *)
(* Proof: by sublist_cons_eq, sublist_cons_remove *)
val sublist_cons_include = store_thm(
  "sublist_cons_include",
  ``!h p q. p <= q ==> p <= h::q``,
  metis_tac[sublist_cons_eq, sublist_cons_remove]);

(* Theorem: p <= q ==> LENGTH p <= LENGTH q *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> LENGTH p <= LENGTH []
        Note p = []      by sublist_of_nil
        Thus true        by arithemtic
   Step: !p. p <= q ==> LENGTH p <= LENGTH q ==>
         !h p. p <= h::q ==> LENGTH p <= LENGTH (h::q)
         If p = [], LENGTH p = 0          by LENGTH
            and 0 <= LENGTH (h::q).
         If p = h'::t,
            If h = h',
               (h::t) <= (h::q)
            <=>    t <= q                 by sublist_def, same heads
            ==> LENGTH t <= LENGTH q      by inductive hypothesis
            ==> SUC(LENGTH t) <= SUC(LENGTH q)
              = LENGTH (h::t) <= LENGTH (h::q)
            If ~(h = h'),
                (h'::t) <= (h::q)
            <=> (h'::t) <= q                      by sublist_def, different heads
            ==> LENGTH (h'::t) <= LENGTH q        by inductive hypothesis
            ==> LENGTH (h'::t) <= SUC(LENGTH q)   by arithemtic
              = LENGTH (h'::t) <= LENGTH (h::q)
*)
val sublist_length = store_thm(
  "sublist_length",
  ``!p q. p <= q ==> LENGTH p <= LENGTH q``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[]) >>
  (Cases_on `h = h'` >> fs[sublist_def]) >>
  `LENGTH (h'::t) <= LENGTH q` by rw[] >>
  `LENGTH t < LENGTH (h'::t)` by rw[LENGTH_TL_LT] >>
  decide_tac);

(* Theorem: [Reflexive] p <= p *)
(* Proof:
   By induction on p.
   Base: [] <= [], true                      by sublist_nil
   Step: p <= p ==> !h. h::p <= h::p, true   by sublist_cons
*)
val sublist_refl = store_thm(
  "sublist_refl",
  ``!p:'a list. p <= p``,
  Induct >> rw[sublist_def]);

(* Theorem: [Anti-symmetric] !p q. (p <= q) /\ (q <= p) ==> (p = q) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] /\ [] <= p ==> (p = [])
       Note p <= [] already gives p = []   by sublist_of_nil
   Step: !p. p <= q /\ q <= p ==> (p = q) ==>
         !h p. p <= h::q /\ h::q <= p ==> (p = h::q)
       If p = [], h::q <= [] = F           by sublist_def
       If p = (h'::t),
          If h = h',
              ((h::t) <= (h::q)) /\ ((h::q) <= (h::t))
          <=> (t <= q) and (q <= t)        by sublist_def, same heads
          ==> t = q                        by inductive hypothesis
          <=> (h::t) = (h::q)              by list equality
          If ~(h = h'),
              ((h'::t) <= (h::q)) /\ ((h::q) <= (h'::t))
          <=> ((h'::t) <= q) /\ ((h::q) <= t)      by sublist_def, different heads
          ==> (LENGTH (h'::t) <= LENGTH q) /\
              (LENGTH (h::q) <= LENGTH t)          by sublist_length
          ==> (LENGTh t < LENGTH q) /\
              (LENGTH q < LENGTH t)                by LENGTH_TL_LT
            = F                                    by arithmetic
          Hence the implication is T.
*)
val sublist_antisym = store_thm(
  "sublist_antisym",
  ``!p q:'a list. p <= q /\ q <= p ==> (p = q)``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  Cases_on `p` >-
  fs[sublist_def] >>
  (Cases_on `h' = h` >> fs[sublist_def]) >>
  `LENGTH (h'::t) <= LENGTH q /\ LENGTH (h::q) <= LENGTH t` by rw[sublist_length] >>
  fs[LENGTH_TL_LT]);

(* Theorem [Transitive]: for all lists p, q, r; (p <= q) /\ (q <= r) ==> (p <= r) *)
(* Proof:
   By induction on list r and taking note of cases.
   By induction on r.
   Base: !p q. p <= q /\ q <= [] ==> p <= []
      Note q = []         by sublist_of_nil
        so p = []         by sublist_of_nil
   Step: !p q. p <= q /\ q <= r ==> p <= r ==>
         !h p q. p <= q /\ q <= h::r ==> p <= h::r
      If p = [], true     by sublist_nil
      If p = h'::t, to show:
         h'::t <= q /\ q <= h::r ==>
         (h' = h) /\ t <= r \/
         h' <> h /\ h'::t <= r    by sublist_def
      If q = [], [] <= h::r = F   by sublist_def
      If q = h''::t', this reduces to:
      (1) h' = h'' /\ t <= t' /\ h'' = h /\ t' <= r ==> t <= r
          Note t <= t' /\ t' <= r ==> t <= r     by induction hypothesis
      (2) h' = h'' /\ t <= t' /\ h'' <> h /\ h''::t' <= r ==> h''::t <= r
          Note t <= t' ==> h''::t <= h''::t'     by sublist_cons
          With h''::t' <= r ==> h''::t <= r      by induction hypothesis
      (3) h' <> h'' /\ h'::t <= t' /\ h'' = h /\ t' <= r ==>
          (h' = h) /\ t <= r \/ h' <> h /\ h'::t <= r
          Note h'::t <= t' ==> t <= t'           by sublist_cons_remove
          With t' <= r ==> t <= r                by induction hypothesis
          Or simply h'::t <= t' /\ t' <= r
                    ==> h'::t <= r               by induction hypothesis
          Hence this is true.
      (4) h' <> h'' /\ h'::t <= t' /\ h'' <> h /\ h''::t' <= r ==>
          (h' = h) /\ t <= r \/ h' <> h /\ h'::t <= r
          Same reasoning as (3).
*)
val sublist_trans = store_thm(
  "sublist_trans",
  ``!p q r:'a list. p <= q /\ q <= r ==> p <= r``,
  Induct_on `r` >-
  fs[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >>
  (Cases_on `q` >> fs[sublist_def]) >-
  metis_tac[] >-
  metis_tac[sublist_cons] >-
  metis_tac[sublist_cons_remove] >>
  metis_tac[sublist_cons_remove]);

(* The above theorems show that sublist is a partial ordering. *)

(* Theorem: p <= q ==> SNOC h p <= SNOC h q *)
(* Proof:
   By induction on q.
   Base: !h p. p <= [] ==> SNOC h p <= SNOC h []
       Note p = []                    by sublist_of_nil
       Thus SNOC h [] <= SNOC h []    by sublist_refl
   Step: !h p. p <= q ==> SNOC h p <= SNOC h q ==>
         !h h' p. p <= h::q ==> SNOC h' p <= SNOC h' (h::q)
       If p = [],
          Note [] <= q                by sublist_nil
          Thus SNOC h' []
            <= SNOC h' q              by induction hypothesis
            <= h::SNOC h' q           by sublist_cons_include
             = SNOC h' (h::q)         by SNOC
       If p = h''::t,
          If h = h'',
          Then t <= q                 by sublist_def, same heads
           ==>      SNOC h' t <= SNOC h' q        by induction hypothesis
           ==>   h::SNOC h' t <= h::SNOC h' q     by rw[sublist_cons
            or SNOC h' (h::t) <= SNOC h' (h::q)   by SNOC
            or      SNOC h' p <= SNOC h' (h::q)   by p = h::t
          If h <> h'',
          Then         p <= q              by sublist_def, different heads
           ==> SNOC h' p <= SNOC h' q      by induction hypothesis
           ==> SNOC h' p <= h::SNOC h' q   by sublist_cons_include
*)
val sublist_snoc = store_thm(
  "sublist_snoc",
  ``!h p q. p <= q ==> SNOC h p <= SNOC h q``,
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_refl] >>
  rw[sublist_def] >>
  Cases_on `p` >-
  rw[sublist_nil, sublist_cons_include] >>
  metis_tac[sublist_def, sublist_cons, SNOC]);

(* Theorem: MEM x ls ==> [x] <= ls *)
(* Proof:
   By induction on ls.
   Base: !x. MEM x [] ==> [x] <= []
      True since MEM x [] = F.
   Step: !x. MEM x ls ==> [x] <= ls ==>
         !h x. MEM x (h::ls) ==> [x] <= h::ls
      If x = h,
         Then [h] <= h::ls     by sublist_nil, sublist_cons
      If x <> h,
         Then MEM h ls         by MEM x (h::ls)
          ==> [x] <= ls        by induction hypothesis
          ==> [x] <= h::ls     by sublist_cons_include
*)
val sublist_member_sing = store_thm(
  "sublist_member_sing",
  ``!ls x. MEM x ls ==> [x] <= ls``,
  Induct >-
  rw[] >>
  rw[] >-
  rw[sublist_nil, GSYM sublist_cons] >>
  rw[sublist_cons_include]);

(* Theorem: TAKE n ls <= ls *)
(* Proof:
   By induction on ls.
   Base: !n. TAKE n [] <= []
      LHS = TAKE n [] = []   by TAKE_def
          <= [] = RHS        by sublist_nil
   Step: !n. TAKE n ls <= ls ==> !h n. TAKE n (h::ls) <= h::ls
      If n = 0,
         TAKE 0 (h::ls)
       = []                  by TAKE_def
      <= h::ls               by sublist_nil
      If n <> 0,
         TAKE n (h::ls)
       = h::TAKE (n - 1) ls             by TAKE_def
       Now    TAKE (n - 1) ls <= ls     by induction hypothesis
      Thus h::TAKE (n - 1) ls <= h::ls  by sublist_cons
*)
val sublist_take = store_thm(
  "sublist_take",
  ``!ls n. TAKE n ls <= ls``,
  Induct >-
  rw[sublist_nil] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[sublist_nil] >>
  rw[GSYM sublist_cons]);

(* Theorem: DROP n ls <= ls *)
(* Proof:
   By induction on ls.
   Base: !n. DROP n [] <= []
      LHS = DROP n [] = []   by DROP_def
          <= [] = RHS        by sublist_nil
   Step: !n. DROP n ls <= ls ==> !h n. DROP n (h::ls) <= h::ls
      If n = 0,
         DROP 0 (h::ls)
       = h::ls               by DROP_def
      <= h::ls               by sublist_refl
      If n <> 0,
         DROP n (h::ls)
       = DROP n ls           by DROP_def
      <= ls                  by induction hypothesis
      <= h::ls               by sublist_cons_include
*)
val sublist_drop = store_thm(
  "sublist_drop",
  ``!ls n. DROP n ls <= ls``,
  Induct >-
  rw[sublist_nil] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[sublist_refl] >>
  rw[sublist_cons_include]);

(* Theorem: ls <> [] ==> TL ls <= ls *)
(* Proof:
   Note TL ls = DROP 1 ls    by TAIL_BY_DROP, ls <> []
   Thus TL ls <= ls          by sublist_drop
*)
val sublist_tail = store_thm(
  "sublist_tail",
  ``!ls. ls <> [] ==> TL ls <= ls``,
  rw[TAIL_BY_DROP, sublist_drop]);

(* Theorem: ls <> [] ==> FRONT ls <= ls *)
(* Proof:
   Note FRONT ls = TAKE (LENGTH ls - 1) ls   by FRONT_BY_TAKE
     so FRONT ls <= ls                       by sublist_take
*)
val sublist_front = store_thm(
  "sublist_front",
  ``!ls. ls <> [] ==> FRONT ls <= ls``,
  rw[FRONT_BY_TAKE, sublist_take]);

(* Theorem: ls <> [] ==> [HD ls] <= ls *)
(* Proof: HEAD_MEM, sublist_member_sing *)
val sublist_head_sing = store_thm(
  "sublist_head_sing",
  ``!ls. ls <> [] ==> [HD ls] <= ls``,
  rw[HEAD_MEM, sublist_member_sing]);

(* Theorem: ls <> [] ==> [LAST ls] <= ls *)
(* Proof: LAST_MEM, sublist_member_sing *)
val sublist_last_sing = store_thm(
  "sublist_last_sing",
  ``!ls. ls <> [] ==> [LAST ls] <= ls``,
  rw[LAST_MEM, sublist_member_sing]);

(* Theorem: l <= ls ==> !P. EVERY P ls ==> EVERY P l *)
(* Proof:
   By induction on ls.
   Base: !l. l <= [] ==> !P. EVERY P [] ==> EVERY P l
        Note l <= [] ==> l = []        by sublist_of_nil
         and EVERY P [] = T            by implication, or EVERY_DEF
   Step:  !l. l <= ls ==> !P. EVERY P ls ==> EVERY P l ==>
          !h l. l <= h::ls ==> !P. EVERY P (h::ls) ==> EVERY P l
         l <= h::ls
        If l = [], then EVERY P [] = T    by EVERY_DEF
        Otherwise, let l = k::t           by list_CASES
        Note EVERY P (h::ls)
         ==> P h /\ EVERY P ls            by EVERY_DEF
        Then k::t <= h::ls
         ==> k = h /\ t <= ls
          or k <> h /\ k::t <= ls         by sublist_def
        For the first case, h = k,
            P k /\ EVERY P t              by induction hypothesis
        ==> EVERY P (k::t) = EVERY P l    by EVERY_DEF
        For the second case, h <> k,
            EVERY P (k::t) = EVERY P l    by induction hypothesis
*)
val sublist_every = store_thm(
  "sublist_every",
  ``!l ls. l <= ls ==> !P. EVERY P ls ==> EVERY P l``,
  Induct_on `ls` >-
  rw[sublist_of_nil] >>
  (Cases_on `l` >> simp[]) >>
  metis_tac[sublist_def, EVERY_DEF]);

(* ------------------------------------------------------------------------- *)
(* More sublists, applying partial order properties                          *)
(* ------------------------------------------------------------------------- *)

(* Observation:
When doing induction proofs on sublists about p <= q,
Always induct on q, then take cases on p.
*)

(* The following induction theorem is already present during definition:
> theorem "sublist_ind";
val it = |- !P. (!x. P [] x) /\ (!h1 t1. P (h1::t1) []) /\
                (!h1 t1 h2 t2. P t1 t2 /\ P (h1::t1) t2 ==> P (h1::t1) (h2::t2)) ==>
            !v v1. P v v1: thm

Just prove it as an exercise.
*)

(* Theorem: [Induction] For any property P satisfying,
   (a) !y. P [] y = T
   (b) !h x y. P x y /\ sublist x y ==> P (h::x) (h::y)
   (c) !h x y. P x y /\ sublist x y ==> P x (h::y)
   then  !x y. sublist x y ==> P x y.
*)
(* Proof:
   By induction on y.
   Base: !x. x <= [] ==> P x []
      Note x = []            by sublist_of_nil
       and P [] [] = T       by given
   Step: !x. x <= y ==> P x y ==>
         !h x. x <= h::y ==> P x (h::y)
      If x = [], then [] <= h::y = F      by sublist_def
      If x = h'::t,
         If h' = h, t <= y                by sublist_def, same heads
            Thus P t y                    by induction hypothesis
             and P t y /\ t <= y ==> P (h::t) (h::y) = P x (h::y)
         If h' <> h, x <= y               by sublist_def, different heads
            Thus P x y                    by induction hypothesis
             and P x y /\ x <= y ==> P x (h::y).
*)
val sublist_induct = store_thm(
  "sublist_induct",
  ``!P. (!y. P [] y) /\
       (!h x y. P x y /\ x <= y ==> P (h::x) (h::y)) /\
       (!h x y. P x y /\ x <= y ==> P x (h::y)) ==>
        !x y. x <= y ==> P x y``,
  ntac 2 strip_tac >>
  Induct_on `y` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `x` >> fs[sublist_def]));

(*
Note that from definition:
sublist_ind
|- !P. (!x. P [] x) /\ (!h1 t1. P (h1::t1) []) /\
             (!h1 t1 h2 t2. P t1 t2 /\ P (h1::t1) t2 ==> P (h1::t1) (h2::t2)) ==>
             !v v1. P v v1

sublist_induct
|- !P. (!y. P [] y) /\ (!h x y. P x y /\ x <= y ==> P (h::x) (h::y)) /\
             (!h x y. P x y /\ x <= y ==> P x (h::y)) ==>
             !x y. x <= y ==> P x y

The second is better.
*)

(* Theorem: p <= q /\ MEM x p ==> MEM x q *)
(* Proof:
   By sublist_induct, this is to show:
   (1) MEM x [] ==> MEM x q
       Note MEM x [] = F                       by MEM
       Hence true.
   (2) MEM x p ==> MEM x q /\ p <= q /\ MEM x (h::p) ==> MEM x (h::q)
       If x = h, then MEM h (h::q) = T         by MEM
       If x <> h,     MEM x (h::p)
                  ==> MEM x p                  by MEM, x <> h
                  ==> MEM x q                  by induction hypothesis
                  ==> MEM x (h::q)             by MEM, x <> h
   (3) MEM x p ==> MEM x q /\ p <= q /\ MEM x p ==> MEM x (h::q)
       If x = h, then MEM h (h::q) = T         by MEM
       If x <> h,     MEM x p
                  ==> MEM x q                  by induction hypothesis
                  ==> MEM x (h::q)             by MEM, x <> h
*)
Theorem sublist_mem:
  !p q x. p <= q /\ MEM x p ==> MEM x q
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  qid_spec_tac `q` >>
  qid_spec_tac `p` >>
  ho_match_mp_tac sublist_induct >>
  rpt strip_tac >-
  fs[] >-
  (Cases_on `x = h` >> fs[]) >>
  (Cases_on `x = h` >> fs[])
QED

(* Theorem: sl <= ls ==> set sl SUBSET set ls *)
(* Proof:
       set sl SUBSET set ls
   <=> !x. x IN set (sl) ==> x IN set ls       by SUBSET_DEF
   <=> !x.      MEM x sl ==> MEM x ls          by notation
   ==> T                                       by sublist_mem
*)
Theorem sublist_subset:
  !ls sl. sl <= ls ==> set sl SUBSET set ls
Proof
  metis_tac[SUBSET_DEF, sublist_mem]
QED

(* Theorem: p <= q /\ ALL_DISTINCT q ==> ALL_DISTINCT p *)
(* Proof:
   By sublist_induct, this is to show:
   (1) ALL_DISTINCT q ==> ALL_DISTINCT []
       Note ALL_DISTINCT [] = T                by ALL_DISTINCT
   (2) ALL_DISTINCT q ==> ALL_DISTINCT p /\ p <= q /\ ALL_DISTINCT (h::q) ==> ALL_DISTINCT (h::p)
           ALL_DISTINCT (h::q)
       <=> ~MEM h q /\ ALL_DISTINCT q          by ALL_DISTINCT
       ==> ~MEM h q /\ ALL_DISTINCT p          by induction hypothesis
       ==> ~MEM h p /\ ALL_DISTINCT p          by sublist_mem
       <=> ALL_DISTINCT (h::p)                 by ALL_DISTINCT
   (3) ALL_DISTINCT q ==> ALL_DISTINCT p /\ p <= q /\ ALL_DISTINCT (h::q) ==> ALL_DISTINCT p
           ALL_DISTINCT (h::q)
       ==> ALL_DISTINCT q                      by ALL_DISTINCT
       ==> ALL_DISTINCT p                      by induction hypothesis
*)
Theorem sublist_ALL_DISTINCT:
  !p q. p <= q /\ ALL_DISTINCT q ==> ALL_DISTINCT p
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  qid_spec_tac `q` >>
  qid_spec_tac `p` >>
  ho_match_mp_tac sublist_induct >>
  rpt strip_tac >-
  simp[] >-
  (fs[] >> metis_tac[sublist_mem]) >>
  fs[]
QED

(* Theorem: [Eliminate append from left]: (x ++ p) <= q ==> sublist p <= q *)
(* Proof:
   By induction on the extra list x.
   The induction step follows from sublist_cons_remove.

   By induction on x.
   Base: !p q. [] ++ p <= q ==> p <= q
       True since [] ++ p = p     by APPEND
   Step: !p q. x ++ p <= q ==> p <= q ==>
         !h p q. h::x ++ p <= q ==> p <= q
            h::x ++ p <= q
        = h::(x ++ p) <= q        by APPEND
       ==>   (x ++ p) <= q        by sublist_cons_remove
       ==>          p <= q        by induction hypothesis
*)
val sublist_append_remove = store_thm(
  "sublist_append_remove",
  ``!p q x. x ++ p <= q ==> p <= q``,
  Induct_on `x` >> metis_tac[sublist_cons_remove, APPEND]);

(* Theorem: [Include append to right] p <= q ==> p <= (x ++ q) *)
(* Proof:
   By induction on list x.
   The induction step follows by sublist_cons_include.

   By induction on x.
   Base: !p q. p <= q ==> p <= [] ++ q
       True since [] ++ q = q     by APPEND
   Step: !p q. p <= q ==> p <= x ++ q ==>
         !h p q. p <= q ==> p <= h::x ++ q
             p <= q
       ==>   p <= x ++ q          by induction hypothesis
       ==>   p <= h::(x ++ q)     by sublist_cons_include
         =   p <= h::x ++ q       by APPEND
*)
val sublist_append_include = store_thm(
  "sublist_append_include",
  ``!p q x. p <= q ==> p <= x ++ q``,
  Induct_on `x` >> metis_tac[sublist_cons_include, APPEND]);

(* Theorem: [append after] p <= (p ++ q) *)
(* Proof:
   By induction on list p, and note that p and (p ++ q) have the same head.
   Base: !q. [] <= [] ++ q, true    by sublist_nil
   Step: !q. p <= p ++ q ==> !h q. h::p <= h::p ++ q
               p <= p ++ q          by induction hypothesis
        ==> h::p <= h::(p ++ q)     by sublist_cons
        ==> h::p <= h::p ++ q       by APPEND
*)
val sublist_append_suffix = store_thm(
  "sublist_append_suffix",
  ``!p q. p <= p ++ q``,
  Induct_on `p` >> rw[sublist_def]);

(* Theorem: [append before] p <= (q ++ p) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ++ p
      Note [] ++ p = p       by APPEND
       and p <= p            by sublist_refl
   Step: !p. p <= q ++ p ==> !h p. p <= h::q ++ p
           p <= q ++ p       by induction hypothesis
       ==> p <= h::(q ++ p)  by sublist_cons_include
        =  p <= h::q ++ p    by APPEND
*)
val sublist_append_prefix = store_thm(
  "sublist_append_prefix",
  ``!p q. p <= q ++ p``,
  Induct_on `q` >-
  rw[sublist_refl] >>
  rw[sublist_cons_include]);

(* Theorem: [prefix append] p <= q <=> (x ++ p) <= (x ++ q) *)
(* Proof:
   By induction on x.
   Base: !p q. p <= q <=> [] ++ p <= [] ++ q
      Since [] ++ p = p /\ [] ++ q = q           by APPEND
      This is trivially true.
   Step: !p q. p <= q <=> x ++ p <= x ++ q ==>
         !h p q. p <= q <=> h::x ++ p <= h::x ++ q
         p <= q <=>      x ++ p <= x ++ q        by induction hypothesis
                <=> h::(x ++ p) <= h::(x ++ q)   by sublist_cons
                <=>   h::x ++ p <= h::x ++ q     by APPEND
*)
val sublist_prefix = store_thm(
  "sublist_prefix",
  ``!x p q. p <= q <=> (x ++ p) <= (x ++ q)``,
  Induct_on `x` >> metis_tac[sublist_cons, APPEND]);

(* Theorem: [no append to left] !p q. (p ++ q) <= q ==> p = [] *)
(* Proof:
   By induction on q.
   Base: !p. p ++ [] <= [] ==> (p = [])
      Note p ++ [] = p         by APPEND
       and p <= [] ==> p = []  by sublist_of_nil
   Step: !p. p ++ q <= q ==> (p = []) ==>
         !h p. p ++ h::q <= h::q ==> (p = [])
      If p = [], true trivially.
      If p = h'::t,
          (h'::t) ++ (h::q) <= h::q
         =  h'::(t ++ h::q) <= h::q       by APPEND
         If h' = h,
            Then       t ++ h::q <= q     by sublist_def, same heads
              or (t ++ [h]) ++ q <= q     by APPEND
             ==>     t ++ [h] = []        by induction hypothesis
            which is F, hence h' <> h.
         If h' <> h,
            Then       p ++ h::q <= q     by sublist_def, different heads
              or (p ++ [h]) ++ q <= q     by APPEND
             ==> (p ++ [h]) = []          by induction hypothesis
             which is F, hence neither h' <> h.
         All these shows that p = h'::t is impossible.
*)
val sublist_prefix_nil = store_thm(
  "sublist_prefix_nil",
  ``!p q. (p ++ q) <= q ==> (p = [])``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >| [
    `t ++ h::q = (t ++ [h])++ q` by rw[] >>
    `t ++ [h] <> []` by rw[] >>
    metis_tac[],
    `(t ++ h::q) <= q` by metis_tac[sublist_cons_remove] >>
    `t ++ h::q = (t ++ [h])++ q` by rw[] >>
    `t ++ [h] <> []` by rw[] >>
    metis_tac[]
  ]);

(* Theorem: [tail append - if] p <= q ==> (p ++ [h]) <= (q ++ [h]) *)
(* Proof:
                p <= q
   ==>   SNOC h p <= SNOC h q      by sublist_snoc
   ==> (p ++ [h]) <= (q ++ [h])    by SNOC_APPEND
*)
Theorem sublist_append_if:
  !p q h. p <= q ==> (p ++ [h]) <= (q ++ [h])
Proof
  rw[sublist_snoc, GSYM SNOC_APPEND]
QED

(* Theorem: [tail append - only if] p ++ [h] <= q ++ [h] ==> p <= q *)
(* Proof:
   By induction on q.
   Base: !p h. p ++ [h] <= [] ++ [h] ==> p <= []
       Note [] ++ [h] = [h]                  by APPEND
        and p ++ [h] <= [h] ==> p = []       by sublist_prefix_nil
        and [] <= []                         by sublist_nil
   Step: !p h. p ++ [h] <= q ++ [h] ==> p <= q ==>
         !h p h'. p ++ [h'] <= h::q ++ [h'] ==> p <= h::q
       If p = [], [h'] <= h::q ++ [h'] = F    by sublist_def
       If p = h''::t,
          h''::t ++ [h'] = h''::(t ++ [h'])   by APPEND
          If h'' = h',
             Then t ++ [h'] <= q ++ [h']      by sublist_def, same heads
              ==>         t <= q              by induction hypothesis
          If h'' <> h',
             Then h''::t ++ [h'] <= q ++ [h'] by sublist_def, different heads
              ==>         h''::t <= q         by induction hypothesis
*)
val sublist_append_only_if = store_thm(
  "sublist_append_only_if",
  ``!p q h. (p ++ [h]) <= (q ++ [h]) ==> p <= q``,
  Induct_on `q` >-
  metis_tac[sublist_prefix_nil, sublist_nil, APPEND] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >-
  metis_tac[] >>
  `h''::(t ++ [h']) = (h''::t) ++ [h']` by rw[] >>
  metis_tac[]);

(* Theorem: [tail append] p <= q <=> p ++ [h] <= q ++ [h] *)
(* Proof: by sublist_append_if, sublist_append_only_if *)
val sublist_append_iff = store_thm(
  "sublist_append_iff",
  ``!p q h. p <= q <=> (p ++ [h]) <= (q ++ [h])``,
  metis_tac[sublist_append_if, sublist_append_only_if]);

(* Theorem: [suffix append] sublist p q ==> sublist (p ++ x) (q ++ x) *)
(* Proof:
   By induction on x.
   Base: !p q. p <= q <=> p ++ [] <= q ++ []
      True by p ++ [] = p, q ++ [] = q           by APPEND
   Step: !p q. p <= q <=> p ++ x <= q ++ x ==>
         !h p q. p <= q <=> p ++ h::x <= q ++ h::x
                         p <= q
       <=>      (p ++ [h]) <= (q ++ [h])         by sublist_append_iff
       <=> (p ++ [h]) ++ x <= (q ++ [h]) ++ x    by induction hypothesis
       <=>     p ++ (h::x) <= q ++ (h::x)        by APPEND
*)
val sublist_suffix = store_thm(
  "sublist_suffix",
  ``!x p q. p <= q <=> (p ++ x) <= (q ++ x)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `!z. z ++ h::x = (z ++ [h]) ++ x` by rw[] >>
  metis_tac[sublist_append_iff]);

(* Theorem : (a <= b) /\ (c <= d) ==> (a ++ c) <= (b ++ d) *)
(* Proof:
   Note a ++ c <= a ++ d    by sublist_prefix
    and a ++ d <= b ++ d    by sublist_suffix
    ==> a ++ c <= b ++ d    by sublist_trans
*)
val sublist_append_pair = store_thm(
  "sublist_append_pair",
  ``!a b c d. (a <= b) /\ (c <= d) ==> (a ++ c) <= (b ++ d)``,
  metis_tac[sublist_prefix, sublist_suffix, sublist_trans]);

(* Theorem: [Extended Append, or Decomposition] (h::t) <= q <=> ?x y. (q = x ++ (h::y)) /\ (t <= y) *)
(* Proof:
   By induction on list q.
   Base case is to prove:
     sublist (h::t) []  <=> ?x y. ([] = x ++ (h::y)) /\ (sublist t y)
     Hypothesis sublist (h::t) [] is F by SUBLIST_NIL.
     In the conclusion, [] cannot be decomposed, hence implication is valid.
   Step case is to prove:
     (sublist (h::t) q  <=> ?x y. (q = x ++ (h::y)) /\ (sublist t y)) ==>
     (sublist (h::t) (h'::q)  <=> ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y))
     Applying SUBLIST definition and split the if-and-only-if parts, there are 4 cases:
     When h = h', if part:
       sublist (h::t) (h::q) ==> ?x y. (h::q = x ++ (h::y)) /\ (sublist t y)
       For this case, choose x=[], y=q, and sublist (h::t) (h::q) = sublist t q, by SUBLIST same head.
     When h = h', only-if part:
       ?x y. (h::q = x ++ (h::y)) /\ (sublist t y) ==> sublist (h::t) (h::q)
       Take cases on x.
       When x = [],
         h::q = h::y ==> q = y,
         hence sublist t y = sublist t q ==> sublist (h::t) (h::q) by SUBLIST same head.
       When x = h''::t',
         h::q = (h''::t') ++ (h::y) = h''::(t' ++ (h::y)) ==>
         q = t' ++ (h::y),
         hence sublist t y ==> sublist t q (by SUBLIST_APPENDR_I) ==> sublist (h::t) (h::q).
     When ~(h=h'), if part:
       sublist (h::t) (h'::q) ==> ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y)
       From hypothesis,
             sublist (h::t) (h'::q)
           = sublist (h::t) q           when ~(h=h'), by SUBLIST definition
         ==> ?x1 y1. (q = x1 ++ (h::y1)) /\ (sublist t y1))  by inductive hypothesis
         Now (h'::q) = (h'::(x1 ++ (h::y1)) = (h'::x1) ++ (h::y1) by APPEND associativity
         So taking x = h'::x1, y = y1, this gives the conclusion.
     When ~(h=h'), only-if part:
       ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y) ==> sublist (h::t) (h'::q)
       The case x = [] is impossible by list equality, since ~(h=h').
       Hence x = h'::t', giving:
            q = t'++(h::y) /\ (sublist t y)
          = sublist (h::t) q              by inductive hypothesis (only-if)
        ==> sublist (h::t) (h'::q)        by SUBLIST, different head.
*)
val sublist_append_extend = store_thm(
  "sublist_append_extend",
  ``!h t q. h::t <= q  <=> ?x y. (q = x ++ (h::y)) /\ (t <= y)``,
  ntac 2 strip_tac >>
  Induct >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `h = h'` >> rw[EQ_IMP_THM]) >| [
    `h::q = [] ++ [h] ++ q` by rw[] >>
    metis_tac[sublist_cons],
    `h::t <= h::y` by rw[GSYM sublist_cons] >>
    `x ++ [h] ++ y = x ++ (h::y)` by rw[] >>
    metis_tac[sublist_append_include],
    `h::t <= q` by metis_tac[sublist_def] >>
    metis_tac[APPEND, APPEND_ASSOC],
    `h::t <= h::y` by rw[GSYM sublist_cons] >>
    `x ++ [h] ++ y = x ++ (h::y)` by rw[] >>
    metis_tac[sublist_append_include]
  ]);

(* ------------------------------------------------------------------------- *)
(* Applications of sublist.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p <= q ==> (MAP f p) <= (MAP f q) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> MAP f p <= MAP f []
         Note p = []       by sublist_of_nil
          and MAP f []     by MAP
           so [] <= []     by sublist_nil
   Step: !p. p <= q ==> MAP f p <= MAP f q ==>
         !h p. p <= h::q ==> MAP f p <= MAP f (h::q)
         If p = [], [] <= h::q = F          by sublist_def
         If p = h'::t,
            If h' = h,
               Then             t <= q             by sublist_def, same heads
                ==>       MAP f t <= MAP f q       by induction hypothesis
                ==>    h::MAP f t <= h::MAP f q    by sublist_cons
                ==>  MAP f (h::t) <= MAP f (h::q)  by MAP
                 or       MAP f p <= MAP f (h::q)  by p = h::t
            If h' <> h,
               Then          p <= q                by sublist_def, different heads
               ==>     MAP f p <= MAP f q          by induction hypothesis
               ==>     MAP f p <= h::MAP f q       by sublist_cons_include
                or     MAP f p <= MAP f (h::q)     by MAP
*)
val MAP_SUBLIST = store_thm(
  "MAP_SUBLIST",
  ``!f p q. p <= q ==> (MAP f p) <= (MAP f q)``,
  strip_tac >>
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[sublist_def]) >>
  metis_tac[sublist_def, sublist_cons_include, MAP]);

(* Theorem: l1 <= l2 ==> SUM l1 <= SUM l2 *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> SUM p <= SUM []
      Note p = []        by sublist_of_nil
       and SUM [] = 0    by SUM
      Hence true.
   Step: !p. p <= q ==> SUM p <= SUM q ==>
         !h p. p <= h::q ==> SUM p <= SUM (h::q)
      If p = [], [] <= h::q = F         by sublist_def
      If p = h'::t,
         If h' = h,
         Then          t <= q           by sublist_def, same heads
          ==>      SUM t <= SUM q       by induction hypothesis
          ==>  h + SUM t <= h + SUM q   by arithmetic
          ==> SUM (h::t) <= SUM (h::q)  by SUM
           or      SUM p <= SUM (h::q)  by p = h::t
         If h' <> h,
         Then          p <= q           by sublist_def, different heads
          ==>      SUM p <= SUM q       by induction hypothesis
          ==>      SUM p <= h + SUM q   by arithmetic
          ==>      SUM p <= SUM (h::q)  by SUM
*)
val SUM_SUBLIST = store_thm(
  "SUM_SUBLIST",
  ``!p q. p <= q ==> SUM p <= SUM q``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >>
  `h' + SUM t <= SUM q` by metis_tac[SUM] >>
  decide_tac);

(* Idea: express order-preserving in sublist *)

(* Note:
A simple statement of order-preserving:

g `p <= q /\ MEM x p /\ MEM y p /\ findi x p <= findi y p ==> findi x q <= findi y q`;

This simple statement has a counter-example:
q = [1;2;3;4;3;5;1]
p = [2;4;1]
MEM 4 p /\ MEM 1 p /\ findi 4 p = 1 <= findi 1 p = 2, but findi 4 q = 3, yet findi 1 q = 0.
This is because findi gives the first appearance of the member.
This can be fixed by ALL_DISTINCT, but the idea of order-preserving should not depend on ALL_DISTINCT.
*)

(* Theorem: sl <= ls /\ MEM x sl ==>
            ?l1 l2 l3 l4. ls = l1 ++ [x] ++ l2 /\ sl = l3 ++ [x] ++ l4 /\ l3 <= l1 /\ l4 <= l2 *)
(* Proof:
   By sublist_induct, this is to show:
   (1) MEM x [] ==> ?l1 l2 l3 l4...
       Note MEM x [] = F                       by MEM
       hence true.
   (2) MEM x sl ==> ?l1 l2 l3 l4... /\ sl <= ls /\ MEM x (h::sl) ==>
       ?l1 l2 l3 l4. h::ls = l1 ++ [x] ++ l2 /\ h::sl = l3 ++ [x] ++ l4 /\ l3 <= l1 /\ l4 <= l2
       Note MEM x (h::sl)
        ==> x = h \/ MEM x sl                  by MEM
       If x = h,
          Then h::ls = [h] ++ ls               by CONS_APPEND
           and h::sl = [h] ++ sl               by CONS_APPEND
       Pick l1 = [], l2 = ls, l3 = [], l4 = sl.
       Then l3 <= l1 since                     by sublist_nil
        and l4 <= l2 since sl <= ls            by induction hypothesis
       Otherwise, MEM x sl,
           Note ?l1 l2 l3 l4.
                ls = l1 ++ [x] ++ l2 /\ sl = l3 ++ [x] ++ l4 /\ l3 <= l1 /\ l4 <= l2
                                               by induction hypothesis
           Then h::ls = h::(l1 ++ [x] ++ l2)
                      = h::l1 ++ [x] ++ l2     by APPEND
            and h::sl = h::(l3 ++ [x] ++ l4)
                      = h::l3 ++ [x] ++ l4     by APPEND
           Pick new l1 = h::l1, l2 = l2, l3 = h::l3, l4 = l4.
           Then l3 <= l1 ==> h::l3 <= h::l1    by sublist_cons
   (3) MEM x sl ==> ?l1 l2 l3 l4... /\ sl <= ls /\ MEM x sl ==>
       ?l1 l2 l3 l4. h::ls = l1 ++ [x] ++ l2 /\ sl = l3 ++ [x] ++ l4 /\ l3 <= l1 /\ l4 <= l2
       Note ?l1 l2 l3 l4.
            ls = l1 ++ [x] ++ l2 /\ sl = l3 ++ [x] ++ l4 /\ l3 <= l1 /\ l4 <= l2
                                               by induction hypothesis
       Then h::ls = h::(l1 ++ [x] ++ l2)
                  = h::l1 ++ [x] ++ l2         by APPEND
        Pick new l1 = h::l1, l2 = l2, l3 = l3, l4 = l4.
        Then l3 <= l1 ==> l3 <= h::l1          by sublist_cons_include
*)
Theorem sublist_order:
  !ls sl x. sl <= ls /\ MEM x sl ==>
            ?l1 l2 l3 l4. ls = l1 ++ [x] ++ l2 /\ sl = l3 ++ [x] ++ l4 /\ l3 <= l1 /\ l4 <= l2
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  qid_spec_tac `ls` >>
  qid_spec_tac `sl` >>
  ho_match_mp_tac sublist_induct >>
  rpt strip_tac >-
  fs[] >-
 (fs[] >| [
    map_every qexists_tac [`[]`, `ls`, `[]`, `sl`] >>
    simp[sublist_nil],
    fs[] >>
    map_every qexists_tac [`h::l1`, `l2`, `h::l3`, `l4`] >>
    simp[GSYM sublist_cons]
  ]) >>
  fs[] >>
  map_every qexists_tac [`h::l1`, `l2`, `l3`, `l4`] >>
  simp[sublist_cons_include]
QED

(* Theorem: sl <= ls /\ MONO_INC ls ==> MONO_INC sl *)
(* Proof:
   By sublist induction, this is to show:
   (1) n < LENGTH [] /\ m <= n ==> EL m [] <= EL n []
       Note LENGTH [] = 0                      by LENGTH
         so assumption is F, hence T.
   (2) MONO_INC ls ==> MONO_INC sl /\ sl <= ls /\
       MONO_INC (h::ls) /\ m <= n /\ n < LENGTH (h::sl) ==> EL m (h::sl) <= EL n (h::sl)
       Note MONO_INC (h::ls) ==> MONO_INC ls   by MONO_INC_CONS
       If m = 0,
          If n = 0,
             Then EL 0 (h::sl) = h, hence T.
          If 0 < n,
             Then 0 <= PRE n,
               so EL n (h::sl) = EL (PRE n) sl
             Let x = EL 0 sl.
             Then x <= EL (PRE n) sl           by MONO_INC sl
              But MEM x sl                     by EL_MEM
              ==> MEM x ls                     by sublist_mem
               so h <= x                       by MONO_INC (h::ls)
              Thus h <= EL n (h::sl)           by inequality
       If 0 < m,
          Then m <= n means 0 < n.
          Thus PRE m <= PRE n
                EL m (h::sl)
              = EL (PRE m) sl                  by EL_CONS, 0 < m
             <= EL (PRE n) sl                  by induction hypothesis
              = EL n (h::sl)                   by EL_CONS, 0 < n

   (3) MONO_INC ls ==> MONO_INC sl /\ sl <= ls /\
       MONO_INC (h::ls) /\ m <= n /\ n < LENGTH sl ==> EL m sl <= EL n sl
       Note MONO_INC (h::ls) ==> MONO_INC ls   by MONO_INC_CONS
       Thus MONO_INC sl                        by induction hypothesis
         so m <= n ==> EL m sl <= EL n sl      by MONO_INC sl
*)
Theorem sublist_MONO_INC:
  !ls sl. sl <= ls /\ MONO_INC ls ==> MONO_INC sl
Proof
  ntac 3 strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  qid_spec_tac `ls` >>
  qid_spec_tac `sl` >>
  ho_match_mp_tac sublist_induct >>
  rpt strip_tac >-
  fs[] >-
 (`MONO_INC ls` by metis_tac[MONO_INC_CONS] >>
  `m = 0 \/ 0 < m` by decide_tac >| [
    `n = 0 \/ 0 < n` by decide_tac >-
    simp[] >>
    `0 <= PRE n` by decide_tac >>
    qabbrev_tac `x = EL 0 sl` >>
    `x <= EL (PRE n) sl` by fs[Abbr`x`] >>
    `MEM x sl` by fs[EL_MEM, Abbr`x`] >>
    `h <= x` by metis_tac[MONO_INC_HD, sublist_mem] >>
    simp[EL_CONS],
    `0 < n /\ PRE m <= PRE n` by decide_tac >>
    `EL (PRE m) sl <= EL (PRE n) sl` by fs[] >>
    simp[EL_CONS]
  ]) >>
  `MONO_INC ls` by metis_tac[MONO_INC_CONS] >>
  fs[]
QED

(* Theorem: sl <= ls /\ MONO_DEC ls ==> MONO_DEC sl *)
(* Proof:
   By sublist induction, this is to show:
   (1) n < LENGTH [] /\ m <= n ==> EL n [] <= EL m []
       Note LENGTH [] = 0                      by LENGTH
         so assumption is F, hence T.
   (2) MONO_DEC ls ==> MONO_DEC sl /\ sl <= ls /\
       MONO_DEC (h::ls) /\ m <= n /\ n < LENGTH (h::sl) ==> EL n (h::sl) <= EL m (h::sl)
       Note MONO_DEC (h::ls) ==> MONO_DEC ls   by MONO_DEC_CONS
       If m = 0,
          If n = 0,
             Then EL 0 (h::sl) = h, hence T.
          If 0 < n,
             Then 0 <= PRE n,
               so EL n (h::sl) = EL (PRE n) sl
             Let x = EL 0 sl.
             Then EL (PRE n) sl <= x           by MONO_DEC sl
              But MEM x sl                     by EL_MEM
              ==> MEM x ls                     by sublist_mem
               so x <= h                       by MONO_DEC (h::ls)
              Thus EL n (h::sl) <= h           by inequality
       If 0 < m,
          Then m <= n means 0 < n.
          Thus PRE m <= PRE n
                EL n (h::sl)
              = EL (PRE n) sl                  by EL_CONS, 0 < n
             <= EL (PRE m) sl                  by induction hypothesis
              = EL m (h::sl)                   by EL_CONS, 0 < m

   (3) MONO_DEC ls ==> MONO_DEC sl /\ sl <= ls /\
       MONO_DEC (h::ls) /\ m <= n /\ n < LENGTH sl ==> EL n sl <= EL m sl
       Note MONO_DEC (h::ls) ==> MONO_DEC ls   by MONO_DEC_CONS
       Thus MONO_DEC sl                        by induction hypothesis
         so m <= n ==> EL n sl <= EL m sl      by MONO_DEC sl
*)
Theorem sublist_MONO_DEC:
  !ls sl. sl <= ls /\ MONO_DEC ls ==> MONO_DEC sl
Proof
  ntac 3 strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  qid_spec_tac `ls` >>
  qid_spec_tac `sl` >>
  ho_match_mp_tac sublist_induct >>
  rpt strip_tac >-
  fs[] >-
 (`MONO_DEC ls` by metis_tac[MONO_DEC_CONS] >>
  `m = 0 \/ 0 < m` by decide_tac >| [
    `n = 0 \/ 0 < n` by decide_tac >-
    simp[] >>
    `0 <= PRE n` by decide_tac >>
    qabbrev_tac `x = EL 0 sl` >>
    `EL (PRE n) sl <= x` by fs[Abbr`x`] >>
    `MEM x sl` by fs[EL_MEM, Abbr`x`] >>
    `x <= h` by metis_tac[MONO_DEC_HD, sublist_mem] >>
    simp[EL_CONS],
    `0 < n /\ PRE m <= PRE n` by decide_tac >>
    `EL (PRE n) sl <= EL (PRE m) sl` by fs[] >>
    simp[EL_CONS]
  ]) >>
  `MONO_DEC ls` by metis_tac[MONO_DEC_CONS] >>
  fs[]
QED

(* Yes, finally! *)

(* ------------------------------------------------------------------------- *)
(* FILTER as sublist.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FILTER P ls <= ls *)
(* Proof:
   By induction on ls.
   Base: FILTER P [] <= [],
      Note FILTER P [] = []        by FILTER
       and [] <= []                by sublist_refl
   Step: FILTER P ls <= ls ==>
         !h. FILTER P (h::ls) <= h::ls
     If P h,
             FILTER P ls <= ls                 by induction hypothesis
         ==> h::FILTER P ls <= h::ls           by sublist_cons
         ==> FILTER P (h::ls) <= h::ls         by FILTER, P h.

     If ~P h,
             FILTER P ls <= ls                 by induction hypothesis
         ==> FILTER P ls <= h::ls              by sublist_cons_include
         ==> FILTER P (h::ls) <= h::ls         by FILTER, ~P h.
*)
Theorem FILTER_sublist:
  !P ls. FILTER P ls <= ls
Proof
  strip_tac >>
  Induct >-
  simp[sublist_refl] >>
  rpt strip_tac >>
  Cases_on `P h` >-
  metis_tac[FILTER, sublist_cons] >>
  metis_tac[FILTER, sublist_cons_include]
QED

(* Theorem: MONO_INC ls ==> MONO_INC (FILTER P ls) *)
(* Proof:
   Note (FILTER P ls) <= ls        by FILTER_sublist
   With MONO_INC ls
    ==> MONO_INC (FILTER P ls)     by sublist_MONO_INC
*)
Theorem FILTER_MONO_INC:
  !P ls. MONO_INC ls ==> MONO_INC (FILTER P ls)
Proof
  metis_tac[FILTER_sublist, sublist_MONO_INC]
QED

(* Theorem: MONO_DEC ls ==> MONO_DEC (FILTER P ls) *)
(* Proof:
   Note (FILTER P ls) <= ls        by FILTER_sublist
   With MONO_DEC ls
    ==> MONO_DEC (FILTER P ls)     by sublist_MONO_DEC
*)
Theorem FILTER_MONO_DEC:
  !P ls. MONO_DEC ls ==> MONO_DEC (FILTER P ls)
Proof
  metis_tac[FILTER_sublist, sublist_MONO_DEC]
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
