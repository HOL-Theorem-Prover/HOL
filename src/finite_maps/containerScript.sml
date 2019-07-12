(*---------------------------------------------------------------------------
       Mapping finite sets (and bags) into lists. Needs a constraint
       that the set (bag) is finite. One might think to introduce this
       function via a constant specification, but in this case,
       TFL technology makes an easy job of it.
 ---------------------------------------------------------------------------*)

open HolKernel Parse boolLib pred_setTheory listTheory bagTheory
     Defn TotalDefn BasicProvers sortingTheory finite_mapTheory
     listSimps bossLib;

(* ---------------------------------------------------------------------*)
(* Create the new theory.                                               *)
(* ---------------------------------------------------------------------*)

val _ = new_theory "container";
  (* this theory may be for the chop; the set-related theorems are now all
     in listTheory.  The bag-related ones might end up there too if we
     decided to allow bag to move back in the build order.  Alternatively,
     the bag-related theorems could just go into bagTheory... *)

val SET_TO_LIST_THM = save_thm("SET_TO_LIST_THM", listTheory.SET_TO_LIST_THM)
val SET_TO_LIST_IND = save_thm("SET_TO_LIST_IND", listTheory.SET_TO_LIST_IND);

(*---------------------------------------------------------------------------
      Map a list into a set.
 ---------------------------------------------------------------------------*)

val LIST_TO_SET_THM = save_thm("LIST_TO_SET_THM", listTheory.LIST_TO_SET_THM)

(*---------------------------------------------------------------------------
            Some consequences
 ---------------------------------------------------------------------------*)

val SET_TO_LIST_INV = save_thm("SET_TO_LIST_INV", listTheory.SET_TO_LIST_INV)
val SET_TO_LIST_CARD = save_thm("SET_TO_LIST_CARD", listTheory.SET_TO_LIST_CARD)
val SET_TO_LIST_IN_MEM = save_thm("SET_TO_LIST_IN_MEM",
                                  listTheory.SET_TO_LIST_IN_MEM)
val MEM_SET_TO_LIST = save_thm("MEM_SET_TO_LIST", listTheory.MEM_SET_TO_LIST)
val SET_TO_LIST_SING = save_thm("SET_TO_LIST_SING", listTheory.SET_TO_LIST_SING)
val UNION_APPEND = save_thm("UNION_APPEND", listTheory.UNION_APPEND);
val LIST_TO_SET_APPEND = save_thm("LIST_TO_SET_APPEND",
                                  listTheory.LIST_TO_SET_APPEND)
val FINITE_LIST_TO_SET = save_thm("FINITE_LIST_TO_SET",
                                  listTheory.FINITE_LIST_TO_SET)

(*---------------------------------------------------------------------------
    Lists and bags. Note that we also have SET_OF_BAG and BAG_OF_SET
    in bagTheory.
 ---------------------------------------------------------------------------*)

val LIST_TO_BAG_def =
  Define
    `(LIST_TO_BAG [] = {||})
 /\  (LIST_TO_BAG (h::t) = BAG_INSERT h (LIST_TO_BAG t))`;
val _ = export_rewrites ["LIST_TO_BAG_def"]

val LIST_TO_BAG_alt = store_thm ("LIST_TO_BAG_alt",
  ``!l x. LIST_TO_BAG l x = LENGTH (FILTER ($= x) l)``,
  EVERY [ REPEAT GEN_TAC, Induct_on `l`,
    SIMP_TAC list_ss [LIST_TO_BAG_def, EMPTY_BAG_alt, BAG_INSERT],
    GEN_TAC, COND_CASES_TAC THENL [ BasicProvers.VAR_EQ_TAC, ALL_TAC],
    ASM_SIMP_TAC arith_ss [LENGTH] ]) ;

val BAG_TO_LIST = Hol_defn "BAG_TO_LIST"
    `BAG_TO_LIST bag =
       if FINITE_BAG bag
         then if bag = EMPTY_BAG then []
              else BAG_CHOICE bag :: BAG_TO_LIST (BAG_REST bag)
         else ARB`;

val (BAG_TO_LIST_EQN,BAG_TO_LIST_IND) =
Defn.tprove
 (BAG_TO_LIST,
  WF_REL_TAC `measure BAG_CARD`
   THEN PROVE_TAC [PSUB_BAG_CARD, PSUB_BAG_REST]);

val BAG_TO_LIST_THM = save_thm("BAG_TO_LIST_THM",
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME ``FINITE_BAG bag``] BAG_TO_LIST_EQN));

val BAG_TO_LIST_IND = save_thm("BAG_TO_LIST_IND",BAG_TO_LIST_IND);

(*---------------------------------------------------------------------------
       Some consequences.
 ---------------------------------------------------------------------------*)

val BAG_TO_LIST_INV = Q.store_thm("BAG_TO_LIST_INV",
`!b. FINITE_BAG b ==> (LIST_TO_BAG(BAG_TO_LIST b) = b)`,
 recInduct BAG_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH BAG_TO_LIST_THM]
   THEN RW_TAC bool_ss [LIST_TO_BAG_def]
   THEN PROVE_TAC [BAG_INSERT_CHOICE_REST,FINITE_SUB_BAG,SUB_BAG_REST]);

val BAG_IN_MEM = Q.store_thm("BAG_IN_MEM",
`!b. FINITE_BAG b ==> !x. BAG_IN x b = MEM x (BAG_TO_LIST b)`,
 recInduct BAG_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH BAG_TO_LIST_THM]
   THEN RW_TAC bool_ss [listTheory.MEM,NOT_IN_EMPTY_BAG]
   THEN PROVE_TAC [FINITE_SUB_BAG,SUB_BAG_REST,
                   BAG_INSERT_CHOICE_REST,BAG_IN_BAG_INSERT]);

(* version with the equation the "rewrite" way round *)
val MEM_BAG_TO_LIST = Q.store_thm
("MEM_BAG_TO_LIST",
 `!b. FINITE_BAG b ==> !x. MEM x (BAG_TO_LIST b) = BAG_IN x b`,
  PROVE_TAC [BAG_IN_MEM]);

val _ = export_rewrites ["MEM_BAG_TO_LIST"];

val FINITE_LIST_TO_BAG = Q.store_thm(
"FINITE_LIST_TO_BAG",
`FINITE_BAG (LIST_TO_BAG ls)`,
Induct_on `ls` THEN SRW_TAC [][LIST_TO_BAG_def]);
val _ = export_rewrites["FINITE_LIST_TO_BAG"];


val EVERY_LIST_TO_BAG = Q.store_thm(
"EVERY_LIST_TO_BAG",
`BAG_EVERY P (LIST_TO_BAG ls) <=> EVERY P ls`,
Induct_on `ls` THEN SRW_TAC [][LIST_TO_BAG_def]);


val LIST_TO_BAG_APPEND = store_thm ("LIST_TO_BAG_APPEND",
``!l1 l2.
LIST_TO_BAG (l1 ++ l2) =
BAG_UNION (LIST_TO_BAG l1) (LIST_TO_BAG l2)``,
Induct_on `l1` THENL [
  SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_UNION_EMPTY],
  ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_UNION_INSERT]
]);

val LIST_TO_BAG_MAP = store_thm ("LIST_TO_BAG_MAP",
  ``LIST_TO_BAG (MAP f b) = BAG_IMAGE f (LIST_TO_BAG b)``,
  EVERY [ Induct_on `b`,
    ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_IMAGE_EMPTY],
    GEN_TAC, irule (GSYM BAG_IMAGE_FINITE_INSERT),
    irule FINITE_LIST_TO_BAG] ) ;

val LIST_TO_BAG_FILTER = store_thm ("LIST_TO_BAG_FILTER",
  ``LIST_TO_BAG (FILTER f b) = BAG_FILTER f (LIST_TO_BAG b)``,
  EVERY [ Induct_on `b`,
    ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_FILTER_EMPTY],
    GEN_TAC, COND_CASES_TAC,
    ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_FILTER_BAG_INSERT] ] ) ;


val INN_LIST_TO_BAG = store_thm ("INN_LIST_TO_BAG",
``!n h l. BAG_INN h n (LIST_TO_BAG l) = (LENGTH (FILTER ($= h) l) >= n)``,
Induct_on `l` THENL [
  SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_INN_EMPTY_BAG],
  ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_INN_BAG_INSERT, COND_RAND, COND_RATOR]
]);


val IN_LIST_TO_BAG = store_thm ("IN_LIST_TO_BAG",
``!h l. BAG_IN h (LIST_TO_BAG l) = MEM h l``,
Induct_on `l` THENL [
  SIMP_TAC list_ss [LIST_TO_BAG_def, NOT_IN_EMPTY_BAG],
  ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_IN_BAG_INSERT]
]);

val LIST_TO_BAG_DISTINCT = store_thm ("LIST_TO_BAG_DISTINCT",
  ``BAG_ALL_DISTINCT (LIST_TO_BAG b) = ALL_DISTINCT b``,
  Induct_on `b` THEN
    ASM_SIMP_TAC (srw_ss ()) [LIST_TO_BAG_def, IN_LIST_TO_BAG]) ;

val LIST_TO_BAG_EQ_EMPTY = store_thm ("LIST_TO_BAG_EQ_EMPTY",
``!l. (LIST_TO_BAG l = EMPTY_BAG) = (l = [])``,
Cases_on `l` THEN
SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_INSERT_NOT_EMPTY]);


val PERM_LIST_TO_BAG = store_thm ("PERM_LIST_TO_BAG",
  ``!l1 l2. (LIST_TO_BAG l1 = LIST_TO_BAG l2) = PERM l1 l2``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [PERM_DEF] THEN EQ_TAC THENL [
    EVERY [ REPEAT STRIP_TAC,
      POP_ASSUM (fn th => ASSUME_TAC (Q.AP_THM th `x`)),
      FULL_SIMP_TAC std_ss [LIST_TO_BAG_alt],
      ONCE_REWRITE_TAC [FILTER_EQ_REP], ASM_SIMP_TAC std_ss [] ],
    DISCH_TAC THEN irule EQ_EXT THEN ASM_SIMP_TAC std_ss [LIST_TO_BAG_alt] ]) ;

val CARD_LIST_TO_BAG = Q.store_thm(
"CARD_LIST_TO_BAG",
`BAG_CARD (LIST_TO_BAG ls) = LENGTH ls`,
Induct_on `ls` THEN SRW_TAC [][BAG_CARD_THM,arithmeticTheory.ADD1])
before export_rewrites ["CARD_LIST_TO_BAG"];

val EQ_TRANS' = REWRITE_RULE [GSYM AND_IMP_INTRO] EQ_TRANS ;
val th = MATCH_MP EQ_TRANS' (SYM CARD_LIST_TO_BAG) ;

val BAG_TO_LIST_CARD = store_thm ("BAG_TO_LIST_CARD",
  ``!b. FINITE_BAG b ==> (LENGTH (BAG_TO_LIST b) = BAG_CARD b)``,
  EVERY [REPEAT STRIP_TAC, irule th,
    ASM_SIMP_TAC bool_ss [BAG_TO_LIST_INV] ]) ;

val BAG_TO_LIST_EQ_NIL = Q.store_thm(
"BAG_TO_LIST_EQ_NIL",
`FINITE_BAG b ==>
 (([] = BAG_TO_LIST b) <=> (b = {||})) /\
 ((BAG_TO_LIST b = []) <=> (b = {||}))`,
Q.SPEC_THEN `b` STRUCT_CASES_TAC BAG_cases THEN
SRW_TAC [][BAG_TO_LIST_THM])
before export_rewrites ["BAG_TO_LIST_EQ_NIL"];

local open rich_listTheory arithmeticTheory in
  val LIST_ELEM_COUNT_LIST_TO_BAG = Q.store_thm(
    "LIST_ELEM_COUNT_LIST_TO_BAG",
    `LIST_ELEM_COUNT e ls = LIST_TO_BAG ls e`,
    Induct_on `ls` THEN SRW_TAC [][LIST_ELEM_COUNT_THM,EMPTY_BAG] THEN
    Cases_on `h = e` THEN SRW_TAC [][LIST_ELEM_COUNT_THM,BAG_INSERT,ADD1]);
end

Theorem LIST_TO_BAG_SUB_BAG_FLAT_suff:
  !ls1 ls2. LIST_REL (\l1 l2. LIST_TO_BAG l1 <= LIST_TO_BAG l2) ls1 ls2 ==>
            LIST_TO_BAG (FLAT ls1) <= LIST_TO_BAG (FLAT ls2)
Proof
  Induct_on ‘LIST_REL’ >> srw_tac [bagLib.SBAG_SOLVE_ss] [LIST_TO_BAG_APPEND]
QED

Theorem LIST_TO_BAG_SUBSET:
  !l1 l2. LIST_TO_BAG l1 <= LIST_TO_BAG l2 ==> set l1 SUBSET set l2
Proof
  Induct >> rw[LIST_TO_BAG_def] >> imp_res_tac BAG_INSERT_SUB_BAG_E >>
  imp_res_tac IN_LIST_TO_BAG >> fs[]
QED

(*---------------------------------------------------------------------------*)
(* Following packaging of multiset order applied to lists is easier to use   *)
(* in some termination proofs, typically those of worklist algorithms, where *)
(* the head of the list is replaced by a list of smaller elements.           *)
(*---------------------------------------------------------------------------*)

val mlt_list_def =
 Define
   `mlt_list R =
     \l1 l2.
       ?h t list.
         (l1 = list ++ t) /\
         (l2 = h::t) /\
         (!e. MEM e list ==> R e h)`;

val WF_mlt_list = Q.store_thm
("WF_mlt_list",
 `!R. WF(R) ==> WF (mlt_list R)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC relationTheory.WF_SUBSET THEN
  Q.EXISTS_TAC `inv_image (mlt1 R) LIST_TO_BAG` THEN
  CONJ_TAC THENL
  [METIS_TAC [relationTheory.WF_inv_image,bagTheory.WF_mlt1],
   RW_TAC list_ss [mlt_list_def, relationTheory.inv_image_thm,bagTheory.mlt1_def]
   THENL
   [METIS_TAC [FINITE_LIST_TO_BAG],
    METIS_TAC [FINITE_LIST_TO_BAG],
    MAP_EVERY Q.EXISTS_TAC [`h`, `LIST_TO_BAG list`, `LIST_TO_BAG t`]
     THEN RW_TAC std_ss [BAG_INSERT_UNION,LIST_TO_BAG_APPEND,LIST_TO_BAG_def]
      THENL [METIS_TAC [COMM_BAG_UNION,ASSOC_BAG_UNION,BAG_UNION_EMPTY],
             METIS_TAC [IN_LIST_TO_BAG]]]]);


(*---------------------------------------------------------------------------*)
(* Tell the termination proof infrastructure about mlt_list                  *)
(*---------------------------------------------------------------------------*)

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn _ => let
   fun S s = [PP.add_string s, PP.add_newline]
 in
   PP.block PP.CONSISTENT 0 (
     S "val _ = TotalDefn.WF_thms := (!TotalDefn.WF_thms @ [WF_mlt_list]);" @
     S "val _ = TotalDefn.termination_simps := \
         \(!TotalDefn.termination_simps @ [mlt_list_def]);"
   )
  end)};


(*---------------------------------------------------------------------------
    finite maps and bags.
 ---------------------------------------------------------------------------*)

val BAG_OF_FMAP = Define `BAG_OF_FMAP f b =
  \x. CARD (\k. (k IN FDOM b) /\ (x = f k (b ' k)))`


val BAG_OF_FMAP_THM = store_thm ("BAG_OF_FMAP_THM",
``(!f. (BAG_OF_FMAP f FEMPTY = EMPTY_BAG)) /\
  (!f b k v. (BAG_OF_FMAP f (b |+ (k, v)) =
             BAG_INSERT (f k v) (BAG_OF_FMAP f (b \\ k))))``,
SIMP_TAC std_ss [BAG_OF_FMAP, FDOM_FEMPTY, NOT_IN_EMPTY, EMPTY_BAG,
                 combinTheory.K_DEF,
                 BAG_INSERT, FDOM_FUPDATE, IN_INSERT,
                 GSYM EMPTY_DEF, CARD_EMPTY] THEN
ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN SIMP_TAC std_ss [] THEN
Cases_on `x = f k v` THENL [
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
     FAPPLY_FUPDATE_THM, FDOM_DOMSUB, IN_DELETE,
     DOMSUB_FAPPLY_THM] THEN
   `(\k'. ((k' = k) \/ k' IN FDOM b) /\
           (f k v = f k' ((if k' = k then v else b ' k')))) =
           k INSERT (\k'. (k' IN FDOM b /\ ~(k' = k)) /\ (f k v = f k' (b ' k')))` by (
     SIMP_TAC std_ss [EXTENSION, IN_INSERT, IN_ABS] THEN
     GEN_TAC THEN Cases_on `x' = k` THEN ASM_REWRITE_TAC[]
   ) THEN
   ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   Q.ABBREV_TAC `ks = (\k'. (k' IN FDOM b /\ k' <> k) /\ (f k v = f k' (b ' k')))` THEN
   `FINITE ks` by (
      `ks = ks INTER FDOM b` suffices_by (
         STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
         MATCH_MP_TAC FINITE_INTER THEN
         REWRITE_TAC[FDOM_FINITE]
      ) THEN
      Q.UNABBREV_TAC `ks` THEN
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
      PROVE_TAC[]
   ) THEN
   `~(k IN ks)` by (
      Q.UNABBREV_TAC `ks` THEN
      SIMP_TAC std_ss [IN_ABS]
   ) THEN
   ASM_SIMP_TAC arith_ss [CARD_INSERT],


   FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
      FAPPLY_FUPDATE_THM, FDOM_DOMSUB, IN_DELETE,
      DOMSUB_FAPPLY_THM] THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN SIMP_TAC std_ss [] THEN
   Cases_on `x' = k` THEN (
      ASM_SIMP_TAC std_ss []
   )
]);

val BAG_IN_BAG_OF_FMAP = store_thm ("BAG_IN_BAG_OF_FMAP",
``!x f b. BAG_IN x (BAG_OF_FMAP f b) =
          ?k. k IN FDOM b /\ (x = f k (b ' k))``,
SIMP_TAC std_ss [BAG_OF_FMAP, BAG_IN, BAG_INN] THEN
`!X. (X >= (1:num)) = ~(X = 0)` by bossLib.DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT GEN_TAC THEN
`FINITE (\k. k IN FDOM b /\ (x = f k (b ' k)))` by (
   `(\k. k IN FDOM b /\ (x = f k (b ' k))) =
    (\k. k IN FDOM b /\ (x = f k (b ' k))) INTER (FDOM b)` by (
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
      METIS_TAC[]
   ) THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FINITE_INTER THEN
   REWRITE_TAC[FDOM_FINITE]
) THEN
ASM_SIMP_TAC std_ss [CARD_EQ_0] THEN
SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS]);

val FINITE_BAG_OF_FMAP = store_thm ("FINITE_BAG_OF_FMAP",
``!f b. FINITE_BAG (BAG_OF_FMAP f b)``,
GEN_TAC THEN HO_MATCH_MP_TAC fmap_INDUCT THEN
SIMP_TAC std_ss [BAG_OF_FMAP_THM, FINITE_EMPTY_BAG,
                 DOMSUB_NOT_IN_DOM, FINITE_BAG_INSERT]);



val _ = export_theory ();
