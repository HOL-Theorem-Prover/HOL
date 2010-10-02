(*****************************************************************************)
(* Encoding and decoding of finite maps to lists and then s-expressions      *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Load theories                                                             *)
(*****************************************************************************)
(*
load "finite_mapTheory";
load "sortingTheory";
load "translateTheory";
quietdec := true;
open finite_mapTheory sortingTheory pred_setTheory listTheory pred_setLib;
quietdec := false;
*)

(*****************************************************************************)
(* Boilerplate needed for compilation: open HOL4 systems modules.            *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib;

(*****************************************************************************)
(* Theories for compilation                                                  *)
(*****************************************************************************)

open finite_mapTheory pred_setTheory listTheory pred_setLib sortingTheory;

(*****************************************************************************)
(* Start new theory "fmap_encode"                                            *)
(*****************************************************************************)

val _ = new_theory "fmap_encode";

val PULL_CONV = REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV));
val PULL_RULE = CONV_RULE PULL_CONV;

val IND_STEP_TAC = PAT_ASSUM ``!y. P ==> Q`` (MATCH_MP_TAC o PULL_RULE);

(*****************************************************************************)
(* fold for finite maps                                                      *)
(*****************************************************************************)

val fold_def = TotalDefn.tDefine "fold" `fold f v map = 
             if map = FEMPTY 
                then v
                else let x = (@x. x IN FDOM map)
                     in (f (x, map ' x) (fold f v (map \\ x)))`
   (WF_REL_TAC `measure (FCARD o SND o SND)` THEN
    RW_TAC std_ss [FDOM_FUPDATE,FCARD_DEF,FDOM_DOMSUB,CARD_DELETE,FDOM_FINITE] THEN
    METIS_TAC [FDOM_F_FEMPTY1,CARD_EQ_0,FDOM_EQ_EMPTY,FDOM_FINITE,arithmeticTheory.NOT_ZERO_LT_ZERO]);

(*****************************************************************************)
(* Encoding and decoding to lists                                            *)
(*                                                                           *)
(* Note: M2L, like SET_TO_LIST, is non-deterministic, so we cannot prove     *)
(*       M2L (L2M x) = x for any x.                                          *)
(*                                                                           *)
(*****************************************************************************)

val M2L_def = Define `M2L = fold CONS []`;

val L2M_def = Define `L2M = FOLDR (combin$C FUPDATE) FEMPTY`;

val L2M = store_thm("L2M", 
    ``(L2M [] = FEMPTY) /\ (!a b. L2M (a::b) = L2M b |+ a)``, 
    RW_TAC std_ss [L2M_def,FOLDR]);

(*****************************************************************************)
(* Definitions to capture the properties that a list or a set representing   *)
(* a finite map would have.                                                  *)
(*****************************************************************************)

val uniql_def = 
    Define `uniql l = !x y y'. MEM (x,y) l /\ MEM (x,y') l ==> (y = y')`;

val uniqs_def =
    Define `uniqs s = !x y y'. (x,y) IN s /\ (x,y') IN s ==> (y = y')`;

(*****************************************************************************)
(* Theorems about uniqs and l                                                *)
(*****************************************************************************)

val uniqs_cons = prove(``uniqs (a INSERT b) ==> uniqs b``,
    RW_TAC std_ss [uniqs_def,IN_INSERT] THEN METIS_TAC []);

val uniql_cons = prove(``!a h. uniql (h::a) ==> uniql a``,
    Induct THEN RW_TAC std_ss [uniql_def, MEM] THEN METIS_TAC []);

val uniqs_eq = prove(``!a. FINITE a ==> (uniqs a = uniql (SET_TO_LIST a))``,
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    RW_TAC std_ss [SET_TO_LIST_THM, FINITE_EMPTY, uniql_def, uniqs_def, MEM, NOT_IN_EMPTY] THEN
    EQ_TAC THEN RW_TAC std_ss [] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    Q.EXISTS_TAC `x` THEN
    METIS_TAC [SET_TO_LIST_IN_MEM, FINITE_INSERT]);

val uniql_eq = prove(``!x. uniql x = uniqs (set x)``, 
    RW_TAC std_ss [uniql_def, uniqs_def, IN_LIST_TO_SET]);

val uniql_filter = prove(``!x. uniql x ==> uniql (FILTER P x)``,
    METIS_TAC [MEM_FILTER, uniql_def]);

val uniq_double = prove(``!a. uniql a ==> (uniql (SET_TO_LIST (set a)))``,
    Induct THEN
    RW_TAC std_ss [uniql_def, SET_TO_LIST_THM, LIST_TO_SET_THM, FINITE_EMPTY,
            MEM_SET_TO_LIST, MEM, NOT_IN_EMPTY, FINITE_LIST_TO_SET, IN_INSERT, IN_LIST_TO_SET]);

val uniql_empty = prove(``uniql []``, RW_TAC std_ss [MEM, uniql_def]);

(*****************************************************************************)
(* L2M_EQ: Lists representing maps give the same maps                        *)
(* !l1 l2. uniql l1 /\ uniql l2 /\ (set l1 = set l2) ==> (L2M l1 = L2M l2)   *)
(*****************************************************************************)

val delete_l2m = prove(``!a b. L2M a \\ b = L2M (FILTER ($~ o $= b o FST) a)``,
    Induct THEN TRY Cases THEN REPEAT (RW_TAC std_ss [L2M, FILTER, DOMSUB_FEMPTY, DOMSUB_FUPDATE_NEQ, DOMSUB_FUPDATE]));

val update_filter = prove(``!a b. L2M a |+ b = L2M (FILTER ($~ o $= (FST b) o FST) a) |+ b``,
    GEN_TAC THEN Cases THEN RW_TAC std_ss [] THEN METIS_TAC [FUPDATE_PURGE, delete_l2m]);

val length_filter = prove(``!a P. LENGTH (FILTER P a) <= LENGTH a``,
    Induct THEN RW_TAC std_ss [LENGTH, FILTER] THEN METIS_TAC [DECIDE ``a <= b ==> a <= SUC b``]);

val seteq_mem = prove(``!l1 l2. (set l1 = set l2) ==> (?h. MEM h l1 /\ MEM h l2) \/ (l1 = []) /\ (l2 = [])``,
   Induct THEN RW_TAC std_ss [LENGTH, MEM, LIST_TO_SET_THM, LIST_TO_SET_EQ_EMPTY] THEN
   METIS_TAC [IN_LIST_TO_SET, IN_INSERT]);

val l2m_update = prove(``!l h. uniql l /\ MEM h l ==> (L2M l = L2M l |+ h)``,
    Induct THEN TRY Cases THEN TRY (Cases_on `h'`) THEN RW_TAC std_ss [MEM,L2M] THEN RW_TAC std_ss [FUPDATE_EQ] THEN
    REVERSE (Cases_on `q' = q`) THEN RW_TAC std_ss [FUPDATE_COMMUTES, FUPDATE_EQ] THEN1 METIS_TAC [uniql_cons] THEN
    FULL_SIMP_TAC std_ss [uniql_def] THEN METIS_TAC [MEM]);

val length_filter_mem = prove(``!l P. (?x. MEM x l /\ ~(P x)) ==> (LENGTH (FILTER P l) < LENGTH l)``,
    Induct THEN RW_TAC std_ss [FILTER,LENGTH,MEM] THEN
    METIS_TAC [length_filter, DECIDE ``a <= b ==> a < SUC b``]);

val L2M_EQ = store_thm("L2M_EQ", 
    ``!l1 l2. uniql l1 /\ uniql l2 /\ (set l1 = set l2) ==> (L2M l1 = L2M l2)``,
    REPEAT GEN_TAC THEN completeInduct_on `LENGTH l1 + LENGTH l2` THEN REPEAT STRIP_TAC THEN
    PAT_ASSUM ``!y. P`` (ASSUME_TAC o CONV_RULE (REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV)))) THEN
    IMP_RES_TAC seteq_mem THEN FULL_SIMP_TAC std_ss [L2M] THEN
    IMP_RES_TAC l2m_update THEN ONCE_ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [update_filter] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    RW_TAC std_ss [GSYM LENGTH_APPEND, GSYM rich_listTheory.FILTER_APPEND, uniql_filter, LIST_TO_SET_FILTER] THEN
    MATCH_MP_TAC length_filter_mem THEN
    Q.EXISTS_TAC `h` THEN RW_TAC std_ss [MEM_APPEND]);

(*****************************************************************************)
(* L2M_DOUBLE:                                                               *)
(* `!a. uniql a ==> (L2M (SET_TO_LIST (set a)) = L2M a)`                     *)
(*****************************************************************************)

val L2M_DOUBLE = prove(``!a. uniql a ==> (L2M (SET_TO_LIST (set a)) = L2M a)``,
    METIS_TAC [uniq_double, L2M_EQ, FINITE_LIST_TO_SET, SET_TO_LIST_INV]);

(*****************************************************************************)
(* EXISTS_MEM_M2L:                                                           *)
(* `!x a. (?y. MEM (a,y) (M2L x)) = a IN FDOM x`                             *)
(*****************************************************************************)

val not_fempty_eq = prove(``!x. ~(x = FEMPTY) = (?y. y IN FDOM x)``,
    HO_MATCH_MP_TAC fmap_INDUCT THEN 
    RW_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FDOM_FEMPTY, NOT_IN_EMPTY, NOT_EQ_FEMPTY_FUPDATE] THEN 
    PROVE_TAC []);

val fcard_less = prove(``!y x. y IN FDOM x ==> FCARD (x \\ y) < FCARD x``,
    RW_TAC std_ss [FCARD_DEF, FDOM_DOMSUB, CARD_DELETE, FDOM_FINITE] THEN
    METIS_TAC [CARD_EQ_0, DECIDE ``0 < a = ¬(a = 0:num)``, NOT_IN_EMPTY, FDOM_FINITE]);

val uniql_rec = prove(``!x y. uniql x /\ ¬(?z. MEM (y,z) x) ==> (uniql ((y,z)::x))``,
    Induct THEN RW_TAC std_ss [uniql_def, MEM] THEN METIS_TAC []);

val INSERT_SING = prove(``(a INSERT b = {a}) = (b = {}) \/ (b = {a})``,
    ONCE_REWRITE_TAC [INSERT_SING_UNION] THEN RW_TAC std_ss [UNION_DEF,SET_EQ_SUBSET, SUBSET_DEF] THEN
    RW_TAC (std_ss ++ PRED_SET_ss) [] THEN METIS_TAC []);

val fold_FEMPTY = store_thm("fold_FEMPTY",``(!f v. fold f v FEMPTY = v)``,
    ONCE_REWRITE_TAC [fold_def] THEN RW_TAC std_ss []);

val infdom_lemma = prove(``!a b. ¬(a = b) /\ a IN FDOM x ==> (b IN FDOM x = b IN FDOM (x \\ a))``,
    RW_TAC (std_ss ++ PRED_SET_ss) [FDOM_DOMSUB, IN_DELETE]);

val EXISTS_MEM_M2L = store_thm("EXISTS_MEM_M2L",
   ``!x a. (?y. MEM (a,y) (M2L x)) = a IN FDOM x``,
   GEN_TAC THEN completeInduct_on `FCARD x` THEN REPEAT STRIP_TAC THEN
   PAT_ASSUM ``!y. P`` (ASSUME_TAC o CONV_RULE (REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV)))) THEN
   FULL_SIMP_TAC std_ss [M2L_def] THEN
   ONCE_REWRITE_TAC [fold_def] THEN REPEAT (CHANGED_TAC (RW_TAC std_ss [MEM, FDOM_FEMPTY, NOT_IN_EMPTY])) THEN
   Cases_on `(a = x')` THEN RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC [fcard_less, infdom_lemma, not_fempty_eq]);

(*****************************************************************************)
(* UNIQL_M2L:                                                                *)
(* `!x. uniql (M2L x)`                                                       *)
(*****************************************************************************)

val UNIQL_M2L = store_thm("UNIQL_M2L", ``!x. uniql (M2L x)``,
    GEN_TAC THEN completeInduct_on `FCARD x` THEN RW_TAC std_ss [M2L_def] THEN
    ONCE_REWRITE_TAC [fold_def] THEN RW_TAC std_ss [uniql_empty,GSYM M2L_def] THEN
    MATCH_MP_TAC uniql_rec THEN  `x' IN FDOM x` by METIS_TAC [not_fempty_eq] THEN
    RW_TAC std_ss [fcard_less] THEN
    `¬(x' IN FDOM (x \\ x'))` by RW_TAC std_ss [FDOM_DOMSUB, IN_DELETE] THEN
    METIS_TAC [infdom_lemma,EXISTS_MEM_M2L]);

(*****************************************************************************)
(* MEM_M2L:                                                                  *)
(* `!x y z. MEM (y,z) (M2L x) = y IN FDOM x /\ (z = x ' y)`                  *)
(*****************************************************************************)

val MEM_M2L = store_thm("MEM_M2L", 
    ``!x y z. MEM (y,z) (M2L x) = y IN FDOM x /\ (z = x ' y)``,
    GEN_TAC THEN completeInduct_on `FCARD x` THEN REPEAT STRIP_TAC THEN Cases_on `x = FEMPTY` THEN RW_TAC std_ss [M2L_def] THEN
    ONCE_REWRITE_TAC [fold_def] THEN RW_TAC std_ss [GSYM M2L_def, MEM, FDOM_FEMPTY, NOT_IN_EMPTY] THEN
    Cases_on `y = x'` THEN RW_TAC std_ss [MEM] THEN1
        METIS_TAC [not_fempty_eq, EXISTS_MEM_M2L, IN_DELETE, FDOM_DOMSUB] THEN
    PAT_ASSUM ``!y. P`` (ASSUME_TAC o CONV_RULE (REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV)))) THEN
    FULL_SIMP_TAC std_ss [] THEN
    `FCARD (x \\ x') < FCARD x` by METIS_TAC [fcard_less, not_fempty_eq] THEN
    RW_TAC std_ss [FDOM_DOMSUB, DOMSUB_FAPPLY_NEQ, IN_DELETE]);

(*****************************************************************************)
(* L2M_M2L_SETLIST                                                           *)
(* `!x. L2M (M2L x) = L2M (SET_TO_LIST (set (M2L x)))`                       *)
(*****************************************************************************)

val L2M_M2L_SETLIST = store_thm("L2M_M2L_SETLIST",
    ``!x. L2M (M2L x) = L2M (SET_TO_LIST (set (M2L x)))``,
    GEN_TAC THEN HO_MATCH_MP_TAC L2M_EQ THEN
    RW_TAC std_ss [UNIQL_M2L, GSYM uniqs_eq, FINITE_LIST_TO_SET, GSYM uniql_eq, SET_TO_LIST_INV]);

(*****************************************************************************)
(* SET_M2L_FUPDATE:                                                          *)
(* `!x y. set (M2L (x |+ y)) = set (y :: M2L (x \\ FST y))`                  *)
(*****************************************************************************)

val MEM_M2L_FUPDATE = prove(``!x y z. MEM (y,z) (M2L (x |+ (y,z)))``,
    RW_TAC std_ss [MEM_M2L, FDOM_FUPDATE, FAPPLY_FUPDATE, IN_INSERT]);

val MEM_M2L_PAIR = prove(``!x y. MEM y (M2L x) = (FST y) IN FDOM x /\ (SND y = x ' (FST y))``,
    GEN_TAC THEN Cases THEN RW_TAC std_ss [MEM_M2L]);

val SET_M2L_FUPDATE = store_thm("SET_M2L_FUPDATE",
    ``!x y. set (M2L (x |+ y)) = set (y :: M2L (x \\ FST y))``,
    RW_TAC std_ss [SET_EQ_SUBSET, SUBSET_DEF, LIST_TO_SET_THM, IN_INSERT, IN_LIST_TO_SET, MEM_M2L_PAIR, MEM] THEN
    TRY (Cases_on `x'`) THEN TRY (Cases_on `y`) THEN Cases_on `q = q'` THEN
    FULL_SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE, FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY, DOMSUB_FAPPLY_NEQ, NOT_EQ_FAPPLY]);

(*****************************************************************************)
(* FDOM_L2M:                                                                 *)
(* `!x y. y IN FDOM (L2M x) = ?z. MEM (y,z) x`                               *)
(*****************************************************************************)

val FDOM_L2M = store_thm("FDOM_L2M",
    ``!x y. y IN FDOM (L2M x) = ?z. MEM (y,z) x``,
    Induct THEN TRY (Cases_on `h`) THEN 
    RW_TAC std_ss [L2M,MEM,FDOM_FEMPTY,NOT_IN_EMPTY,FDOM_FUPDATE,IN_INSERT] THEN
    METIS_TAC []);

(*****************************************************************************)
(* FDOM_L2M_M2L                                                              *)
(* `!x. FDOM (L2M (M2L x)) = FDOM x`                                         *)
(*****************************************************************************)

val FDOM_L2M_M2L = prove(``!x. FDOM (L2M (M2L x)) = FDOM x``,
    RW_TAC std_ss [SET_EQ_SUBSET, SUBSET_DEF, FDOM_L2M, MEM_M2L]);

(*****************************************************************************)
(* L2M_APPLY:                                                                *)
(* `!x y z. uniql x /\ MEM (y,z) x ==> (L2M x ' y = z)`                      *)
(*****************************************************************************)

val L2M_APPLY = store_thm("L2M_APPLY",
    ``!x y z. uniql x /\ MEM (y,z) x ==> (L2M x ' y = z)``,
    Induct THEN TRY (Cases_on `h`) THEN RW_TAC std_ss [MEM,L2M] THEN
    Cases_on `q = y` THEN RW_TAC std_ss [FAPPLY_FUPDATE,NOT_EQ_FAPPLY] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [MEM, uniql_def] THEN
    METIS_TAC []);

(*****************************************************************************)
(* L2M_APPLY_MAP_EQ:                                                         *)
(* `!x f g y. ONE_ONE f /\ (?z. MEM (y,z) x) ==>                             *)
(*          (L2M (MAP (f ## g) x) ' (f y) = g (L2M x ' y))                   *)
(*****************************************************************************)

val L2M_APPLY_MAP_EQ = store_thm("L2M_APPLY_MAP_EQ",
    ``!x f g y. ONE_ONE f /\ (?z. MEM (y,z) x) ==> (L2M (MAP (f ## g) x) ' (f y) = g (L2M x ' y))``,
    Induct THEN NTAC 2 (RW_TAC std_ss [L2M, MAP, MEM,FAPPLY_FUPDATE_THM,pairTheory.PAIR_MAP]) THEN 
    FULL_SIMP_TAC std_ss [] THEN
    Cases_on `h` THEN RW_TAC std_ss [FAPPLY_FUPDATE_THM] THEN
    METIS_TAC [pairTheory.FST,ONE_ONE_THM]);

(*****************************************************************************)
(* APPLY_L2M_M2L                                                             *)
(* `y IN FDOM x ==> (L2M (M2L x) ' y = x ' y)`                               *)
(*****************************************************************************)

val APPLY_L2M_M2L = store_thm("APPLY_L2M_M2L",
    ``!x y. y IN FDOM x ==> (L2M (M2L x) ' y = x ' y)``,
    METIS_TAC [L2M_APPLY, UNIQL_M2L, MEM_M2L, FDOM_L2M_M2L, FDOM_L2M]);

(*****************************************************************************)
(* L2M_M2L:                                                                  *)
(* `!x. L2M (M2L x) = x`                                                     *)
(*****************************************************************************)

val L2M_M2L = store_thm("L2M_M2L",
    ``!x. L2M (M2L x) = x``,
    REWRITE_TAC [GSYM SUBMAP_ANTISYM, SUBMAP_DEF, FDOM_L2M_M2L] THEN
    RW_TAC std_ss [APPLY_L2M_M2L]);

(*****************************************************************************)
(* SETEQ                                                                     *)
(*****************************************************************************)

val SETEQ_def = Define `SETEQ l1 l2 = !x. MEM x l1 = MEM x l2`;

val SETEQ_TRANS = store_thm("SETEQ_TRANS",
    ``!l1 l2 l3. SETEQ l1 l2 /\ SETEQ l2 l3 ==> SETEQ l1 l3``,
    RW_TAC std_ss [SETEQ_def]);

val SETEQ_SYM = store_thm("SETEQ_SYM",
    ``!l. SETEQ l l``,
    RW_TAC std_ss [SETEQ_def]);

(*****************************************************************************)
(* M2L_L2M_SETEQ:                                                            *)
(* `!x. uniql x ==> SETEQ x (M2L (L2M x))`                                   *)
(*****************************************************************************)

val lemma1 = prove(``!x y z. uniql (y::x) ==> !z. MEM (FST y,z) x ==> (z = SND y)``,
    REPEAT (Cases ORELSE GEN_TAC) THEN REWRITE_TAC [uniql_def,MEM] THEN METIS_TAC []);

val M2L_L2M_SETEQ = store_thm("M2L_L2M_SETEQ",
    ``!x. uniql x ==> SETEQ x (M2L (L2M x))``,
    Induct THEN RW_TAC std_ss [L2M, M2L_def, fold_FEMPTY, SETEQ_def,MEM] THEN
    IMP_RES_TAC uniql_cons THEN
    Cases_on `x' = h` THEN Cases_on `MEM x' x` THEN Cases_on `x'` THEN
    RW_TAC std_ss [GSYM M2L_def,GSYM IN_LIST_TO_SET, SET_M2L_FUPDATE] THEN
    RW_TAC std_ss [IN_LIST_TO_SET, MEM, MEM_M2L, FDOM_DOMSUB, DOMSUB_FAPPLY_THM, IN_DELETE, FDOM_L2M, L2M_APPLY] THEN
    METIS_TAC [lemma1,pairTheory.PAIR, L2M_APPLY, uniql_def]);

(*****************************************************************************)
(* M2L_L2M_MAP_SETEQ:                                                        *)
(* `!l f g. ONE_ONE f ==>                                                    *)
(*          SETEQ (M2L (L2M (MAP (f ## g) l))) (MAP (f ## g) (M2L (L2M l)))` *)
(*****************************************************************************)

val M2L_L2M_MAP_SETEQ = store_thm("M2L_L2M_MAP_SETEQ",
    ``!l f g. ONE_ONE f ==> SETEQ (M2L (L2M (MAP (f ## g) l))) (MAP (f ## g) (M2L (L2M l)))``,
    RW_TAC std_ss [SETEQ_def] THEN EQ_TAC THEN Cases_on `x` THEN
    RW_TAC std_ss [pairTheory.PAIR_MAP, MEM_MAP,pairTheory.EXISTS_PROD, MEM_M2L,FDOM_L2M] THEN
    TRY (Q.EXISTS_TAC `p_1`) THEN RW_TAC std_ss [] THEN
    METIS_TAC [L2M_APPLY_MAP_EQ]);

(*****************************************************************************)
(*                                                                           *)
(*****************************************************************************)

val SORTSET_def = Define `SORTSET sort relation = sort relation o SET_TO_LIST o set`;
val SORTEDSET_def = Define `SORTEDSET r l = SORTED r l /\ ALL_DISTINCT l`;
val MAPSET_def = Define `MAPSET r l = SORTED r l /\ ALL_DISTINCT (MAP FST l)`;

local
val not = ``$~ : bool -> bool``;
in
val RFILTER_EQ_NIL = 
    CONJ (REWRITE_RULE [] (AP_TERM not (SPEC_ALL FILTER_NEQ_NIL)))
         (CONV_RULE (REWRITE_CONV [] THENC LAND_CONV SYM_CONV) (AP_TERM not (SPEC_ALL FILTER_NEQ_NIL)))
end

val ALL_DISTINCT_THM = ALL_DISTINCT_FILTER;

(*****************************************************************************)
(* PERM_S2L_L2S:                                                             *)
(* `!l. ALL_DISTINCT l ==> PERM (SET_TO_LIST (set l)) l`                     *)
(*****************************************************************************)

val ALL_DISTINCT_CONS = store_thm("ALL_DISTINCT_CONS",
    ``!l. ALL_DISTINCT (h::l) ==> ALL_DISTINCT l``,
    RW_TAC std_ss [ALL_DISTINCT_THM,FILTER,MEM] THEN
    PAT_ASSUM ``!y. P`` (MP_TAC o Q.SPEC `x`) THEN RW_TAC std_ss [FILTER_NEQ_NIL] THEN
    FIRST_ASSUM ACCEPT_TAC);

val IN_FILTER_SET = prove(``!x y. FINITE x /\ y IN x ==> (FILTER ($= y) (SET_TO_LIST x) = [y])``,
    GEN_TAC THEN completeInduct_on `CARD x` THEN
    RW_TAC std_ss [SET_TO_LIST_THM, FILTER, FINITE_EMPTY, CHOICE_DEF] THEN
    POP_ASSUM MP_TAC THEN RW_TAC std_ss [CHOICE_NOT_IN_REST, FINITE_REST, MEM_SET_TO_LIST, NOT_IN_EMPTY, RFILTER_EQ_NIL] THEN
    PAT_ASSUM ``!y. P`` (MATCH_MP_TAC o CONV_RULE (REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV)))) THEN
    Q.EXISTS_TAC `CARD (REST x)` THEN RW_TAC std_ss [FINITE_REST, REST_DEF, CARD_DELETE, CHOICE_DEF, IN_DELETE, GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,CARD_EQ_0]);

val NOT_IN_FILTER_SET = prove(``!x y. FINITE x /\ ~(y IN x) ==> (FILTER ($= y) (SET_TO_LIST x) = [])``,
    RW_TAC std_ss [REWRITE_RULE [] (AP_TERM ``$~:bool -> bool`` (SPEC_ALL FILTER_NEQ_NIL)), MEM_SET_TO_LIST]);

val FILTER_SET = store_thm("FILTER_SET",
    ``!x. FINITE x ==> (!y. FILTER ($= y) (SET_TO_LIST x) = if y IN x then [y] else [])``,
    METIS_TAC [IN_FILTER_SET, NOT_IN_FILTER_SET]);

val PERM_S2L_L2S = store_thm("PERM_S2L_L2S",
    ``!l. ALL_DISTINCT l ==> PERM (SET_TO_LIST (set l)) l``,
    REPEAT (RW_TAC std_ss [PERM_DEF, FILTER_SET, FINITE_LIST_TO_SET, RFILTER_EQ_NIL, IN_LIST_TO_SET, ALL_DISTINCT_THM]));

val NO_MEM_EMPTY = prove(``!l. (!x. ¬(MEM x l)) = (l = [])``,
    Induct THEN RW_TAC std_ss [MEM] THEN METIS_TAC []);

val SORTED_APPEND = prove(``!a b r. transitive r /\ SORTED r (a ++ b) ==> !x y. MEM x a /\ MEM y b ==> r x y``,
    Induct THEN METIS_TAC [APPEND,MEM,SORTED_EQ,MEM_APPEND]);

val MEM_PERM = store_thm("MEM_PERM", 
    ``!l1 l2. PERM l1 l2 ==> (!a. MEM a l1 = MEM a l2)``,
    METIS_TAC [Q.SPEC `$= a` MEM_FILTER, PERM_DEF]);

val PERM_SORTED_EQ = store_thm("PERM_SORTED_EQ",
    ``!l1 l2 r. (irreflexive r \/ antisymmetric r) /\ transitive r /\ PERM l1 l2 /\ SORTED r l1 /\ SORTED r l2 ==> (l1 = l2)``,
    REPEAT GEN_TAC THEN completeInduct_on `LENGTH l1 + LENGTH l2` THEN REPEAT Cases THEN REWRITE_TAC [LENGTH] THEN
    TRY (REWRITE_TAC [PERM_DEF, RFILTER_EQ_NIL, FILTER] THEN METIS_TAC [NOT_NIL_CONS]) THEN
    RW_TAC std_ss [NO_MEM_EMPTY] THEN
    `t' = t''` by IND_STEP_TAC THEN
    IMP_RES_TAC SORTED_EQ THEN RW_TAC arith_ss [] THEN
    FULL_SIMP_TAC std_ss [PERM_CONS_EQ_APPEND] THEN
    Cases_on `M` THEN FULL_SIMP_TAC std_ss [APPEND,list_11] THEN
    REPEAT (PAT_ASSUM ``a = b`` SUBST_ALL_TAC) THEN
    METIS_TAC [MEM_PERM, MEM, MEM_APPEND, SORTED_APPEND, 
    	       relationTheory.antisymmetric_def, relationTheory.irreflexive_def, relationTheory.transitive_def,
    	       PERM_FUN_APPEND_CONS, PERM_TRANS, PERM_SYM, APPEND]);

val SORTSET_SORTEDSET = store_thm("SORTSET_SORTEDSET",
    ``!l. transitive R /\ (irreflexive R \/ antisymmetric R) /\ SORTS sort R /\ SORTEDSET R l ==> (SORTSET sort R l = l)``,
    RW_TAC std_ss [SORTEDSET_def,SORTSET_def, SETEQ_def, SORTS_DEF] THEN
    `PERM (sort R (SET_TO_LIST (set l))) l` by METIS_TAC [PERM_SYM, PERM_TRANS, PERM_S2L_L2S] THEN
    METIS_TAC [PERM_SORTED_EQ]);

val ALL_DISTINCT_M2L = store_thm("ALL_DISTINCT_M2L",
    ``!s. ALL_DISTINCT (M2L s)``,
    completeInduct_on `FCARD s` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [M2L_def] THEN ONCE_REWRITE_TAC [fold_def] THEN
    NTAC 2 (RW_TAC std_ss [ALL_DISTINCT, GSYM M2L_def,MEM_M2L,FDOM_DOMSUB,IN_DELETE]) THEN
    IND_STEP_TAC THEN
    METIS_TAC [fcard_less, not_fempty_eq]);

val ALL_DISTINCT_MAPFST_M2L = store_thm("ALL_DISTINCT_MAPFST_M2L",
    ``!s. ALL_DISTINCT (MAP FST (M2L s))``,
    completeInduct_on `FCARD s` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [M2L_def] THEN ONCE_REWRITE_TAC [fold_def] THEN
    NTAC 2 (RW_TAC std_ss [ALL_DISTINCT, GSYM M2L_def,MEM_M2L,FDOM_DOMSUB,IN_DELETE,MAP,MEM_MAP]) THEN
    (IND_STEP_TAC ORELSE Cases_on `y` THEN RW_TAC std_ss [ALL_DISTINCT, GSYM M2L_def,MEM_M2L,FDOM_DOMSUB,IN_DELETE,MAP,MEM_MAP]) THEN
    METIS_TAC [fcard_less, not_fempty_eq]);

val PERM_DISTINCT = prove(``!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)``,
    METIS_TAC [MEM_PERM, PERM_DEF, ALL_DISTINCT_THM]);

val SORTSET_SORT = prove(``!l R. (antisymmetric R \/ irreflexive R) /\ transitive R /\ SORTS sort R /\ ALL_DISTINCT l ==> (SORTSET sort R l = sort R l)``,
    RW_TAC std_ss [SORTS_DEF,SORTSET_def] THEN
    `PERM l (sort R (SET_TO_LIST (set l)))` by METIS_TAC [PERM_S2L_L2S, PERM_DISTINCT, PERM_TRANS, PERM_SYM] THEN
    MATCH_MP_TAC PERM_SORTED_EQ THEN RW_TAC std_ss [] THEN
    Q.EXISTS_TAC `R` THEN RW_TAC std_ss [] THEN
    METIS_TAC [PERM_S2L_L2S, PERM_DISTINCT, PERM_TRANS, PERM_SYM]);

val PERM_S2L_L2S_EQ = prove(``!l1 l2. SETEQ l1 l2 ==> PERM (SET_TO_LIST (set l1)) (SET_TO_LIST (set l2))``,
    RW_TAC std_ss [PERM_DEF, FILTER_SET, FINITE_LIST_TO_SET,IN_LIST_TO_SET,SETEQ_def]);

val PERM_SETEQ = store_thm("PERM_SETEQ",
    ``!l1 l2. PERM l1 l2 ==> SETEQ l1 l2``,
    Induct THEN RW_TAC std_ss [PERM_CONS_EQ_APPEND, PERM_NIL,SETEQ_def] THEN
    Cases_on `x = h` THEN ASM_REWRITE_TAC [MEM, MEM_APPEND] THEN EQ_TAC THEN
    RES_TAC THEN FULL_SIMP_TAC std_ss [SETEQ_def, MEM_APPEND]);

val SETEQ_THM = store_thm("SETEQ_THM",
    ``!l1 l2. SETEQ l1 l2 = (set l1 = set l2)``,
    RW_TAC std_ss [pred_setTheory.EXTENSION, SETEQ_def, IN_LIST_TO_SET]);

val SORTSET_EQ = prove(``!l1 l2 R. SORTS sort R /\ (irreflexive R \/ antisymmetric R) /\ transitive R /\ SETEQ l1 l2 ==> (SORTSET sort R l1 = SORTSET sort R l2)``,
    RW_TAC std_ss [SORTSET_def, SORTS_DEF] THEN
    MATCH_MP_TAC PERM_SORTED_EQ THEN Q.EXISTS_TAC `R` THEN RW_TAC std_ss [] THEN
    METIS_TAC [PERM_S2L_L2S_EQ,PERM_TRANS,PERM_SYM, PERM_SETEQ]);

val MAPSET_IMP_SORTEDSET = prove(``!l R. transitive R ==> (MAPSET R l ==> SORTEDSET R l)``,
    Induct THEN RW_TAC std_ss [MAPSET_def, SORTEDSET_def, ALL_DISTINCT, MAP, MEM_MAP] THEN
    METIS_TAC [MAPSET_def, SORTEDSET_def, SORTED_EQ]);

val SORTED_CONS = store_thm("SORTED_CONS",
    ``!a b R. SORTED R (a::b) ==> SORTED R b``,
    GEN_TAC THEN Cases THEN RW_TAC std_ss [SORTED_DEF]);

val MAPSET_CONS = store_thm("MAPSET_CONS",
    ``!a b R. MAPSET R (a::b) ==> MAPSET R b``,
    RW_TAC std_ss [MAPSET_def, MAP, ALL_DISTINCT, SORTED_CONS] THEN
    METIS_TAC [SORTED_CONS]);

val MAPSET_UNIQ = store_thm("MAPSET_UNIQ",
    ``!a R. MAPSET R a ==> uniql a``,	
    Induct THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MAPSET_CONS THEN RES_TAC THEN
    FULL_SIMP_TAC std_ss [uniql_def, MEM, uniql_def, MAPSET_def, MAP, ALL_DISTINCT, MEM_MAP] THEN
    Cases_on `h` THEN RW_TAC std_ss [] THENL [
       PAT_ASSUM ``!y. P \/ Q`` (MP_TAC o Q.SPEC `(q,y')`),
       PAT_ASSUM ``!y. P \/ Q`` (MP_TAC o Q.SPEC `(q,y)`),
       ALL_TAC] THEN 
    ASM_REWRITE_TAC [] THEN METIS_TAC []);

val ALL_DISTINCT_MAPFST = store_thm("ALL_DISTINCT_MAPFST",
    ``!l. ALL_DISTINCT (MAP FST l) ==> ALL_DISTINCT l``,
    Induct THEN RW_TAC std_ss [ALL_DISTINCT,MAP,MEM_MAP] THEN
    METIS_TAC []);

val MAPSET_DISTINCT = store_thm("MAPSET_DISTINCT",
    ``MAPSET R x ==> ALL_DISTINCT x``,
    METIS_TAC [MAPSET_def,ALL_DISTINCT_MAPFST]);

val TOTAL_LEX = store_thm("TOTAL_LEX",``!R R'. total R /\ total R' ==> total (R LEX R')``,
    RW_TAC std_ss [pairTheory.LEX_DEF,relationTheory.total_def] THEN
    Cases_on `x` THEN Cases_on `y` THEN RW_TAC std_ss [] THEN
    METIS_TAC []);

val TRANSITIVE_LEX = store_thm("TRANSITIVE_LEX",
    ``!R R'. transitive R /\ transitive R' ==> transitive (R LEX R')``,
    RW_TAC std_ss [pairTheory.LEX_DEF,relationTheory.transitive_def] THEN
    Cases_on `x` THEN Cases_on `y` THEN Cases_on `z` THEN RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC []);

val SORTED_LEX = store_thm("SORTED_LEX",
    ``!R1 R2. total R1 /\ transitive R1 /\ transitive R2 ==> !x. SORTED (R1 LEX R2) x ==> SORTED R1 (MAP FST x)``,
    NTAC 3 STRIP_TAC THEN Induct THEN TRY Cases THEN RW_TAC std_ss [SORTED_EQ,MAP,SORTED_DEF,TRANSITIVE_LEX,MEM_MAP,pairTheory.LEX_DEF] THEN
    RES_TAC THEN Cases_on `y'` THEN FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC [relationTheory.transitive_def, relationTheory.total_def]);

val filter_first = prove(``!l x y. (FILTER ($= x) (MAP FST l) = [x]) /\ (x = FST y) /\ MEM y l ==> (FILTER ($= x o FST) l = [y])``,
    Induct THEN RW_TAC std_ss [FILTER,MEM,RFILTER_EQ_NIL] THEN
    FULL_SIMP_TAC std_ss [MAP,FILTER,list_11,RFILTER_EQ_NIL, MEM_MAP] THEN
    FIRST [PAT_ASSUM ``a = b`` MP_TAC, METIS_TAC []] THEN
    RW_TAC std_ss [RFILTER_EQ_NIL, MEM_MAP] THEN METIS_TAC []);

val MAP_FST_DISTINCT_EQ = store_thm("MAP_FIRST_DISTINCT_EQ",
    ``!l1 l2. (MAP FST l1 = MAP FST l2) /\ ALL_DISTINCT (MAP FST l1) /\ PERM l1 l2 ==> (l1 = l2)``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_EQ THEN RW_TAC std_ss [PERM_LENGTH,pairTheory.PAIR_FST_SND_EQ] THEN
    `FST (EL x l1) = FST (EL x l2)` by METIS_TAC [EL_MAP, PERM_LENGTH] THEN
    FULL_SIMP_TAC std_ss [ALL_DISTINCT_FILTER] THEN
    `MEM (FST (EL x l2)) (MAP FST l2) /\ MEM (FST (EL x l1)) (MAP FST l1)` by METIS_TAC [MEM_MAP, rich_listTheory.EL_IS_EL,PERM_LENGTH] THEN
    MAP_EVERY (fn x => x by (MATCH_MP_TAC filter_first THEN METIS_TAC [filter_first, rich_listTheory.EL_IS_EL, PERM_LENGTH, MEM_PERM])) [
         `FILTER ($= (FST (EL x l2)) o FST) l2 = [EL x l2]`,
         `FILTER ($= (FST (EL x l2)) o FST) l2 = [EL x l1]`] THEN
    METIS_TAC [pairTheory.PAIR,list_11]);


val SETEQ_PERM = store_thm("SETEQ_PERM",
    ``!l1 l2. SETEQ l1 l2 /\ ALL_DISTINCT l1 /\ ALL_DISTINCT l2 ==> PERM l1 l2``,
    RW_TAC std_ss [SETEQ_def, ALL_DISTINCT_FILTER, PERM_DEF] THEN
    Cases_on `MEM x l1` THEN1 METIS_TAC [FILTER_NEQ_NIL] THEN
    MAP_EVERY (fn x => x by RW_TAC std_ss [RFILTER_EQ_NIL])
         [`FILTER ($= x) l1 = []`, `FILTER ($= x) l2 = []`] THEN
    METIS_TAC []);

(*****************************************************************************)
(* M2L_L2M:                                                                  *)
(*`!R R' sort. total R /\ transitive R /\ transitive R' /\ antisymmetric R   *)
(*               /\ SORTS sort (R LEX R')                                    *)
(*               ==> !l. MAPSET (R LEX R') l                                 *)
(*                       ==> (sort (R LEX R') (M2L (L2M l)) = l)`            *)
(*****************************************************************************)

val M2L_L2M = store_thm("M2L_L2M", 
    ``!sort R R'. total R /\ antisymmetric R /\ transitive R /\ transitive R' /\ 
                    SORTS sort (R LEX R') ==> !l. MAPSET (R LEX R') l 
                    ==> (sort (R LEX R') (M2L (L2M l)) = l)``,
    REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MAP_FST_DISTINCT_EQ THEN
    IMP_RES_TAC MAPSET_def THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [SORTS_DEF] THEN
    TRY (
        MATCH_MP_TAC PERM_SORTED_EQ THEN Q.EXISTS_TAC `R` THEN REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC (PULL_RULE SORTED_LEX) THEN METIS_TAC []) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PERM_MAP) THEN
    MATCH_MP_TAC SETEQ_PERM THEN
    RW_TAC std_ss [ALL_DISTINCT_MAPFST] THEN 
    REPEAT (MAP_FIRST MATCH_MP_TAC [PERM_SETEQ, PERM_TRANS]) THEN
    TRY (Q.EXISTS_TAC `M2L (L2M l)`) THEN RW_TAC std_ss [] THEN
    TRY (MATCH_MP_TAC SETEQ_PERM) THEN 
    METIS_TAC [M2L_L2M_SETEQ, MAPSET_UNIQ, ALL_DISTINCT_PERM, ALL_DISTINCT_M2L, ALL_DISTINCT_MAPFST]);   

(*****************************************************************************)
(* Other ordering theorems....                                               *)
(*****************************************************************************)

val TRANS_INV = store_thm("TRANS_INV",
    ``!R f. transitive R ==> transitive (inv_image R f)``,
    RW_TAC std_ss [relationTheory.transitive_def,relationTheory.inv_image_def] THEN
    METIS_TAC []);

val TOTAL_INV = store_thm("TOTAL_INV",
    ``!R f. total R ==> total (inv_image R f)``,
    RW_TAC std_ss [relationTheory.total_def,relationTheory.inv_image_def] THEN
    METIS_TAC []);    

val IRREFL_INV = store_thm("IRREFL_INV",
    ``!R f. irreflexive R ==> irreflexive (inv_image R f)``,
    RW_TAC std_ss [relationTheory.irreflexive_def,relationTheory.inv_image_def] THEN
    METIS_TAC []);

val ANTISYM_INV = store_thm("ANTISYM_INV",
    ``!R f. ONE_ONE f /\ antisymmetric R ==> antisymmetric (inv_image R f)``,
    RW_TAC std_ss [relationTheory.antisymmetric_def,relationTheory.inv_image_def, ONE_ONE_DEF]);

val COM_LT_TRANS = prove(``!a b c. a < b /\ b < c ==> a < c : complex_rational``,
    REPEAT Cases THEN RW_TAC std_ss [complex_rationalTheory.COMPLEX_LT_def] THEN
    METIS_TAC [ratTheory.RAT_LES_TRANS]);

val COM_LT_REFL = prove(``!a. ~(a < a : complex_rational)``,
    REPEAT Cases THEN RW_TAC std_ss [complex_rationalTheory.COMPLEX_LT_def] THEN
    METIS_TAC [ratTheory.RAT_LES_REF]);

val COM_LT_TOTAL = prove(``!a b. a < b \/ b < a \/ (a = b : complex_rational)``,
    REPEAT Cases THEN RW_TAC std_ss [complex_rationalTheory.COMPLEX_LT_def] THEN
    METIS_TAC [ratTheory.RAT_LES_TOTAL]);

(*****************************************************************************)
(* SEXP Ordering theorems                                                    *)
(*****************************************************************************)

val SEXP_LE_def = Define `SEXP_LE a b = |= lexorder a b`;

val _ = overload_on ("<=", ``SEXP_LE``);

val lexorder_def = hol_defaxiomsTheory.lexorder_def;

val sym_rwr = prove(``
    (!a b c. lexorder (sym a b) (chr c) = nil) /\ 
    (!a b c d. lexorder (sym a b) (cons c d) = t) /\  
    (!a b c. lexorder (sym a b) (str c) = nil) /\
    (!a b c. lexorder (chr a) (sym b c) = t) /\ 
    (!a b c d. lexorder (cons a b) (sym c d) = nil) /\  
    (!a b c. lexorder (str a) (sym b c) = t)``,
    ONCE_REWRITE_TAC [lexorder_def] THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def]);

val bool_rwr = prove(``!a. bool a = if a then t else nil``,Cases THEN RW_TAC std_ss [translateTheory.bool_def]);

val sexp_str_lt_l1 = prove(``!a b c. (string_less_l (list_to_sexp chr (EXPLODE a)) (list_to_sexp chr (EXPLODE b)) (int c) = nil) = ~STRING_LESS a b``,
    Induct THEN (GEN_TAC THEN Cases ORELSE Cases) THEN
    ONCE_REWRITE_TAC [hol_defaxiomsTheory.string_less_l_def] THEN
    RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def, sexpTheory.coerce_string_to_list_def, 
                  stringTheory.EXPLODE_def, sexpTheory.list_to_sexp_def, 
                  sexpTheory.STRING_LESS_IRREFLEXIVE, GSYM translateTheory.INT_LT, integerTheory.INT_LT_CALCULATE,
                  bool_rwr, sexpTheory.STRING_LESS_def, sexpTheory.LIST_LEX_ORDER_def, MAP, stringTheory.ORD_11, sexpTheory.cpx_def] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS] THEN
    FULL_SIMP_TAC std_ss [GSYM sexpTheory.cpx_def, translateTheory.COM_THMS, GSYM sexpTheory.int_def, GSYM translateTheory.INT_THMS,integerTheory.INT_ADD_REDUCE, sexpTheory.STRING_LESS_def] THEN
    RW_TAC std_ss [sexpTheory.int_def,sexpTheory.cpx_def]);

val len_not_nil = prove(``!a. ~(len a = nil)``,
     Cases THEN ONCE_REWRITE_TAC [hol_defaxiomsTheory.len_def] THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.nat_def, sexpTheory.int_def, sexpTheory.cpx_def] THEN
     Cases_on `len s0` THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.nat_def, sexpTheory.int_def]);

val lexorder_str_string = prove(``!a b. lexorder (str a) (str b) = if STRING_LESS_EQ a b then t else nil``,
    ONCE_REWRITE_TAC [lexorder_def] THEN 
    RW_TAC std_ss [sexpTheory.coerce_string_to_list_def, hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def] THEN
    REPEAT (CHANGED_TAC (REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [sexpTheory.COMMON_LISP_def,sexpTheory.csym_def, sexpTheory.STRING_LESS_IRREFLEXIVE])) THEN
    FULL_SIMP_TAC std_ss [sexp_str_lt_l1, GSYM sexpTheory.int_def, GSYM sexpTheory.nil_def] THEN
    METIS_TAC [sexpTheory.STRING_LESS_TRICHOTOMY, sexpTheory.STRING_LESS_IRREFLEXIVE, sexpTheory.STRING_LESS_TRANS, sexpTheory.STRING_LESS_EQ_def, len_not_nil]);

val lexorder_char = prove(``!a b. lexorder (chr a) (chr b) = if ORD a <= ORD b then t else nil``,
    ONCE_REWRITE_TAC [lexorder_def] THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def] THEN
    REPEAT (CHANGED_TAC (REPEAT (POP_ASSUM MP_TAC) THEN 
            RW_TAC std_ss [GSYM translateTheory.INT_THMS, translateTheory.bool_def, integerTheory.INT_GT_CALCULATE, integerTheory.INT_LT_CALCULATE, hol_defaxiomsTheory.ACL2_SIMPS, bool_rwr])) THEN
    FULL_SIMP_TAC std_ss [GSYM stringTheory.ORD_11] THEN 
    DECIDE_TAC);

val string_less_l_nil = prove(``!a b. string_less_l (str a) (str b) (int 0) = nil``,
    ONCE_REWRITE_TAC [hol_defaxiomsTheory.string_less_l_def] THEN
    RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def, sexpTheory.coerce_string_to_list_def, 
                  stringTheory.EXPLODE_def, sexpTheory.list_to_sexp_def, 
                  sexpTheory.STRING_LESS_IRREFLEXIVE, GSYM translateTheory.INT_LT, integerTheory.INT_LT_CALCULATE,
                  bool_rwr, sexpTheory.STRING_LESS_def, sexpTheory.LIST_LEX_ORDER_def, MAP, stringTheory.ORD_11, sexpTheory.cpx_def]);

val lexorder_sym = prove(``lexorder (sym a b) (sym c d) =
    if ~(a = "") /\ (BASIC_INTERN b a = sym a b) 
       then if ~(c = "") /\ (BASIC_INTERN d c = sym c d)
               then if STRING_LESS b d \/ (b = d) /\ STRING_LESS_EQ a c then t else nil
 	       else t
       else if ~(c = "") /\ (BASIC_INTERN d c = sym c d)
       	       then nil
	       else if STRING_LESS a c \/ (a = c) /\ STRING_LESS_EQ b d then t else nil``,
    ONCE_REWRITE_TAC [lexorder_def] THEN 
    REWRITE_TAC [sexpTheory.coerce_string_to_list_def, hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def, hol_defaxiomsTheory.ACL2_SIMPS,
                sexpTheory.SEXP_SYM_LESS_EQ_def,sexpTheory.SEXP_SYM_LESS_def] THEN
    REPEAT (CHANGED_TAC (REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC (std_ss ++ boolSimps.LET_ss) 
    	   [GSYM sexpTheory.int_def, hol_defaxiomsTheory.ACL2_SIMPS,sexpTheory.coerce_string_to_list_def, REWRITE_RULE [sexpTheory.nil_def] sexp_str_lt_l1, string_less_l_nil, sexpTheory.COMMON_LISP_def])) THEN
    TRY (METIS_TAC [sexpTheory.STRING_LESS_TRANS, sexpTheory.STRING_LESS_TRANS_NOT, sexpTheory.STRING_LESS_EQ_TRANS, sexpTheory.STRING_LESS_EQ_def, sexpTheory.STRING_LESS_EQ_ANTISYM, sexpTheory.STRING_LESS_IRREFLEXIVE]));


val vars1 = [``num (com a b)``, ``sym a b``, ``str a``, ``chr a``, ``cons a b``];
val vars2 = [``num (com c d)``, ``sym c d``, ``str c``, ``chr c``, ``cons c d``];

val lexorder_terms = flatten (map (fn y => (map (fn x => mk_comb(mk_comb(``lexorder``, x), y)) vars1)) vars2);
val lexorder_thms = map (REWRITE_CONV [lexorder_str_string, lexorder_char, lexorder_sym] THENC ONCE_REWRITE_CONV [lexorder_def] THENC 
                         REWRITE_CONV [hol_defaxiomsTheory.ACL2_SIMPS,sexpTheory.itel_def, sym_rwr,
    		       	               sexpTheory.SEXP_SYM_LESS_EQ_def, sexpTheory.SEXP_SYM_LESS_def]) lexorder_terms;

val SEXP_LE_RWRS = LIST_CONJ (hol_defaxiomsTheory.ACL2_SIMPS::bool_rwr::
                              METIS_PROVE [] ``((if a then b else c) = d) = (a /\ (b = d) \/ ~a /\ (c = d))``::lexorder_thms);

fun ALL_CASES f (a,g) =
let val v = filter (fn x => f x handle _ => false) (free_vars g)    
in  (NTAC (length a) (POP_ASSUM MP_TAC) THEN 
     MAP_EVERY (fn b => SPEC_TAC (b,b)) v THEN
     REPEAT Cases THEN
     NTAC (length a) DISCH_TAC) (a,g)
end;

val SEXP_LE = REWRITE_RULE [hol_defaxiomsTheory.ACL2_SIMPS] SEXP_LE_def;

fun rattac (a,goal) =
let val rats = filter (curry op= ``:rat`` o type_of) (free_vars goal)
    val zrats = filter (mem #"0" o explode o fst o dest_var) rats
in
    (MAP_EVERY (fn x => STRIP_ASSUME_TAC (SPEC (mk_eq(x, ``rat_0``)) EXCLUDED_MIDDLE)) zrats) (a,goal)
end;

fun droptac (a,goal) = 
    (if free_in ``lexorder s0 s0'`` goal
       then ALL_TAC
       else REPEAT (POP_ASSUM (K ALL_TAC))) (a,goal);

val SEXP_LE_ANTISYMMETRIC = time store_thm("SEXP_LE_ANTISYMMETRIC",
    ``antisymmetric SEXP_LE``,
    REWRITE_TAC [relationTheory.antisymmetric_def, SEXP_LE] THEN
    completeInduct_on `sexp_size x + sexp_size y` THEN 
    REPEAT Cases THEN ALL_CASES (curry op= ``:complex_rational`` o type_of) THEN
    REWRITE_TAC [SEXP_LE_RWRS, sexpTheory.sexp_size_def, complex_rationalTheory.complex_rational_11, DE_MORGAN_THM] THEN
    STRIP_TAC THEN droptac THEN TRY STRIP_TAC THEN
    PROVE_TAC [
        sexpTheory.STRING_LESS_EQ_SYM, sexpTheory.STRING_LESS_IRREFLEXIVE, sexpTheory.STRING_LESS_SYM,
        stringTheory.ORD_11, arithmeticTheory.LESS_EQUAL_ANTISYM,
        ratTheory.RAT_LEQ_ANTISYM, ratTheory.RAT_LEQ_LES, ratTheory.RAT_LES_ANTISYM,
        DECIDE ``a + b < 1n + (a + a') + (1 + (b + b'))``,
        DECIDE ``a' + b' < 1n + (a + a') + (1 + (b + b'))``]);

val sexp_le_antirewrite = REWRITE_RULE [hol_defaxiomsTheory.ACL2_SIMPS,relationTheory.antisymmetric_def,SEXP_LE_def] SEXP_LE_ANTISYMMETRIC;

val SEXP_LE_TRANSITIVE = time store_thm ("SEXP_LE_TRANSITIVE",
    ``transitive SEXP_LE``,
    REWRITE_TAC [relationTheory.transitive_def, SEXP_LE] THEN
    completeInduct_on `sexp_size x + sexp_size y + sexp_size z` THEN 
    REPEAT Cases THEN ALL_CASES (curry op= ``:complex_rational`` o type_of) THEN
    REWRITE_TAC [SEXP_LE_RWRS, sexpTheory.sexp_size_def, complex_rationalTheory.complex_rational_11, DE_MORGAN_THM] THEN
    STRIP_TAC THEN droptac THEN rattac THEN ASM_REWRITE_TAC [] THEN TRY STRIP_TAC THEN
    PROVE_TAC [sexpTheory.STRING_LESS_EQ_def, sexpTheory.STRING_LESS_TRANS, sexpTheory.STRING_LESS_EQ_TRANS,
              ratTheory.RAT_LES_TRANS, ratTheory.RAT_LES_REF, ratTheory.RAT_LEQ_TRANS, ratTheory.RAT_LEQ_LES,
              arithmeticTheory.LESS_TRANS, arithmeticTheory.LESS_EQ_TRANS,
              sexp_le_antirewrite,
              DECIDE ``a + b + c < 1n + (a + a') + (1 + (b + b')) + (1 + (c + c'))``, 
              DECIDE ``a' + b' + c' < 1n + (a + a') + (1 + (b + b')) + (1 + (c + c'))``, sexpTheory.sexp_distinct]);

val SEXP_LE_TOTAL = store_thm("SEXP_LE_TOTAL", ``total SEXP_LE``,
    REWRITE_TAC [relationTheory.total_def, SEXP_LE_def, hol_defaxiomsTheory.ACL2_SIMPS] THEN
    completeInduct_on `sexp_size x + sexp_size y` THEN 
    REPEAT Cases THEN ALL_CASES (curry op= ``:complex_rational`` o type_of) THEN
    REWRITE_TAC [SEXP_LE_RWRS, sexpTheory.sexp_size_def, DE_MORGAN_THM] THEN
    METIS_TAC [ratTheory.RAT_LEQ_LES,ratTheory.rat_leq_def, sexpTheory.STRING_LESS_TRICHOTOMY, arithmeticTheory.LESS_CASES, 
               arithmeticTheory.LESS_OR_EQ,stringTheory.ORD_11, ratTheory.RAT_LES_TOTAL, sexpTheory.STRING_LESS_EQ_def,
               DECIDE ``a + c < 1n + (a + b) + (1 + (c + d))``, DECIDE ``b + d < 1n + (a + b) + (1 + (c + d))``]);

val SEXP_LT_def = Define `SEXP_LT a b = ~(a = b) /\ SEXP_LE a b`;

val _ = overload_on ("<", ``SEXP_LT``);

val SEXP_LT_IRREFLEXIVE = store_thm("SEXP_LT_IRREFLEXIVE",
    ``irreflexive SEXP_LT``,
    METIS_TAC [SEXP_LT_def, relationTheory.irreflexive_def]);

val SEXP_LT_TRANSITIVE = store_thm("SEXP_LT_TRANSITIVE",
    ``transitive SEXP_LT``,
    REWRITE_TAC [relationTheory.transitive_def, SEXP_LT_def] THEN
    METIS_TAC (map (REWRITE_RULE [relationTheory.transitive_def,relationTheory.antisymmetric_def])
                    [SEXP_LE_TRANSITIVE, SEXP_LE_ANTISYMMETRIC]));

val TOTAL_K = store_thm("TOTAL_K",
    ``total (K (K T))``, RW_TAC std_ss [relationTheory.total_def]);

val TRANSITIVE_K = store_thm("TRANSITIVE_K",
    ``transitive (K (K T))``, RW_TAC std_ss [relationTheory.transitive_def]);

(*****************************************************************************)
(* Encoding definitions                                                      *)
(*****************************************************************************)

val map_fmap_def = Define `map_fmap m1 m2 = L2M o MAP (m1 ## m2) o M2L`;

val all_fmap_def = Define `all_fmap p1 p2 = EVERY (all_pair p1 p2) o M2L`;

val fix_fmap_def = Define `fix_fmap f1 f2 = list (pair I I) o  
    		   	  	    QSORT3 ($<= LEX (K (K T))) o M2L o L2M o sexp_to_list (sexp_to_pair I I) o fix_list (fix_pair f1 f2)`;

val encode_fmap_def = Define `encode_fmap fenc tenc = list (pair fenc tenc) o QSORT3 ((inv_image $<= fenc) LEX (K (K T))) o M2L`;

val decode_fmap_def = Define `decode_fmap fdec tdec = L2M o sexp_to_list (sexp_to_pair fdec tdec)`;

val detect_fmap_def = Define `detect_fmap fdet tdet x = 
    		      	     		  (MAPSET ($<= LEX (K (K T))) o sexp_to_list (sexp_to_pair I I)) x /\ 
					  (listp (pairp fdet tdet) x)`;

(*****************************************************************************)
(* Encoding proofs                                                           *)
(*****************************************************************************)

val o_split = prove(``((a o sexp_to_list f) o list g = a o (sexp_to_list f o list g)) /\
                      (sexp_to_list f o (list g o b) = (sexp_to_list f o list g) o b)``,
    METIS_TAC [combinTheory.o_DEF]);

val UNIQL_MAP = store_thm("UNIQL_MAP", ``!f g l. ONE_ONE f /\ uniql l ==> uniql (MAP (f ## g) l)``,
    RW_TAC std_ss [uniql_def,MAP,MEM,pairTheory.PAIR_MAP,MEM_MAP,ONE_ONE_THM] THEN
    METIS_TAC [pairTheory.PAIR]);

val PERM_UNIQL = store_thm("PERM_UNIQL", ``!l1 l2. PERM l1 l2 ==> (uniql l1 = uniql l2)``,
    RW_TAC std_ss [uniql_def,MAP,MEM,ONE_ONE_THM] THEN
    METIS_TAC [pairTheory.PAIR, MEM_PERM]);

val ONE_ONE_RING = store_thm("ONE_ONE_RING",
    ``!f g. ONE_ONE (f o g) ==> ONE_ONE g``,
    RW_TAC std_ss [ONE_ONE_DEF]);

val ONE_ONE_I = store_thm("ONE_ONE_I",
    ``ONE_ONE I``, RW_TAC std_ss [ONE_ONE_DEF]);

val o_assoc = prove(
    ``(f o g) o h = f o g o h``, METIS_TAC [combinTheory.o_DEF]);

(*****************************************************************************)
(* ENCDECMAP_FMAP: encode then decode equals map                             *)
(*****************************************************************************)

val ENCDECMAP_FMAP = store_thm("ENCDECMAP_FMAP", 
    ``!fdec tdec fenc tenc. ONE_ONE (fdec o fenc) ==> (decode_fmap fdec tdec o encode_fmap fenc tenc = map_fmap (fdec o fenc) (tdec o tenc))``,
    REWRITE_TAC [decode_fmap_def, encode_fmap_def, o_assoc, map_fmap_def] THEN
    REWRITE_TAC [o_split, translateTheory.ENCDECMAP_LIST, combinTheory.I_o_ID, quotient_listTheory.LIST_MAP_I, translateTheory.ENCDECMAP_PAIR] THEN
    RW_TAC std_ss [FUN_EQ_THM] THEN
    MATCH_MP_TAC L2M_EQ THEN REPEAT CONJ_TAC THEN
    METIS_TAC [L2M_EQ, UNIQL_MAP, PERM_MAP, PERM_UNIQL, UNIQL_M2L, PERM_QSORT3, UNIQL_MAP, PERM_SETEQ, SETEQ_THM, PERM_SYM]);

(*****************************************************************************)
(* DECENCFIX_FMAP: decode then encode equals fix                             *)
(*****************************************************************************)

val RWR = REWRITE_RULE [FUN_EQ_THM, combinTheory.o_THM];

val map_lemma = prove(``!l f g. MAP FST (MAP (f ## g) l) = MAP f (MAP FST l)``,
    Induct THEN RW_TAC std_ss [MAP, pairTheory.PAIR_MAP]);

val map_eq_sing = prove(``!l f x. (MAP f l = [x]) = ?h. (l = [h]) /\ (x = f h)``,
    Induct THEN RW_TAC std_ss [MAP, MAP_EQ_NIL] THEN PROVE_TAC []);

val one_one_lemma = prove(``!f. ONE_ONE f ==> !y. $= (f y) o f = $= y``,
    RW_TAC std_ss [ONE_ONE_THM,FUN_EQ_THM] THEN METIS_TAC []);

val ALL_DISTINCT_MAP = store_thm("ALL_DISTINCT_MAP",
    ``!l f. ONE_ONE f /\ ALL_DISTINCT l ==> ALL_DISTINCT (MAP f l)``,
    NTAC 2 (RW_TAC std_ss [ALL_DISTINCT_FILTER, rich_listTheory.FILTER_MAP, map_eq_sing, MEM_MAP, one_one_lemma]));

val M2L_L2M_MAP = store_thm("M2L_L2M_MAP",
    ``!l f g. ONE_ONE f ==> PERM (M2L (L2M (MAP (f ## g) l))) (MAP (f ## g) (M2L (L2M l)))``,
    METIS_TAC [ALL_DISTINCT_MAPFST_M2L,ALL_DISTINCT_MAP, map_lemma, ALL_DISTINCT_MAPFST, SETEQ_PERM, M2L_L2M_MAP_SETEQ, ALL_DISTINCT_M2L]);

val QSORT3_M2L_L2M_MAP = store_thm("QSORT3_M2L_L2M_MAP", 
    ``!l f g. ONE_ONE f ==> (QSORT3 ($<= LEX K (K T)) (M2L (L2M (MAP (f ## g) l))) = QSORT3 ($<= LEX (K (K T))) (MAP (f ## g) (M2L (L2M l))))``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_FST_DISTINCT_EQ THEN
    REPEAT CONJ_TAC THEN
    TRY (MATCH_MP_TAC PERM_SORTED_EQ) THEN
    TRY (Q.EXISTS_TAC `$<=`) THEN
    METIS_TAC [M2L_L2M_MAP, PERM_QSORT3, PERM_TRANS,PERM_SYM, PERM_MAP, QSORT3_SORTS, SEXP_LE_TOTAL, 
               SEXP_LE_TRANSITIVE, TRANSITIVE_K, TOTAL_K, TRANSITIVE_LEX, TOTAL_LEX, SORTS_DEF, SORTED_LEX, 
               SEXP_LE_ANTISYMMETRIC, ALL_DISTINCT_PERM, ALL_DISTINCT_MAPFST_M2L]);

val MAP_EQ_LENGTH = store_thm("MAP_EQ_LENGTH",
    ``!l1 l2. (MAP f l1 = MAP g l2) ==> (LENGTH l1 = LENGTH l2)``,
    METIS_TAC [LENGTH_MAP]);

val MEM_EL_FILTER = store_thm("MEM_EL_FILTER", 
    ``!f l x. MEM x l ==> ?y. y < LENGTH (FILTER ($= (f x) o f) l) /\ (EL y (FILTER ($= (f x) o f) l) = x)``,
    GEN_TAC THEN Induct THEN RW_TAC std_ss [FILTER, rich_listTheory.EL_CONS, MEM] THEN RES_TAC THENL [
       Q.EXISTS_TAC `0`, Q.EXISTS_TAC `SUC y`,ALL_TAC] THEN 
    RW_TAC arith_ss [LENGTH,EL,HD,TL] THEN
    METIS_TAC []);

val EL_MAP_FILTER = store_thm("EL_MAP_FITLE",
    ``!f x. (MAP f l1 = MAP f l2) /\ x < LENGTH l1 /\ (FILTER ($= (f (EL x l1)) o f) l1 = FILTER ($= (f (EL x l2)) o f) l2) ==> (EL x l1 = EL x l2)``,
    completeInduct_on `LENGTH l1 + LENGTH l2` THEN REPEAT Cases THEN 
    RW_TAC std_ss [LENGTH, rich_listTheory.EL_CONS, MEM, MAP, FILTER] THEN
    Cases_on `x` THEN FULL_SIMP_TAC std_ss [rich_listTheory.EL_CONS, EL, HD, TL, list_11] THEN 
    POP_ASSUM MP_TAC THEN RW_TAC std_ss [list_11] THEN
    IND_STEP_TAC THEN RW_TAC std_ss [] THEN Q.EXISTS_TAC `f` THEN RW_TAC arith_ss [] THEN METIS_TAC [EL_MAP, LENGTH_MAP]);

val MAP_FST_SND_EQ = store_thm("MAP_FST_SND_EQ",
    ``!l1 l2. (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)``,
    REPEAT GEN_TAC THEN completeInduct_on `LENGTH l1 + LENGTH l2` THEN REPEAT Cases THEN 
    RW_TAC std_ss [LENGTH, rich_listTheory.EL_CONS, MEM, MAP, FILTER, pairTheory.PAIR_FST_SND_EQ] THEN
    IND_STEP_TAC THEN RW_TAC arith_ss []);

val STABLE_FST_EQ = store_thm("STABLE_FST_EQ", 
    ``!l1 l2. (MAP FST l1 = MAP FST l2) /\ (!x. FILTER ($= x o FST) l1 = FILTER ($= x o FST) l2) ==> (l1 = l2)``,
    METIS_TAC [EL_MAP_FILTER, EL_MAP, LENGTH_MAP, LIST_EQ_REWRITE,MAP_FST_SND_EQ]);

val SORTED_MAP = store_thm("SORTED_MAP",
    ``!l f R. transitive R /\ SORTED (inv_image R f) l ==> SORTED R (MAP f l)``,
    Induct THEN RW_TAC std_ss [SORTED_EQ,SORTED_DEF,MAP,MEM_MAP] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [SORTED_EQ, TRANS_INV, relationTheory.inv_image_def]);

local
val lemma 
    = GSYM (GEN_ALL (PULL_RULE (DISCH_ALL (CONJUNCT2 (UNDISCH (SPEC_ALL (PULL_RULE (REWRITE_RULE [STABLE_DEF] QSORT3_STABLE))))))));
val sorttac 
    = RW_TAC std_ss [map_lemma, TRANSITIVE_K, SEXP_LE_ANTISYMMETRIC, SEXP_LE_TRANSITIVE, SEXP_LE_TOTAL, 
                     REWRITE_RULE [SORTS_DEF] QSORT3_SORTS, TOTAL_K, TOTAL_LEX, TRANSITIVE_LEX, TOTAL_INV, TRANS_INV]
in
val QSORT3_PAIRMAP = store_thm("QSORT3_PAIRMAP",
    ``!f. ONE_ONE f ==> !l g. QSORT3 ($<= LEX K (K T)) (MAP (f ## g) l) = MAP (f ## g) (QSORT3 (inv_image $<= f LEX K (K T)) l)``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STABLE_FST_EQ THEN REPEAT STRIP_TAC THENL [
       MATCH_MP_TAC PERM_SORTED_EQ THEN
       Q.EXISTS_TAC `$<=` THEN sorttac,
       MATCH_MP_TAC EQ_TRANS THEN 
       Q.EXISTS_TAC `FILTER ($= x o FST) (MAP (f ## g) l)` THEN CONJ_TAC
    ] THEN1 METIS_TAC [PERM_QSORT3, PERM_MAP, PERM_SYM, PERM_TRANS, map_lemma] THEN
    REPEAT (FIRST [MATCH_MP_TAC (PULL_RULE SORTED_LEX) ORELSE MATCH_MP_TAC SORTED_MAP THEN RW_TAC std_ss [SEXP_LE_TRANSITIVE],
            MATCH_MP_TAC lemma ORELSE MATCH_MP_TAC (GSYM lemma) ORELSE (REWRITE_TAC [rich_listTheory.FILTER_MAP] THEN AP_TERM_TAC)]) THEN
    TRY (Q.EXISTS_TAC `K (K T)`) THEN sorttac THEN
    REPEAT (POP_ASSUM MP_TAC) THEN (fn (a,g) => MAP_EVERY (fn b => SPEC_TAC (b,b)) (free_vars g) (a,g)) THEN
    REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [pairTheory.LEX_DEF,relationTheory.inv_image_def, ONE_ONE_DEF])
end;

val list_pair_map = prove(``!f g f' g' l. list (pair f g) (MAP (f' ## g') l) = list (pair (f o f') (g o g')) l``,
    NTAC 4 GEN_TAC THEN Induct THEN RW_TAC std_ss [translateTheory.list_def, translateTheory.pair_def, MAP, pairTheory.PAIR_MAP]);

(*****************************************************************************)
(* DECENCFIX_FMAP: Decode then encode is fix.                                *)
(*****************************************************************************)

val DECENCFIX_FMAP = store_thm("DECENCFIX_FMAP",
    ``!fdec tdec fenc tenc. ONE_ONE (fdec o fenc) ==> (encode_fmap fenc tenc o decode_fmap fdec tdec = fix_fmap (fenc o fdec) (tenc o tdec))``,
    RW_TAC std_ss [encode_fmap_def,decode_fmap_def,fix_fmap_def,FUN_EQ_THM,GSYM translateTheory.DECENCFIX_LIST,GSYM translateTheory.DECENCFIX_PAIR,
                  RWR translateTheory.ENCDECMAP_LIST, translateTheory.ENCDECMAP_PAIR] THEN
    IMP_RES_TAC ONE_ONE_RING THEN
    RW_TAC std_ss [QSORT3_M2L_L2M_MAP, QSORT3_PAIRMAP, list_pair_map]);

(*****************************************************************************)
(* MAPID_FMAP: Map identity.                                                 *)
(*****************************************************************************)

val MAPID_FMAP = store_thm("MAPID_FMAP", 
    ``map_fmap I I = I``,
    RW_TAC std_ss [FUN_EQ_THM, map_fmap_def, quotient_pairTheory.PAIR_MAP_I,quotient_listTheory.LIST_MAP_I, L2M_M2L]);

(*****************************************************************************)
(* FIXID_FMAP: Fix identity.                                                 *)
(*****************************************************************************)

val FIXID_FMAP = store_thm("FIXID_FMAP",
    ``(!x. p0 x ==> (f0 x = x)) ∧ (!x. p1 x ==> (f1 x = x)) ==> !x. detect_fmap p0 p1 x ⇒ (fix_fmap f0 f1 x = x)``,
    RW_TAC std_ss [fix_fmap_def, detect_fmap_def, translateTheory.FIXID_LIST, translateTheory.FIXID_PAIR] THEN
    SUBGOAL_THEN ``fix_list (fix_pair f0 f1) x = x`` SUBST_ALL_TAC THENL [ALL_TAC,
        Q.ABBREV_TAC `m = sexp_to_list (sexp_to_pair I I) x` THEN
        `QSORT3 ($<= LEX K (K T)) (M2L (L2M m)) = m` by MATCH_MP_TAC (PULL_RULE M2L_L2M) THEN
        RW_TAC std_ss [SEXP_LE_TOTAL, SEXP_LE_TRANSITIVE, TRANSITIVE_K, SEXP_LE_ANTISYMMETRIC, QSORT3_SORTS, TRANSITIVE_LEX, TOTAL_LEX, TOTAL_K] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        Q.UNABBREV_TAC `m` THEN
        RW_TAC std_ss [RWR translateTheory.DECENCFIX_LIST, translateTheory.DECENCFIX_PAIR]] THEN
    MATCH_MP_TAC (GEN_ALL (PULL_RULE translateTheory.FIXID_LIST)) THEN
    Q.EXISTS_TAC `pairp p0 p1` THEN RW_TAC std_ss [] THEN MATCH_MP_TAC (GEN_ALL (PULL_RULE translateTheory.FIXID_PAIR)) THEN 
    METIS_TAC [combinTheory.I_THM,combinTheory.K_THM, translateTheory.GENERAL_DETECT_PAIR]);

val EVERY_PERM = store_thm("EVERY_PERM", ``!l1 l2. PERM l1 l2 ==> (EVERY P l1 = EVERY P l2)``,
    METIS_TAC [MEM_PERM, EVERY_MEM]);

val INV_LEX_PAIRMAP = store_thm("INV_LEX_PAIRMAP", 
    ``ONE_ONE f ==> (inv_image (R LEX R') (f ## g) = inv_image R f LEX inv_image R' g)``,
    RW_TAC std_ss [relationTheory.inv_image_def, pairTheory.LEX_DEF,pairTheory.PAIR_MAP, FUN_EQ_THM] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN (fn (a,g) => MAP_EVERY (fn b => SPEC_TAC (b,b)) (free_vars g) (a,g)) THEN
    REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [] THEN
    METIS_TAC [ONE_ONE_THM]);

val INVIMAGE_K = store_thm("INVIMAGE_K",
    ``inv_image (K (K T)) x = K (K T)``,
    RW_TAC std_ss [relationTheory.inv_image_def, pairTheory.LEX_DEF,pairTheory.PAIR_MAP, FUN_EQ_THM] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN (fn (a,g) => MAP_EVERY (fn b => SPEC_TAC (b,b)) (free_vars g) (a,g)) THEN
    REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss []);

(*****************************************************************************)
(* ENCDETALL_FMAP: Encoding then detecting equals every                      *)
(*****************************************************************************)

val ENCDETALL_FMAP = store_thm("ENCDETALL_FMAP",
    ``!p0 p1 f0 f1. ONE_ONE f0 ==> (detect_fmap p0 p1 o encode_fmap f0 f1 = all_fmap (p0 o f0) (p1 o f1))``,
    RW_TAC std_ss [FUN_EQ_THM, detect_fmap_def, encode_fmap_def, all_fmap_def, RWR translateTheory.ENCDETALL_LIST, 
                  all_fmap_def, RWR translateTheory.ENCDECMAP_LIST, translateTheory.ENCDECMAP_PAIR, MAPSET_def, 
                  translateTheory.ENCDETALL_PAIR, map_lemma] THEN
    `!Q. EVERY Q (QSORT3 (inv_image $<= f0 LEX K (K T)) (M2L x)) = EVERY Q (M2L x)` by MATCH_MP_TAC EVERY_PERM THEN
    RW_TAC std_ss [PERM_QSORT3, PERM_SYM] THEN
    MATCH_MP_TAC (DECIDE ``!a b. a ==> (a /\ b = b)``) THEN REPEAT CONJ_TAC THEN
    MAP_FIRST MATCH_MP_TAC [SORTED_MAP, ALL_DISTINCT_MAP] THEN
    METIS_TAC [QSORT3_SORTS, SORTS_DEF, TRANSITIVE_LEX, TRANSITIVE_K, SEXP_LE_TRANSITIVE, TOTAL_LEX, TOTAL_K, SEXP_LE_TOTAL, 
               TOTAL_INV, TRANS_INV, INV_LEX_PAIRMAP, 
               INVIMAGE_K, ALL_DISTINCT_MAPFST_M2L, PERM_QSORT3, PERM_MAP, PERM_TRANS, PERM_SYM, ALL_DISTINCT_PERM]);
    
(*****************************************************************************)
(* ALLID_FMAP: All identity                                                  *)
(*****************************************************************************)

val ALLID_FMAP = store_thm("ALLID_FMAP", ``all_fmap (K T) (K T) = K T``,
    RW_TAC std_ss [all_fmap_def,translateTheory.ALLID_PAIR, translateTheory.ALLID_LIST]);

(*****************************************************************************)
(* DETECT_DEAD: Detect nil is always true.                                   *)
(*****************************************************************************)

val DETECTDEAD_FMAP = store_thm("DETECTDEAD_FMAP", ``!p0 p1. detect_fmap p0 p1 nil``,
    RW_TAC std_ss [detect_fmap_def, translateTheory.sexp_to_list_def, sexpTheory.nil_def, MAPSET_def, 
       SORTED_DEF, ALL_DISTINCT_THM, MAP, MEM, FILTER, translateTheory.listp_def,translateTheory.pairp_def]);

val MAPSET_CONS = store_thm("MAPSET_CONS", 
    ``!b a R. MAPSET ($<= LEX (K (K T))) (a::b) ==> MAPSET ($<= LEX (K (K T))) b``,
    RW_TAC std_ss [MAPSET_def, SORTED_EQ, SEXP_LE_TRANSITIVE, TRANSITIVE_LEX, TRANSITIVE_K, MAP, ALL_DISTINCT]);

(*****************************************************************************)
(* DETECT_GENERAL_FMAP: An exact map implies any map                         *)
(*****************************************************************************)

val DETECT_GENERAL_FMAP = store_thm("DETECT_GENERAL_FMAP",
    ``!p0 p1 x. detect_fmap p0 p1 x ==> detect_fmap (K T) (K T) x``,
    REWRITE_TAC [detect_fmap_def] THEN
    NTAC 2 GEN_TAC THEN Induct THEN RW_TAC std_ss [] THEN
    RW_TAC std_ss [translateTheory.listp_def, translateTheory.pairp_def] THEN
    FULL_SIMP_TAC std_ss [translateTheory.listp_def,translateTheory.pairp_def, translateTheory.sexp_to_list_def] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    METIS_TAC [MAPSET_CONS]);


(*****************************************************************************)
(* MAP_COMPOSE: Composition of maps                                          *)
(* `fmap_map f0 f1 o fmap_map g0 g1 = fmap_map (f0 o g0) (f1 o g1)`          *)
(* Only needed for types based upon finite maps                              *)
(*****************************************************************************)

(*****************************************************************************)
(* ENCMAPENC: Composition of encoding                                        *)
(* `encode_fmap f0 f1 o map_fmap g0 g1 = encode_fmap (f0 o g0) (f1 o g1)`    *)
(* Only needed for types based upon finite maps                              *)
(*****************************************************************************)

(*****************************************************************************)
(* Rewrite theorems:                                                         *)
(*   -) sorted_car_rewrite                                                   *)
(*****************************************************************************)

val sorted_car_def = TotalDefn.tDefine "sorted_car" `
    sorted_car a = ite (andl [consp a ; consp (cdr a)])
                       (andl [not (equal (caar a) (caadr a)) ; lexorder (caar a) (caadr a) ; sorted_car (cdr a)])
                       t`
    (WF_REL_TAC `measure sexp_size` THEN Cases_on `a` THEN 
     RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS]);

val sexp_nil = REWRITE_RULE [hol_defaxiomsTheory.ACL2_SIMPS] (
         prove(``!a f. (consp a = nil) ==> (sexp_to_list f a = []) /\ (car a = nil) /\ (cdr a = nil)``,
         Cases THEN RW_TAC std_ss [translateTheory.sexp_to_list_def, hol_defaxiomsTheory.ACL2_SIMPS]));

val trans_rewrite = REWRITE_RULE [SEXP_LE_def, hol_defaxiomsTheory.ACL2_SIMPS, relationTheory.transitive_def] SEXP_LE_TRANSITIVE;
val sym_rewrite = REWRITE_RULE [SEXP_LE_def, hol_defaxiomsTheory.ACL2_SIMPS, relationTheory.antisymmetric_def] SEXP_LE_ANTISYMMETRIC;

val lemma = prove(
     ``!x' x. ~(lexorder (car x) (car (car x')) = nil) /\ ~(car x = car (car x')) /\ (sorted_car x' = t) ==> ~MEM (car x) (MAP FST (sexp_to_list (sexp_to_pair I I) x'))``,
     Induct THEN ONCE_REWRITE_TAC [sorted_car_def] THEN
     REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS, translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def, MAP, ALL_DISTINCT, MEM] THEN
     RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [] THEN
     Cases_on `x'` THEN
     FULL_SIMP_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def, MAP, ALL_DISTINCT, MEM] THEN
     RW_TAC std_ss [sexp_nil,MAP,MEM] THEN
     `~(car x = car (car x''))` by METIS_TAC [REWRITE_RULE [SEXP_LE_def, hol_defaxiomsTheory.ACL2_SIMPS, relationTheory.antisymmetric_def] SEXP_LE_ANTISYMMETRIC] THEN
     FIRST_ASSUM (fn x => MATCH_MP_TAC x THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC trans_rewrite THEN METIS_TAC []));

val sorted_car_cons = prove(``!y x. sorted_car (cons x y) = ite (consp y) (andl [not (equal (car x) (caar y)) ; lexorder (car x) (caar y); sorted_car y]) t``,
    CONV_TAC (ONCE_DEPTH_CONV (LAND_CONV (REWR_CONV sorted_car_def))) THEN
    RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS]);

val sorted_car_distinct = store_thm("sorted_car_distinct",
    ``!x. (sorted_car x = t) ==> ALL_DISTINCT (MAP FST (sexp_to_list (sexp_to_pair I I) x))``,
     Induct THEN ONCE_REWRITE_TAC [sorted_car_def] THEN
     REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS, translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def, MAP, ALL_DISTINCT, MEM] THEN
     RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [] THEN
     Cases_on `x'` THEN
     FULL_SIMP_TAC std_ss [sorted_car_cons, hol_defaxiomsTheory.ACL2_SIMPS, translateTheory.sexp_to_list_def, 
     		   translateTheory.sexp_to_pair_def, MAP, ALL_DISTINCT, MEM] THEN
     REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [sexp_nil,MAP,MEM] THEN
     TRY (FIRST_ASSUM (STRIP_ASSUME_TAC o el 2 o CONJUNCTS o SPEC_ALL o MATCH_MP sexp_nil) THEN
          POP_ASSUM (CONV_TAC o DEPTH_CONV o REWR_CONV o GSYM)) THEN
     TRY (MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [SEXP_LT_def,hol_defaxiomsTheory.ACL2_SIMPS] THEN
          CONJ_TAC THEN1 (MATCH_MP_TAC trans_rewrite THEN Q.EXISTS_TAC `car s` THEN METIS_TAC []) THEN METIS_TAC [sym_rewrite]) THEN
     METIS_TAC [sym_rewrite, sexp_nil]);

val slemma = prove(``!x l. SORTED (SEXP_LE LEX K (K T)) (x::l) = SORTED (SEXP_LE LEX K (K T)) l /\ ((l = []) \/ ((SEXP_LE LEX K (K T)) x (HD l)))``,
    GEN_TAC THEN Cases THEN RW_TAC std_ss [sortingTheory.SORTED_DEF,HD] THEN METIS_TAC []);

val sorted_car_sorted = store_thm("sorted_car_sorted", 
    ``!x. (sorted_car x = t) ==> SORTED (SEXP_LE LEX K (K T)) (sexp_to_list (sexp_to_pair I I) x)``,
    Induct THEN ONCE_REWRITE_TAC [sorted_car_def] THEN 
    REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS, translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def, MAP, ALL_DISTINCT,
                 sortingTheory.SORTED_DEF] THEN
    RW_TAC std_ss [slemma] THEN TRY (METIS_TAC [sexpTheory.t_def]) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN TRY (Cases_on `x'`) THEN 
    REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS, translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def, MAP, ALL_DISTINCT,
                 sortingTheory.SORTED_DEF] THEN
    RW_TAC std_ss [HD, SEXP_LT_def,pairTheory.LEX_DEF, SEXP_LE_def, hol_defaxiomsTheory.ACL2_SIMPS] THEN
    METIS_TAC [sexp_nil]);

val MAPSET_sortedcar = store_thm("MAPSET_sortedcar",
   ``!l. MAPSET (SEXP_LE LEX K (K T)) (sexp_to_list (sexp_to_pair I I) l) ==> (sorted_car l = t)``,
   Induct THEN ONCE_REWRITE_TAC [sorted_car_def] THEN TRY (REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS] THEN NO_TAC) THEN
   REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS,translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def] THEN
   RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [MAPSET_def, slemma, MAP, ALL_DISTINCT, sexpTheory.t_def] THEN
   Cases_on `l'` THEN
   REWRITE_TAC [hol_defaxiomsTheory.ACL2_SIMPS,translateTheory.sexp_to_list_def, translateTheory.sexp_to_pair_def, 
   	       MEM, ALL_DISTINCT, MAP, sortingTheory.SORTED_DEF] THEN
   FULL_SIMP_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS] THEN
   RW_TAC std_ss [HD, pairTheory.LEX_DEF, SEXP_LE_def,SEXP_LT_def, hol_defaxiomsTheory.ACL2_SIMPS] THEN
   METIS_TAC [sexp_nil]);

val booleanp_sortedcar = store_thm("booleanp_sortedcar", ``!x. |= booleanp (sorted_car x)``,
    Induct THEN
    ONCE_REWRITE_TAC [sorted_car_def] THEN REPEAT (
       RW_TAC std_ss [translateTheory.TRUTH_REWRITES, hol_defaxiomsTheory.booleanp_def,sexpTheory.ite_def, 
       	      sexpTheory.equal_def, sexpTheory.andl_def, sexpTheory.consp_def, sexpTheory.car_def, sexpTheory.cdr_def] THEN 
       REPEAT (POP_ASSUM MP_TAC)));

val sorted_car_rewrite = store_thm("sorted_car_rewrite", 
    ``!x. bool ((MAPSET (SEXP_LE LEX K (K T)) o sexp_to_list (sexp_to_pair I I)) x) = sorted_car x``,
    STRIP_TAC THEN Cases_on `sorted_car x = t` THEN RW_TAC std_ss [bool_rwr] THEN 
    MAP_EVERY IMP_RES_TAC [sorted_car_sorted, sorted_car_distinct, MAPSET_sortedcar] THEN RW_TAC std_ss [] THEN
    ASSUME_TAC (Q.SPEC `x` booleanp_sortedcar) THEN
    FULL_SIMP_TAC std_ss [MAPSET_def] THEN
    POP_ASSUM MP_TAC THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS]);

(*****************************************************************************)
(* fdom_rewrite: bool (x IN FDOM y)                                          *)
(*****************************************************************************)

val assoc_list = store_thm("assoc_list",
    ``!y f g x. ONE_ONE f ==> (assoc (f x) (list (pair f g) y) = if (?z. MEM (x,z) y) then pair f g (HD (FILTER ($= x o FST) y)) else nil)``,
    Induct THEN ONCE_REWRITE_TAC [hol_defaxiomsTheory.assoc_def] THEN 
    RW_TAC std_ss [MEM,translateTheory.list_def, hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def,bool_rwr, translateTheory.pair_def, FILTER, HD] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [] THEN
    TRY (POP_ASSUM (ASSUME_TAC o REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] o Q.SPEC `SND h`)) THEN
    METIS_TAC [ONE_ONE_THM]);

val not_pair_nil = prove(``!y f g. not (equal nil (pair f g y)) = t``,
    Cases THEN RW_TAC std_ss [translateTheory.pair_def,hol_defaxiomsTheory.ACL2_SIMPS]);

val not_nil_nil = prove(``not (equal nil nil) = nil``,
    RW_TAC std_ss [translateTheory.pair_def,hol_defaxiomsTheory.ACL2_SIMPS]);

val fdom_rewrite = store_thm("fdom_rewrite", 
    ``!y x. ONE_ONE f ==> (bool (x IN FDOM y) = not (equal nil (assoc (f x) (encode_fmap f g y))))``,
    REWRITE_TAC [encode_fmap_def,combinTheory.o_THM, GSYM EXISTS_MEM_M2L, bool_rwr] THEN
    RW_TAC std_ss [assoc_list, not_pair_nil, translateTheory.TRUTH_REWRITES,not_nil_nil] THEN
    METIS_TAC [PERM_QSORT3, MEM_PERM]);

(*****************************************************************************)
(* apply_rewrite: encode (y ' x)                                             *)
(*****************************************************************************)

val FILTER_EQ_SEXP_SORT = store_thm("FILTER_EQ_SEXP_SORT",
    ``!x l f. FILTER ($= x o FST) (QSORT3 (inv_image SEXP_LE f LEX K (K T)) l) = FILTER ($= x o FST) l``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC (GSYM (PULL_RULE (DISCH_ALL (CONJUNCT2 (MATCH_MP (fst (EQ_IMP_RULE (SPEC_ALL STABLE_DEF))) (UNDISCH (SPEC_ALL QSORT3_STABLE))))))) THEN
    REPEAT (RW_TAC std_ss [TRANS_INV, TRANSITIVE_LEX, TRANSITIVE_K, SEXP_LE_TRANSITIVE, TOTAL_INV, TOTAL_K, TOTAL_LEX, SEXP_LE_TOTAL, relationTheory.inv_image_def, pairTheory.LEX_DEF] THEN
            REPEAT STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN ALL_CASES (K true)));

val uniql_FILTER = prove(``!l. uniql l /\ MEM (x,y) l ==> (HD (FILTER ($= x o FST) l) = (x,y))``,
    Induct THEN REPEAT STRIP_TAC THEN IMP_RES_TAC uniql_cons THEN RW_TAC std_ss [uniql_def, FILTER, MEM, HD] THEN FULL_SIMP_TAC std_ss [MEM] THEN RES_TAC THEN
    FULL_SIMP_TAC std_ss [uniql_def,MEM] THEN RES_TAC THEN Cases_on `h` THEN FULL_SIMP_TAC std_ss []);

val apply_rewrite = store_thm("apply_rewrite", 
    ``!y x. ONE_ONE f /\ x IN FDOM y ==> (g (y ' x) = cdr (assoc (f x) (encode_fmap f g y)))``,
    REWRITE_TAC [encode_fmap_def,combinTheory.o_THM, GSYM EXISTS_MEM_M2L, bool_rwr] THEN
    RW_TAC std_ss [assoc_list, not_pair_nil, translateTheory.TRUTH_REWRITES,not_nil_nil, GSYM translateTheory.PAIR_THMS, FILTER_EQ_SEXP_SORT] THEN
    STRIP_ASSUME_TAC (Q.SPEC `y` UNIQL_M2L) THEN
    IMP_RES_TAC uniql_FILTER THEN
    RW_TAC std_ss [] THEN
    METIS_TAC [MEM_M2L, PERM_QSORT3, MEM_PERM]);

val ains_def = TotalDefn.tDefine "ains" `ains a l = itel [(not (consp l), cons a nil) ;
                                            (equal (caar l) (car a), cons a (cdr l)) ; 
    	       	 		            (lexorder (car a) (caar l), cons a l)] 
                                           (cons (car l) (ains a (cdr l)))`
    (WF_REL_TAC `measure (sexp_size o SND)` THEN 
     GEN_TAC THEN Cases THEN RW_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.sexp_size_def]);

val insert_def = Define `(insert R (x,y) [] = [(x,y)]) /\
                         (insert R (x,y) ((hx,hy)::tl) = 
                             if hx = x then ((x,y)::tl) 
                                       else if R x hx then ((x,y)::(hx,hy)::tl)
                                                            else (hx,hy) :: insert R (x,y) tl)`;

val ains_insert = store_thm("ains_insert", ``!l f g x y. ONE_ONE f ==> (ains (pair f g (x,y)) (list (pair f g) l) = list (pair f g) (insert (inv_image SEXP_LE f) (x,y) l))``,
    Induct THEN ONCE_REWRITE_TAC [ains_def] THEN TRY (Cases_on `h`) THEN 
    RW_TAC std_ss [translateTheory.list_def, hol_defaxiomsTheory.ACL2_SIMPS, sexpTheory.itel_def, translateTheory.pair_def, insert_def, SEXP_LE_def, REWRITE_RULE [FUN_EQ_THM] relationTheory.inv_image_def] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [translateTheory.pair_def] THEN METIS_TAC [ONE_ONE_THM]);

val slemma = prove(``!x l. SORTED R (x::l) = SORTED R l /\ ((l = []) \/ (R x (HD l)))``,
    GEN_TAC THEN Cases THEN RW_TAC std_ss [sortingTheory.SORTED_DEF,HD] THEN METIS_TAC []);

val SORTED_INSERT = store_thm("SORTED_INSERT", 
    ``!R. total R ==> !l x y. SORTED (R LEX K (K T)) l ==> SORTED (R LEX K (K T)) (insert R (x,y) l)``,
    NTAC 2 STRIP_TAC THEN Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [slemma, SORTED_DEF, insert_def] THEN
    TRY (Cases_on `l`) THEN TRY (Cases_on `h`) THEN FULL_SIMP_TAC std_ss [pairTheory.LEX_DEF, HD, insert_def] THEN
    RW_TAC std_ss [HD] THEN
    METIS_TAC [relationTheory.total_def]);

val MEM_MAPFST_INSERT = store_thm("MEM_MAPFST_INSERT", 
    ``!l q x y. MEM q (MAP FST (insert R (x,y) l)) = (q = x) \/ MEM q (MAP FST l)``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [MEM, MAP, insert_def] THEN
    PROVE_TAC []);

val MEM_INSERT = store_thm("MEM_INSERT", 
    ``!l a x y. MEM a (insert R (x,y) l) ==> (FST a = x) /\ (SND a = y) \/ MEM a l``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [MEM, insert_def] THEN
    RES_TAC THEN FULL_SIMP_TAC std_ss [] THEN PROVE_TAC []);

val INSERT_EQ = store_thm("INSERT_EQ",
    ``!l x y y'. antisymmetric R /\ transitive (R LEX R') /\ ALL_DISTINCT (MAP FST l) /\ SORTED (R LEX R') l /\ MEM (x,y) (insert R (x,y') l) ==> (y = y')``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [MEM, insert_def,ALL_DISTINCT,MAP,MEM_MAP] THEN
    IMP_RES_TAC SORTED_EQ THEN FULL_SIMP_TAC std_ss [pairTheory.LEX_DEF] THEN METIS_TAC [relationTheory.antisymmetric_def,pairTheory.FST]);

val INSERT_INSERTS = store_thm("INSERT_INSERTS",
    ``!l x y R. MEM (x,y) (insert R (x,y) l)``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [insert_def, MEM]);

val INSERT_MEM = store_thm("INSERT_MEM",
    ``!l x y q r R. MEM (x,y) l ==> MEM (x,y) (insert R (q,r) l) \/ (x = q)``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [insert_def, MEM] THEN METIS_TAC []);

    
val ALL_DISTINCT_MAPFST_INSERT = store_thm("ALL_DISTINCT_MAPFST_INSERT",
    ``!l R x y. total R /\ antisymmetric R /\ transitive R /\ SORTED R (MAP FST l) /\ ALL_DISTINCT (MAP FST l) ==> ALL_DISTINCT (MAP FST (insert R (x,y) l))``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [insert_def, MAP, ALL_DISTINCT, MEM, SORTED_EQ, MAP] THEN
    IMP_RES_TAC SORTED_EQ THEN
    METIS_TAC [relationTheory.transitive_def, relationTheory.antisymmetric_def, relationTheory.total_def, MEM_MAPFST_INSERT]);

val INSERT_SET = store_thm("INSERT_SET",
    ``!l R R' x y. transitive R /\ antisymmetric R /\ total R /\ transitive (R LEX R') /\ SORTED (R LEX R') l /\ ALL_DISTINCT (MAP FST l) ==> 
              (set (insert R (x,y) l) = (x,y) INSERT (set l DIFF {z | FST z = x}))``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN RW_TAC std_ss [insert_def, LIST_TO_SET_THM, EMPTY_DIFF, INSERT_DIFF, ALL_DISTINCT, MAP] THEN
    IMP_RES_TAC SORTED_EQ THEN
    RW_TAC (std_ss ++ pred_setLib.PRED_SET_ss) [INSERT_DEF, DIFF_DEF, SET_EQ_SUBSET,SUBSET_DEF, LIST_TO_SET_THM, insert_def, IN_LIST_TO_SET, MEM_MAP] THEN
    IMP_RES_TAC MEM_INSERT THEN
    FULL_SIMP_TAC (std_ss ++ pred_setLib.PRED_SET_ss) [MEM_MAP, INSERT_INSERTS] THEN
    TRY (Cases_on `x'`) THEN FULL_SIMP_TAC std_ss [] THENL [
      ALL_TAC, RES_TAC THEN FULL_SIMP_TAC std_ss [pairTheory.LEX_DEF],
      ALL_TAC, ALL_TAC] THEN
    METIS_TAC [relationTheory.transitive_def, relationTheory.antisymmetric_def, relationTheory.total_def, INSERT_EQ, INSERT_MEM]);

val EMPTY_SET = METIS_PROVE [SET_EQ_SUBSET, SUBSET_DEF, NOT_IN_EMPTY] ``({} = a) = !x. ~(x IN a)``;

val M2L_RWR = prove(``!x y. MEM x (M2L y) = FST x IN FDOM y /\ (SND x = y ' (FST x))``,
    Cases THEN RW_TAC std_ss [MEM_M2L]);

val SET_M2L_DOMSUB = store_thm("SET_M2L_DOMSUB", 
    ``!m x. set (M2L (m \\ x)) = set (M2L m) DIFF {z | FST z = x}``,
    RW_TAC std_ss [SET_EQ_SUBSET, SUBSET_DEF, IN_DIFF, IN_LIST_TO_SET, M2L_RWR, FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM] THEN
    FULL_SIMP_TAC (std_ss ++ PRED_SET_ss) []);


val INSERT_FUPDATE = store_thm("INSERT_FUPDATE",
    ``!x y R m. transitive R /\ antisymmetric R /\ total R ==> (QSORT3 (R LEX K (K T)) (M2L (m |+ (x,y))) = insert R (x,y) (QSORT3 (R LEX K (K T)) (M2L m)))``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_FST_DISTINCT_EQ THEN REPEAT STRIP_TAC THENL [
      MATCH_MP_TAC PERM_SORTED_EQ THEN Q.EXISTS_TAC `R` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [
        MATCH_MP_TAC PERM_MAP,
        METIS_TAC [SORTED_LEX, QSORT3_SORTS, SORTS_DEF, TRANSITIVE_LEX, TOTAL_LEX, TRANSITIVE_K, TOTAL_K, SORTED_INSERT],
        METIS_TAC [SORTED_LEX, QSORT3_SORTS, SORTS_DEF, TRANSITIVE_LEX, TOTAL_LEX, TRANSITIVE_K, TOTAL_K, SORTED_INSERT]],
      METIS_TAC [ALL_DISTINCT_MAPFST_M2L, PERM_DISTINCT, PERM_QSORT3, PERM_MAP], ALL_TAC] THEN
    MATCH_MP_TAC SETEQ_PERM THEN REPEAT CONJ_TAC THEN
    TRY (MATCH_MP_TAC SETEQ_TRANS THEN Q.EXISTS_TAC `M2L (m |+ (x,y))` THEN CONJ_TAC THEN1 METIS_TAC [PERM_SETEQ, PERM_QSORT3, PERM_SYM] THEN
         REWRITE_TAC [SETEQ_THM, SET_M2L_FUPDATE, LIST_TO_SET_THM] THEN
         Q.ABBREV_TAC `l = QSORT3 (R LEX K (K T)) (M2L m)` THEN
         REVERSE (`set (insert R (x,y) l) = (x,y) INSERT (set l DIFF {z | FST z = x})` by MATCH_MP_TAC INSERT_SET) THEN1
	     (`set l = set (M2L m)` by METIS_TAC [PERM_SETEQ, SETEQ_THM, PERM_QSORT3] THEN ASM_REWRITE_TAC [SET_M2L_DOMSUB] THEN AP_TERM_TAC)) THEN
    METIS_TAC [PERM_MAP, ALL_DISTINCT_MAPFST_M2L, ALL_DISTINCT_PERM, ALL_DISTINCT_MAPFST_M2L, ALL_DISTINCT_MAPFST, PERM_QSORT3, SORTED_LEX, 
    	       TRANSITIVE_K, QSORT3_SORTS, SORTS_DEF, TOTAL_K, TOTAL_LEX, TRANSITIVE_LEX, ALL_DISTINCT_MAPFST_INSERT]);

val fupdate_rewrite = store_thm("fupdate_rewrite",
    ``!x f g m. ONE_ONE f ==> (encode_fmap f g (m |+ x) = ains (pair f g x) (encode_fmap f g m))``,
    Cases THEN RW_TAC std_ss [encode_fmap_def, ains_insert] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INSERT_FUPDATE THEN
    METIS_TAC [TRANS_INV, ANTISYM_INV, TOTAL_INV, SEXP_LE_TOTAL, SEXP_LE_TRANSITIVE, SEXP_LE_ANTISYMMETRIC]);

val _ = export_theory();