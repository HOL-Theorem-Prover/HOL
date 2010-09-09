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

val IND_STEP_TAC = PAT_ASSUM ``!y. P ==> Q`` 
    (MATCH_MP_TAC o CONV_RULE (REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV))));

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
    METIS_TAC [CARD_EQ_0, DECIDE ``0 < a = ¬(a = 0)``, NOT_IN_EMPTY, FDOM_FINITE]);

val uniql_rec = prove(``!x y. uniql x /\ ¬(?z. MEM (y,z) x) ==> (uniql ((y,z)::x))``,
    Induct THEN RW_TAC std_ss [uniql_def, MEM] THEN METIS_TAC []);

val INSERT_SING = prove(``(a INSERT b = {a}) = (b = {}) \/ (b = {a})``,
    ONCE_REWRITE_TAC [INSERT_SING_UNION] THEN RW_TAC std_ss [UNION_DEF,SET_EQ_SUBSET, SUBSET_DEF] THEN
    RW_TAC (std_ss ++ PRED_SET_ss) [] THEN METIS_TAC []);

val fold_FEMPTY = store_thm("fold_FEMPTY",``(!f v. fold f v FEMPTY = v)``,
    ONCE_REWRITE_TAC [fold_def] THEN RW_TAC std_ss []);

val infdom_lemma = prove(``!a b. ¬(a = b) /\ a IN FDOM x ==> (b IN FDOM x = b IN FDOM (x \\ a))``,
    RW_TAC (std_ss ++ PRED_SET_ss) [FDOM_DOMSUB, IN_DELETE]);

val EXISTS_MEM_M2L = prove(``!x a. (?y. MEM (a,y) (M2L x)) = a IN FDOM x``,
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

val UNIQL_M2L = prove(``!x. uniql (M2L x)``,
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


val SETEQ_def = Define `SETEQ l1 l2 = !x. MEM x l1 = MEM x l2`;

(*****************************************************************************)
(* M2L_L2M_SETEQ:                                                            *)
(* `!x. uniql x ==> SETEQ x (M2L (L2M x))`                                   *)
(*****************************************************************************)

val lemma1 = prove(``!x y z. uniql (y::x) ==> !z. MEM (FST y,z) x ==> (z = SND y)``,
    REPEAT (Cases ORELSE GEN_TAC) THEN REWRITE_TAC [uniql_def,MEM] THEN METIS_TAC []);

val M2L_L2M_SETEQ = prove(``!x. uniql x ==> SETEQ x (M2L (L2M x))``,
    Induct THEN RW_TAC std_ss [L2M, M2L_def, fold_FEMPTY, SETEQ_def,MEM] THEN
    IMP_RES_TAC uniql_cons THEN
    Cases_on `x' = h` THEN Cases_on `MEM x' x` THEN Cases_on `x'` THEN
    RW_TAC std_ss [GSYM M2L_def,GSYM IN_LIST_TO_SET, SET_M2L_FUPDATE] THEN
    RW_TAC std_ss [IN_LIST_TO_SET, MEM, MEM_M2L, FDOM_DOMSUB, DOMSUB_FAPPLY_THM, IN_DELETE, FDOM_L2M, L2M_APPLY] THEN
    METIS_TAC [lemma1,pairTheory.PAIR, L2M_APPLY, uniql_def]);

(*****************************************************************************)
(*                                                                           *)
(*****************************************************************************)

val SORTSET_def = Define `SORTSET sort relation = sort relation o SET_TO_LIST o set`;
val SORTEDSET_def = Define `SORTEDSET r l = SORTED r l /\ ALL_DISTINCT l`;
val MAPSET_def = Define `MAPSET r l = SORTED r l /\ ALL_DISTINCT (MAP FST l)`;

val RFILTER_EQ_NIL = 
    CONJ (REWRITE_RULE [] (AP_TERM ``$~`` (SPEC_ALL FILTER_NEQ_NIL)))
         (CONV_RULE (REWRITE_CONV [] THENC LAND_CONV SYM_CONV) (AP_TERM ``$~`` (SPEC_ALL FILTER_NEQ_NIL)))

val ALL_DISTINCT_THM = prove(``!l. ALL_DISTINCT l = !x. MEM x l ==> (FILTER ($= x) l = [x])``,
    Induct THEN RW_TAC std_ss [ALL_DISTINCT, MEM, FILTER] THEN
    EQ_TAC THEN RW_TAC std_ss [RFILTER_EQ_NIL] THENL [
      ALL_TAC,
      PAT_ASSUM ``!y. P`` (MP_TAC o Q.SPEC `h`),
      PAT_ASSUM ``!y. P`` (MP_TAC o Q.SPEC `x`)] THEN
   RW_TAC std_ss [RFILTER_EQ_NIL] THEN METIS_TAC[]);

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
    RW_TAC std_ss [REWRITE_RULE [] (AP_TERM ``$~`` (SPEC_ALL FILTER_NEQ_NIL)), MEM_SET_TO_LIST]);

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

val MEM_PERM = prove(``!l1 l2. PERM l1 l2 ==> (!a. MEM a l1 = MEM a l2)``,
    METIS_TAC [Q.SPEC `$= a` MEM_FILTER, PERM_DEF]);

val PERM_SORTED_EQ = store_thm("PERM_SORTED_EQ",
    ``!l1 l2 r. antisymmetric r /\ transitive r /\ PERM l1 l2 /\ SORTED r l1 /\ SORTED r l2 ==> (l1 = l2)``,
    REPEAT GEN_TAC THEN completeInduct_on `LENGTH l1 + LENGTH l2` THEN REPEAT Cases THEN REWRITE_TAC [LENGTH] THEN
    TRY (REWRITE_TAC [PERM_DEF, RFILTER_EQ_NIL, FILTER] THEN METIS_TAC [NOT_NIL_CONS]) THEN
    RW_TAC std_ss [NO_MEM_EMPTY] THEN
    `t = t'` by PAT_ASSUM ``!y. P ==> q`` (MATCH_MP_TAC o CONV_RULE (REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV)))) THEN
    IMP_RES_TAC SORTED_EQ THEN RW_TAC arith_ss [] THEN
    FULL_SIMP_TAC std_ss [PERM_CONS_EQ_APPEND] THEN
    Cases_on `M` THEN FULL_SIMP_TAC std_ss [APPEND,list_11] THEN
    REPEAT (PAT_ASSUM ``a = b`` SUBST_ALL_TAC) THEN
    `h = h''` by METIS_TAC [MEM_PERM, MEM, MEM_APPEND, SORTED_APPEND, relationTheory.antisymmetric_def] THEN
    METIS_TAC [PERM_FUN_APPEND_CONS, PERM_TRANS, PERM_SYM, APPEND]);

val SORTSET_SORTEDSET = store_thm("SORTSET_SORTEDSET",
    ``!l. transitive R /\ antisymmetric R /\ SORTS sort R /\ SORTEDSET R l ==> (SORTSET sort R l = l)``,
    RW_TAC std_ss [SORTEDSET_def,SORTSET_def, SETEQ_def, SORTS_DEF] THEN
    `PERM (sort R (SET_TO_LIST (set l))) l` by METIS_TAC [PERM_SYM, PERM_TRANS, PERM_S2L_L2S] THEN
    METIS_TAC [PERM_SORTED_EQ]);

val ALL_DISTINCT_M2L = prove(``!s. ALL_DISTINCT (M2L s)``,
    completeInduct_on `FCARD s` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [M2L_def] THEN ONCE_REWRITE_TAC [fold_def] THEN
    NTAC 2 (RW_TAC std_ss [ALL_DISTINCT, GSYM M2L_def,MEM_M2L,FDOM_DOMSUB,IN_DELETE]) THEN
    IND_STEP_TAC THEN
    METIS_TAC [fcard_less, not_fempty_eq]);

val PERM_DISTINCT = prove(``!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)``,
    METIS_TAC [MEM_PERM, PERM_DEF, ALL_DISTINCT_THM]);

val SORTSET_SORT = prove(``!l R. antisymmetric R /\ transitive R /\ SORTS sort R /\ ALL_DISTINCT l ==> (SORTSET sort R l = sort R l)``,
    RW_TAC std_ss [SORTS_DEF,SORTSET_def] THEN
    `PERM l (sort R (SET_TO_LIST (set l)))` by METIS_TAC [PERM_S2L_L2S, PERM_DISTINCT, PERM_TRANS, PERM_SYM] THEN
    MATCH_MP_TAC PERM_SORTED_EQ THEN RW_TAC std_ss [] THEN
    Q.EXISTS_TAC `R` THEN RW_TAC std_ss [] THEN
    METIS_TAC [PERM_S2L_L2S, PERM_DISTINCT, PERM_TRANS, PERM_SYM]);

val PERM_S2L_L2S_EQ = prove(``!l1 l2. SETEQ l1 l2 ==> PERM (SET_TO_LIST (set l1)) (SET_TO_LIST (set l2))``,
    RW_TAC std_ss [PERM_DEF, FILTER_SET, FINITE_LIST_TO_SET,IN_LIST_TO_SET,SETEQ_def]);

val PERM_SETEQ = prove(``!l1 l2. PERM l1 l2 ==> SETEQ l1 l2``,
    Induct THEN RW_TAC std_ss [PERM_CONS_EQ_APPEND, PERM_NIL,SETEQ_def] THEN
    Cases_on `x = h` THEN ASM_REWRITE_TAC [MEM, MEM_APPEND] THEN EQ_TAC THEN
    RES_TAC THEN FULL_SIMP_TAC std_ss [SETEQ_def, MEM_APPEND]);

val SORTSET_EQ = prove(``!l1 l2 R. SORTS sort R /\ antisymmetric R /\ transitive R /\ SETEQ l1 l2 ==> (SORTSET sort R l1 = SORTSET sort R l2)``,
    RW_TAC std_ss [SORTSET_def, SORTS_DEF] THEN
    MATCH_MP_TAC PERM_SORTED_EQ THEN Q.EXISTS_TAC `R` THEN RW_TAC std_ss [] THEN
    METIS_TAC [PERM_S2L_L2S_EQ,PERM_TRANS,PERM_SYM, PERM_SETEQ]);

val MAPSET_IMP_SORTEDSET = prove(``!l R. transitive R ==> (MAPSET R l ==> SORTEDSET R l)``,
    Induct THEN RW_TAC std_ss [MAPSET_def, SORTEDSET_def, ALL_DISTINCT, MAP, MEM_MAP] THEN
    METIS_TAC [MAPSET_def, SORTEDSET_def, SORTED_EQ]);

val SORTED_CONS = prove(``!a b R. SORTED R (a::b) ==> SORTED R b``,
    GEN_TAC THEN Cases THEN RW_TAC std_ss [SORTED_DEF]);

val MAPSET_CONS = prove(``!a b R. MAPSET R (a::b) ==> MAPSET R b``,
    RW_TAC std_ss [MAPSET_def, MAP, ALL_DISTINCT, SORTED_CONS] THEN
    METIS_TAC [SORTED_CONS]);


val MAPSET_UNIQ = prove(``!a R. MAPSET R a ==> uniql a``,	
    Induct THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MAPSET_CONS THEN RES_TAC THEN
    FULL_SIMP_TAC std_ss [uniql_def, MEM, uniql_def, MAPSET_def, MAP, ALL_DISTINCT, MEM_MAP] THEN
    Cases_on `h` THEN RW_TAC std_ss [] THENL [
       PAT_ASSUM ``!y. P \/ Q`` (MP_TAC o Q.SPEC `(q,y')`),
       PAT_ASSUM ``!y. P \/ Q`` (MP_TAC o Q.SPEC `(q,y)`),
       ALL_TAC] THEN 
    ASM_REWRITE_TAC [] THEN METIS_TAC []);


(*****************************************************************************)
(* M2L_L2M:                                                                  *)
(*`!l sort R. transitive R /\ antisymmetric R /\                             *) 
(*            SORTS sort R /\ MAPSET R l ==> (sort R (M2L (L2M l)) = l)`     *)
(*****************************************************************************)

val M2L_L2M = store_thm("M2L_L2M",
    ``!l sort R. transitive R /\ antisymmetric R /\ SORTS sort R /\ MAPSET R l ==> (sort R (M2L (L2M l)) = l)``,
    REPEAT STRIP_TAC THEN
    `(sort R (M2L (L2M l)) = l) = (SORTSET sort R (M2L (L2M l)) = SORTSET sort R l)` by 
    	   METIS_TAC [ALL_DISTINCT_M2L, SORTSET_SORT, SORTSET_SORTEDSET, MAPSET_IMP_SORTEDSET] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SORTSET_EQ THEN ASM_REWRITE_TAC [] THEN
    METIS_TAC [SETEQ_def, M2L_L2M_SETEQ, MAPSET_UNIQ]);

val _ = export_theory();

