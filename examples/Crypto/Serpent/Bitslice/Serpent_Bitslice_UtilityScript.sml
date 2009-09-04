open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitTheory
     markerTheory pairTheory arithmeticTheory wordsTheory wordsLib;

val _ = new_theory "Serpent_Bitslice_Utility";

(*conversion between different words,
EL 0 is the MS in all split result,
the bit ordering is perserved
*)

val _ = wordsLib.guess_lengths();
val _ = wordsLib.mk_word_size 128;
val _ = wordsLib.mk_word_size 256;

val word128to32l_def = Define`
 word128to32l (w:word128) =
 [(127 >< 96) w; (95 >< 64) w; (63 >< 32) w; (31 >< 0) w]`;

val word256to128l = Define
`word256to128l (w:word256) = [(255 >< 128) w; (127 >< 0) w]`;

val word256to32l_def = Define
`word256to32l (w256:word256) = FLAT (MAP word128to32l (word256to128l w256))`;

val word256to32lLength = Q.store_thm (
"word256to32lLength",
`!w. LENGTH (word256to32l w) = 8`,
EVAL_TAC THEN METIS_TAC []);

(*housemade FIRSTN and BUTLASTN for easy evaluation*)
val (myFIRSTN_def,myFIRSTN_termi) = Defn.tstore_defn(
 Defn.Hol_defn "myFIRSTN"
`myFIRSTN n l = if n = 0
                then []
                else if l =[] then []
                else (HD l)::(myFIRSTN (n-1) (TL l))`,
  WF_REL_TAC `measure (LENGTH o SND)` THEN
  RW_TAC list_ss [] THEN
  Cases_on `l` THENL [
    FULL_SIMP_TAC list_ss [],
    RW_TAC list_ss []]);

val myBUTLASTN_def = Define
`myBUTLASTN n l
 = let len = LENGTH l
   in
   if len>= n
      then myFIRSTN (LENGTH l-n) l
      else []`;

val LENGTH_myFIRSTN = Q.store_thm(
"LENGTH_myFIRSTN",
`!n l.
    n <= LENGTH l
    ==>
    (LENGTH (myFIRSTN n l) = n)`,
  Induct_on `n` THENL [
    RW_TAC list_ss [] THEN
    `myFIRSTN 0 l =[]` by METIS_TAC  [myFIRSTN_def] THEN
    RW_TAC list_ss [],
    RW_TAC list_ss [] THEN
    Cases_on `l` THENL [
        FULL_SIMP_TAC list_ss [],
        `~(SUC n = 0)` by RW_TAC arith_ss [] THEN
        `~((h::t) =[])` by RW_TAC list_ss [] THEN
        `myFIRSTN (SUC n) (h::t)= (HD (h::t))::(myFIRSTN (SUC n-1) (TL (h::t)))`
          by  METIS_TAC  [myFIRSTN_def] THEN
        FULL_SIMP_TAC list_ss []]]);

val LENGTH_myBUTLASTN = Q.store_thm(
"LENGTH_myBUTLASTN",
`!n l.
    n <= LENGTH l
    ==>
    (LENGTH (myBUTLASTN n l) = LENGTH l - n)`,
  RW_TAC arith_ss [myBUTLASTN_def,LENGTH_myFIRSTN,LET_THM]);

(*explicitly instantiate a list give its length*)
val LENGTH_GREATER_EQ_CONS = Q.store_thm(
"LENGTH_GREATER_EQ_CONS",
`!l n.
    (LENGTH l >= SUC n)
    ==>
    ?x l'. (LENGTH l' >= n) /\ (l = x::l')`,
  Induct_on `l` THEN RW_TAC list_ss []);

val listInstGreaterEq8 = Q.store_thm(
"listInstGreaterEq8",
`!l.
    (LENGTH l>= 8)
    ==>
    ?v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 t.
        l = (v_1::v_2::v_3::v_4::v_5::v_6::v_7::v_8::t)`,
  REWRITE_TAC [REDEPTH_CONV numLib.num_CONV ``8``] THEN
  METIS_TAC  [LENGTH_GREATER_EQ_CONS, LENGTH_NIL]);

val listInstEq33 = Q.store_thm(
"listInstEq33",
`!l.
    (LENGTH l = 33)
    ==>
        ?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14
           v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27
           v_28 v_29 v_30 v_31 v_32.
            l = [v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9; v_10; v_11;
                     v_12; v_13; v_14; v_15; v_16; v_17; v_18; v_19; v_20; v_21;
             v_22; v_23; v_24; v_25; v_26; v_27; v_28; v_29; v_30; v_31;
             v_32]`,
  REWRITE_TAC [LENGTH_CONS, LENGTH_NIL, REDEPTH_CONV numLib.num_CONV ``33``]
    THEN METIS_TAC []);

val _ = export_theory();
