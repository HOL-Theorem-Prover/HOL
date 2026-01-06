Theory Serpent_Reference_Utility
Ancestors
  list rich_list bit marker pair arithmetic words
Libs
  wordsLib

(* XOR *)

Definition boolXor_def:   boolXor (x:bool) y = ~(x= y)
End

Theorem boolXorComm:
  !x y. boolXor x y = boolXor y x
Proof
 METIS_TAC [boolXor_def]
QED

Theorem boolXorAssoc:
  !x y z. boolXor z (boolXor x y) = boolXor (boolXor z x) y
Proof
 METIS_TAC [boolXor_def]
QED

Theorem boolXorFacts:
  (!x.(boolXor x x) = F) /\
  (!x.(boolXor x T) = ~x) /\
  (!x.(boolXor x F) = x)
Proof
 METIS_TAC [boolXor_def]
QED

Theorem boolXorComm3:
  !x y z. boolXor x (boolXor y z) = boolXor y (boolXor x z)
Proof
  Cases_on `x` THEN Cases_on `y` THEN Cases_on `z` THEN
  RW_TAC std_ss [boolXor_def]
QED

(* trivial stuff about list *)

Theorem ALL_EL_FILTER:
  !p q l.
    ALL_EL p l
    ==>
    ALL_EL p (FILTER q l)
Proof
 Induct_on `l` THEN RW_TAC list_ss []
QED

Theorem LENGTH_NIL_LEQ:
  !n. LENGTH [] <= n
Proof
 RW_TAC list_ss []
QED

Theorem LENGTH_FILTER:
  !l p. LENGTH (FILTER p l) <= LENGTH l
Proof
 Induct_on `l` THEN
 RW_TAC list_ss [] THEN
 `LENGTH l <=  SUC (LENGTH l)` by RW_TAC arith_ss [] THEN
 METIS_TAC [LESS_EQ_TRANS]
QED

(* make a list of "T" of length n*)

Definition makeTL_def:
 (makeTL 0 =  []) /\
 (makeTL (SUC n) = T::(makeTL n))
End

Theorem LENGTH_makeTL:
  !n. LENGTH (makeTL n) = n
Proof
 Induct_on `n` THEN RW_TAC list_ss [makeTL_def]
QED

Theorem makeTL_fact:
  !i n.
    i<n
    ==>
    EL i (makeTL n)
Proof
 Induct_on `n` THENL [
   RW_TAC arith_ss [],
   Cases_on `i` THEN
   RW_TAC list_ss [makeTL_def]]
QED

(* XOR on bool lists in ZIP fashion *)

Definition zipXor_def:
 (zipXor [] l = l) /\
 (zipXor (xh::xt) (ah::at) = (boolXor xh ah)::zipXor xt at)   /\
 (zipXor (xh::xt) [] = [])
End

Theorem zipXor_fact:
  !l. zipXor l [] = []
Proof
 Cases_on `l` THEN
 RW_TAC list_ss [zipXor_def]
QED

Theorem LENGTH_zipXor:
  !l1 l2. LENGTH (zipXor l1 l2) = LENGTH l2
Proof
 Induct_on `l2` THENL [
   Cases_on `l1` THEN
   RW_TAC list_ss [zipXor_def],
   Cases_on `l1` THEN
   RW_TAC list_ss [zipXor_def]]
QED

Definition makeL_def:
 (makeL 0 = [T]) /\
 (makeL (SUC n) = F::makeL n)
End

Theorem zipXor_makeL_COMM:
  !i n1 n2 l.
     zipXor (makeL n2) (zipXor (makeL n1) al) =
     zipXor (makeL n1) (zipXor (makeL n2) al)
Proof
 Induct_on `al` THENL [
   RW_TAC list_ss [zipXor_fact],
   Cases_on `n1` THEN Cases_on `n2` THEN
   RW_TAC list_ss [makeL_def,zipXor_def,boolXor_def]]
QED

Theorem zipXor_makeL:
  !i al h tl.
    i < LENGTH al  /\
    h < LENGTH al
    ==>
    (EL i (zipXor (makeL h) al) = boolXor (i = h) (EL i al))
Proof
 Induct_on `h` THENL [
   RW_TAC list_ss [zipXor_def,makeL_def] THEN
   Cases_on `al` THEN
   FULL_SIMP_TAC list_ss [zipXor_def,boolXor_def] THEN
   Cases_on `i` THEN
   RW_TAC list_ss [],
   RW_TAC list_ss [makeL_def] THEN
   Cases_on `al` THEN
   RW_TAC list_ss [zipXor_def,boolXor_def] THEN
   Cases_on `i` THEN
   FULL_SIMP_TAC list_ss [boolXor_def]]
QED

Theorem MAP_ID:
  !l f.
    ALL_EL (\x. f x = x) l
    ==>
    (MAP f l = l)
Proof
 Induct_on `l` THEN
 RW_TAC list_ss []
QED

(* housemade FIRSTN and BUTLASTN for easy evaluation*)

val (myFIRSTN_def,myFIRSTN_termi) = Defn.tstore_defn(
 Defn.Hol_defn "myFIRSTN"
 `myFIRSTN n l =
    if n = 0 then []
    else if l =[] then []
    else (HD l)::(myFIRSTN (n-1) (TL l))`,
 WF_REL_TAC `measure (LENGTH o SND)` THEN
 RW_TAC list_ss [] THEN
 Cases_on `l` THENL [
   FULL_SIMP_TAC list_ss [],
   RW_TAC list_ss []]);

Definition myBUTLASTN_def:
 myBUTLASTN n l = let len = LENGTH l in
   if len>= n then myFIRSTN (LENGTH l-n) l
   else []
End

Theorem LENGTH_myFIRSTN:
  !n l.
    n <= LENGTH l
    ==>
    (LENGTH (myFIRSTN n l) = n)
Proof
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
      FULL_SIMP_TAC list_ss []]]
QED

Theorem LENGTH_myBUTLASTN:
  !n l.
    n <= LENGTH l
    ==>
    (LENGTH (myBUTLASTN n l) = LENGTH l - n)
Proof
 RW_TAC arith_ss [myBUTLASTN_def,LENGTH_myFIRSTN,LET_THM]
QED


(* conversion between different words, EL 0 is the MS in all split result,
   the bit ordering is perserved *)

val _ = wordsLib.guess_lengths();
val _ = wordsLib.mk_word_size 128;
val _ = wordsLib.mk_word_size 256;

Definition word128to32l_def:
 word128to32l (w:word128) =
 [(127 >< 96) w; (95 >< 64) w; (63 >< 32) w; (31 >< 0) w]
End

Definition word32to8l_def:
 word32to8l (w:word32) =
 [(31 >< 24) w; (23 >< 16) w; (15 >< 8) w; (7 >< 0) w]
End

Definition word8to4l_def:
 word8to4l(w:word8) =
 [(7 >< 4) w; (3 >< 0) w]
End

Definition word32to4l_def:
 word32to4l w = FLAT (MAP word8to4l (word32to8l w))
End

Definition word4to32_def:   word4to32 = w2w:word4->word32
End
Definition word4to128_def:   word4to128 = w2w:word4->word128
End
Definition word32to128_def:   word32to128 = w2w:word32->word128
End

Definition word256to128l:
 word256to128l (w:word256) =
 [(255 >< 128) w; (127 >< 0) w]
End

Definition word256to32l_def:
 word256to32l (w:word256) = FLAT (MAP word128to32l (word256to128l w))
End

(* input is in MSNibble....LSNibble in each Nibble, MSBit..LSBit input is
   of 32 nibbles *)

(* convert a word4 list to a num LSW,,,,,MSW *)

Definition revWord4ltoNum_def:
 (revWord4ltoNum ([]:word4 list) = 0) /\
 (revWord4ltoNum (h::t) = (w2n h + (revWord4ltoNum t) * 16))
End

(* convert a num to a word4 list, the length of list is controled by a
   parameter, the length provides a MOD LSW,,,,,MSW *)

Definition numtoRevWord4l_def:
 (numtoRevWord4l 0 n = [] : word4 list) /\
 (numtoRevWord4l (SUC m) n = n2w (n MOD 16)::(numtoRevWord4l m (n DIV 16)))
End

Theorem numtoRevWord4lEval:
  !n m.
    numtoRevWord4l m n =
    if m = 0 then []
    else n2w (n MOD 16)::(numtoRevWord4l (m-1) (n DIV 16))
Proof
 RW_TAC arith_ss [numtoRevWord4l_def] THEN
 Cases_on `m` THENL [
   METIS_TAC [],
   FULL_SIMP_TAC arith_ss [numtoRevWord4l_def]]
QED

(* the length provides a MOD *)

Theorem revWord4ltoNumRange:
  !n l.
    LENGTH l <= n ==> revWord4ltoNum l < 2 ** (4 * n)
Proof
 Induct_on `l` THENL [
   METIS_TAC [ revWord4ltoNum_def,ZERO_LESS_EXP,DECIDE ``2 = SUC 1``],
   RW_TAC list_ss [revWord4ltoNum_def] THEN
   Cases_on `n` THENL [
     FULL_SIMP_TAC arith_ss [],
     `4 * SUC n' = 4 + 4 * n'` by RW_TAC arith_ss [] THEN
     `w2n h < 16` by WORD_DECIDE_TAC THEN
     FULL_SIMP_TAC std_ss [EXP_ADD] THEN
     FULL_SIMP_TAC list_ss [] THEN
     `revWord4ltoNum l < 2 ** (4 * n') ` by METIS_TAC [] THEN
     `SUC (revWord4ltoNum l) <= 2 ** (4 * n')` by METIS_TAC [LESS_EQ] THEN
     `16+16* (revWord4ltoNum l)<= 16* 2 ** (4 * n')` by RW_TAC arith_ss [] THEN
     FULL_SIMP_TAC arith_ss []]]
QED

Theorem LENGTH_numtoRevWord4l:
  !wl n.
    LENGTH (numtoRevWord4l n wl) = n
Proof
 Induct_on `n` THEN
 RW_TAC list_ss [numtoRevWord4l_def]
QED

(* the conversions between a num and word4 list are reversible *)

Theorem numtoRevWord4l_conversion:
  !n wl.
    (n = LENGTH wl)
    ==>
    (numtoRevWord4l n (revWord4ltoNum wl) = wl)
Proof
 Induct_on `wl` THEN
 RW_TAC list_ss [revWord4ltoNum_def,numtoRevWord4l_def] THEN
 `w2n h < 16` by WORD_DECIDE_TAC THENL [
    `(16 * revWord4ltoNum wl + w2n h) MOD 16 = w2n h`
        by METIS_TAC [MOD_MULT, MULT_COMM] THEN
    SRW_TAC [] [],
    `(revWord4ltoNum wl * 16) MOD 16 = 0 `
        by METIS_TAC [MOD_EQ_0,DECIDE ``0<16``] THEN
     FULL_SIMP_TAC arith_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO,
       ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]]
QED

Theorem revWord4ltoNum_conversion:
  !n len.
    n < 2 ** (4 * len)
    ==>
    (revWord4ltoNum  (numtoRevWord4l len n) = n)
Proof
 Induct_on `len` THEN
 RW_TAC list_ss [revWord4ltoNum_def,numtoRevWord4l_def] THEN
 `n DIV 16 <= 2 ** (4 * SUC len) DIV 16`
   by RW_TAC arith_ss [DIV_LE_MONOTONE] THEN
 `n = n DIV 16 * 16 + n MOD 16` by METIS_TAC [DIVISION,DECIDE ``0<16``] THEN
 `2 ** (4 * SUC len) = 2**(4* len)*16`
   by FULL_SIMP_TAC std_ss [DECIDE ``4* SUC len = 4*len +4``,EXP_ADD] THEN
 FULL_SIMP_TAC std_ss [MULT_DIV] THEN
 `n DIV 16 * 16<= 2 ** (4 * len)*16` by RW_TAC arith_ss [] THEN
 Cases_on ` n DIV 16 = 2 ** (4 * len) ` THEN
  Cases_on `n MOD 16 = 0` THEN
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
QED

(* the conversions between a word128 and word4 list*)

Definition word4ltow128_def:
 word4ltow128 w4l = n2w (revWord4ltoNum (REVERSE w4l)) : word128
End

Definition word128tow4l_def:
 word128tow4l (w:word128) = REVERSE (numtoRevWord4l 32 (w2n w))
End

Theorem LENGTH_word128tow4l:
  !w.  LENGTH (word128tow4l w) = 32
Proof
 RW_TAC std_ss [word128tow4l_def,LENGTH_REVERSE,LENGTH_numtoRevWord4l]
QED

(* the conversions between a word128 and word4 list are reversible*)

Theorem word128tow4l_conversion:
  !l. (LENGTH l = 32) ==> (word128tow4l (word4ltow128 l) =l)
Proof
 SRW_TAC [] [word128tow4l_def,word4ltow128_def] THEN
 `LENGTH (REVERSE l) <= 32` by RW_TAC list_ss [LENGTH_REVERSE] THEN
 `revWord4ltoNum (REVERSE l) < 2 ** (4* 32)`
   by METIS_TAC [revWord4ltoNumRange] THEN
 FULL_SIMP_TAC arith_ss [LESS_MOD] THEN
 `LENGTH (REVERSE l) = 32` by RW_TAC list_ss [LENGTH_REVERSE] THEN
 `numtoRevWord4l 32 (revWord4ltoNum (REVERSE l)) = REVERSE l`
   by METIS_TAC [numtoRevWord4l_conversion] THEN
 METIS_TAC [REVERSE_REVERSE]
QED

Theorem word4ltow128_conversion:
  !w.  word4ltow128 (word128tow4l w) = w
Proof
 RW_TAC arith_ss [word4ltow128_def,word128tow4l_def,REVERSE_REVERSE] THEN
 `w2n w < 2 ** 128` by WORD_DECIDE_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [revWord4ltoNum_conversion]
QED

Theorem word256to32lLength:
  !w.  LENGTH (word256to32l w) = 8
Proof
 EVAL_TAC THEN METIS_TAC []
QED

(* instantiate explicit list given the length *)

Theorem LENGTH_GREATER_EQ_CONS:
  !l n.
    (LENGTH l >= SUC n)
    ==>
    ?x l'. (LENGTH l' >= n) /\ (l = x::l')
Proof
 Induct_on `l` THEN RW_TAC list_ss []
QED

Theorem listInstGreaterEq2:
  !l.
    (LENGTH l >= 2)
    ==>
    ?v_1 v_2 t. l = (v_1::v_2::t)
Proof
 REWRITE_TAC [REDEPTH_CONV numLib.num_CONV ``2``] THEN
 METIS_TAC  [LENGTH_GREATER_EQ_CONS, LENGTH_NIL]
QED

Theorem listInstEq2:
  !l.
    (LENGTH l = 2)
    ==>
    ?w_1 w_2. l = (w_1::w_2::[])
Proof
 METIS_TAC [LENGTH_CONS, LENGTH_NIL, REDEPTH_CONV numLib.num_CONV ``2``]
QED

Theorem listInstGreaterEq4:
  !l.
    (LENGTH l >= 4)
    ==>
    ?v_1 v_2 v_3 v_4 t. l = (v_1::v_2::v_3::v_4::t)
Proof
 REWRITE_TAC [REDEPTH_CONV numLib.num_CONV ``4``] THEN
 METIS_TAC  [LENGTH_GREATER_EQ_CONS, LENGTH_NIL]
QED

Theorem listInstEq4:
  !l.
    (LENGTH l = 4)
    ==>
    ?w_1 w_2 w_3 w_4. l = (w_1::w_2::w_3::w_4::[])
Proof
 REWRITE_TAC [LENGTH_CONS, LENGTH_NIL, REDEPTH_CONV numLib.num_CONV ``4``] THEN
 METIS_TAC []
QED

Theorem listInstGreaterEq8:
  !l.
    (LENGTH l >= 8)
    ==>
    ?v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 t. l =
    (v_1::v_2::v_3::v_4::v_5::v_6::v_7::v_8::t)
Proof
 REWRITE_TAC [REDEPTH_CONV numLib.num_CONV ``8``] THEN
 METIS_TAC  [LENGTH_GREATER_EQ_CONS, LENGTH_NIL]
QED

Theorem listInstEq8:
  !l.
    (LENGTH l = 8)
    ==>
    ?w_1 w_2 w_3 w_4 w_5 w_6 w_7 w_8. l =
    (w_1::w_2::w_3::w_4::w_5::w_6::w_7::w_8::[])
Proof
 REWRITE_TAC [LENGTH_CONS, LENGTH_NIL, REDEPTH_CONV numLib.num_CONV ``8``] THEN
 METIS_TAC []
QED

Theorem listInstEq32:
   !l.
    (LENGTH l = 32) ==>
        ?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14
         v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27
         v_28 v_29 v_30 v_31.
        l = [v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9; v_10; v_11;
             v_12; v_13; v_14; v_15; v_16; v_17; v_18; v_19; v_20; v_21; v_22;
             v_23; v_24; v_25; v_26; v_27; v_28; v_29; v_30; v_31]
Proof
 REWRITE_TAC [LENGTH_CONS, LENGTH_NIL, REDEPTH_CONV numLib.num_CONV ``32``] THEN
 METIS_TAC []
QED

Theorem listInstEq33:
  !l.
    (LENGTH l = 33) ==>
        ?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14
           v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27
           v_28 v_29 v_30 v_31 v_32.
        l = [v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9; v_10; v_11;
             v_12; v_13; v_14; v_15; v_16; v_17; v_18; v_19; v_20; v_21; v_22;
             v_23; v_24; v_25; v_26; v_27; v_28; v_29; v_30; v_31; v_32]
Proof
 REWRITE_TAC [LENGTH_CONS, LENGTH_NIL, REDEPTH_CONV numLib.num_CONV ``33``] THEN
 METIS_TAC []
QED

