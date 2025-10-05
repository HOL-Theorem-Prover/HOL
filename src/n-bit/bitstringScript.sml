(* ========================================================================= *)
(* FILE          : bitstringScript.sml                                       *)
(* DESCRIPTION   : Boolean lists as Bitstrings                               *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* ========================================================================= *)
Theory bitstring
Ancestors
  bit words numposrep
Libs
  fcpLib wordsLib


val _ = diminish_srw_ss ["NORMEQ"]

(* ------------------------------------------------------------------------- *)

(* MSB is head of list, e.g. [T, F] represents 2 *)

Type bitstring = “:bool list”

Definition extend_def:
   (extend _ 0 l = l: bitstring) /\
   (extend c (SUC n) l = extend c n (c::l))
End

Definition boolify_def:
  (boolify a [] = a) /\
  (boolify a (n :: l) = boolify ((n <> 0)::a) l)
End

Definition bitify_def:
  (bitify a [] = a) /\
  (bitify a (F :: l) = bitify (0::a) l) /\
  (bitify a (T :: l) = bitify (1::a) l)
End

Definition n2v_def: n2v n = boolify [] (n2l 2 n)
End

Definition v2n_def: v2n l = l2n 2 (bitify [] l)
End

Definition s2v_def:
  s2v = MAP (\c. (c = #"1") \/ (c = #"T"))
End

Definition v2s_def:
  v2s = MAP (\b. if b then #"1" else #"0")
End

Definition zero_extend_def[nocompute]:
  zero_extend n v = PAD_LEFT F n v
End

Definition sign_extend_def[nocompute]:
  sign_extend n v = PAD_LEFT (HD v) n v
End

Definition fixwidth_def[nocompute]:
  fixwidth n v =
     let l = LENGTH v in
       if l < n then
          zero_extend n v
       else
          DROP (l - n) v
End

Definition shiftl_def:
  shiftl v m = PAD_RIGHT F (LENGTH v + m) v
End

Definition shiftr_def:
  shiftr (v: bitstring) m = TAKE (LENGTH v - m) v
End

Definition field_def:
  field h l v = fixwidth (SUC h - l) (shiftr v l)
End

Definition rotate_def:
  rotate v m =
    let l = LENGTH v in
    let x = m MOD l
    in
      if (l = 0) \/ (x = 0) then v else field (x - 1) 0 v ++ field (l - 1) x v
End

Definition testbit_def[nocompute]:
  testbit b v = (field b b v = [T])
End

Definition w2v_def:
  w2v (w : 'a word) =
    GENLIST (\i. w ' (dimindex(:'a) - 1 - i)) (dimindex(:'a))
End

Definition v2w_def[nocompute]:
  v2w v : 'a word = FCP i. testbit i v
End

Definition rev_count_list_def:
  rev_count_list n = GENLIST (\i. n - 1 - i) n
End

Definition modify_def:
  modify f (v : bitstring) =
    MAP (UNCURRY f) (ZIP (rev_count_list (LENGTH v), v)) : bitstring
End

Definition field_insert_def:
  field_insert h l s =
    modify (\i. COND (l <= i /\ i <= h) (testbit (i - l) s))
End

Definition add_def:
   add a b =
     let m = MAX (LENGTH a) (LENGTH b) in
       zero_extend m (n2v (v2n a + v2n b))
End

Definition bitwise_def:
   bitwise f v1 v2 =
     let m = MAX (LENGTH v1) (LENGTH v2) in
        MAP (UNCURRY f) (ZIP (fixwidth m v1, fixwidth m v2)) : bitstring
End

Definition bnot_def:   bnot = MAP (bool$~)
End
Definition bor_def:    bor  = bitwise (\/)
End
Definition band_def:   band = bitwise (/\)
End
Definition bxor_def:   bxor = bitwise (<>)
End

Definition bnor_def:   bnor = bitwise (\x y. ~(x \/ y))
End
Definition bxnor_def:   bxnor = bitwise (=)
End
Definition bnand_def:   bnand = bitwise (\x y. ~(x /\ y))
End

Definition replicate_def:
  replicate v n = FLAT (GENLIST (K v) n) : bitstring
End

(* ------------------------------------------------------------------------- *)

val wrw = srw_tac [boolSimps.LET_ss, fcpLib.FCP_ss, ARITH_ss]

Theorem extend_cons:
   !n c l. extend c (SUC n) l = c :: extend c n l
Proof
   Induct \\ metis_tac [extend_def]
QED

Theorem pad_left_extend:
    !n l c. PAD_LEFT c n l = extend c (n - LENGTH l) l
Proof
   ntac 2 strip_tac
   \\ Cases_on `n <= LENGTH l`
   >- lrw [listTheory.PAD_LEFT, DECIDE ``n <= l ==> (n - l = 0)``,
           Thm.CONJUNCT1 extend_def]
   \\ simp[listTheory.PAD_LEFT]
   \\ Induct_on `n` \\ rw []
   \\ Cases_on `LENGTH l = n`
   \\ lrw [bitTheory.SUC_SUB,
           extend_cons |> Q.SPEC `0`
                       |> SIMP_RULE std_ss [Thm.CONJUNCT1 extend_def]]
   \\ `SUC n - LENGTH l = SUC (n - LENGTH l)` by decide_tac
   \\ simp [extend_cons, listTheory.GENLIST_CONS]
QED

Theorem extend:
   (!n v. zero_extend n v = extend F (n - LENGTH v) v) /\
   (!n v. sign_extend n v = extend (HD v) (n - LENGTH v) v)
Proof
  simp [zero_extend_def, sign_extend_def, pad_left_extend]
QED

Theorem fixwidth:
    !n v.
      fixwidth n v =
        let l = LENGTH v in
           if l < n then
              extend F (n - l) v
           else
              DROP (l - n) v
Proof
   lrw [fixwidth_def, extend]
QED

Theorem fixwidth_REPLICATE:
  !len l. fixwidth len l =
    if LENGTH l <= len then REPLICATE (len - LENGTH l) F ++ l
    else DROP (LENGTH l - len) l
Proof
  rw[fixwidth, GSYM pad_left_extend, listTheory.PAD_LEFT] >>
  gvs[GSYM rich_listTheory.REPLICATE_GENLIST] >>
  `len = LENGTH l` by gvs[] >> pop_assum SUBST_ALL_TAC >> gvs[]
QED

Theorem fixwidth_id:
   !w. fixwidth (LENGTH w) w = w
Proof
  lrw [fixwidth_def]
QED

val fixwidth_id_imp = Theory.save_thm ("fixwidth_id_imp",
  metisLib.METIS_PROVE [fixwidth_id]
    ``!n w. (n = LENGTH w) ==> (fixwidth n w = w)``)

Theorem boolify_reverse_map:
    !v a. boolify a v = REVERSE (MAP (\n. n <> 0) v) ++ a
Proof
   Induct \\ lrw [boolify_def]
QED

Theorem bitify_reverse_map:
    !v a. bitify a v = REVERSE (MAP (\b. if b then 1 else 0) v) ++ a
Proof
   Induct \\ lrw [bitify_def]
QED

Theorem every_bit_bitify:
    !v. EVERY ($> 2) (bitify [] v)
Proof
   lrw [bitify_reverse_map, rich_listTheory.ALL_EL_REVERSE,
        listTheory.EVERY_MAP]
   \\ rw [listTheory.EVERY_EL] \\ rw []
QED

Theorem length_pad_left:
    !x n a. LENGTH (PAD_LEFT x n a) = if LENGTH a < n then n else LENGTH a
Proof
   lrw [listTheory.PAD_LEFT]
QED

Theorem length_pad_right:
    !x n a. LENGTH (PAD_RIGHT x n a) = if LENGTH a < n then n else LENGTH a
Proof
   lrw [listTheory.PAD_RIGHT]
QED

Theorem length_zero_extend:
   !n v. LENGTH v <= n ==> (LENGTH (zero_extend n v) = n)
Proof
  lrw [zero_extend_def, length_pad_left]
QED

Theorem length_sign_extend:
   !n v. LENGTH v <= n ==> (LENGTH (sign_extend n v) = n)
Proof
  lrw [sign_extend_def, length_pad_left]
QED

Theorem length_fixwidth:
   !n v. LENGTH (fixwidth n v) = n
Proof
  lrw [fixwidth_def, length_zero_extend]
QED

Theorem length_field:
   !h l v. LENGTH (field h l v) = SUC h - l
Proof
  rw [field_def, length_fixwidth]
QED

Theorem length_bitify:
   !v l. LENGTH (bitify l v) = LENGTH l + LENGTH v
Proof
  lrw [bitify_reverse_map]
QED

Theorem length_bitify_null:
   !v l. LENGTH (bitify [] v) = LENGTH v
Proof
  rw [length_bitify]
QED

Theorem length_shiftr:
    !v n. LENGTH (shiftr v n) = LENGTH v - n
Proof
   lrw [shiftr_def]
QED

Theorem length_rev_count_list:
   !n. LENGTH (rev_count_list n) = n
Proof
  Induct \\ lrw [rev_count_list_def]
QED

Theorem length_w2v:
   !w:'a word. LENGTH (w2v w) = dimindex(:'a)
Proof
  lrw [w2v_def]
QED

Theorem length_rotate:
   !v n. LENGTH (rotate v n) = LENGTH v
Proof
  simp [rotate_def, LET_THM]
  \\ srw_tac[][length_field]
  \\ full_simp_tac (std_ss++ARITH_ss)
       [DECIDE ``n <> 0n ==> (SUC (n - 1) = n)``,
        DECIDE ``n:num < l ==> (n + (l - n) = l)``,
        GSYM listTheory.LENGTH_NIL,
        arithmeticTheory.NOT_ZERO_LT_ZERO,
        arithmeticTheory.MOD_LESS]
QED

Theorem el_rev_count_list:
   !n i. i < n ==> (EL i (rev_count_list n) = n - 1 - i)
Proof
  Induct \\ lrw [rev_count_list_def]
QED

val el_bitify = Q.prove(
   `!v i a. i < LENGTH v ==>
            (EL (LENGTH v - (i + 1)) v = (EL i (bitify a v) = 1))`,
   lrw [bitify_def, bitify_reverse_map, rich_listTheory.EL_APPEND1,
        listTheory.EL_REVERSE, listTheory.EL_MAP, arithmeticTheory.PRE_SUB1])

Theorem el_zero_extend:
  !n i v. EL i (zero_extend n v) <=>
           n - LENGTH v <= i /\ EL (i - (n - LENGTH v)) v
Proof
  lrw [zero_extend_def, listTheory.PAD_LEFT]
  \\ Cases_on `i < n - LENGTH v`
  \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

Theorem el_sign_extend:
   !n i v. EL i (sign_extend n v) =
           if i < n - LENGTH v then
              EL 0 v
           else
              EL (i - (n - LENGTH v)) v
Proof
  lrw [sign_extend_def, listTheory.PAD_LEFT,
       rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

Theorem el_fixwidth:
   !i n w. i < n ==>
           (EL i (fixwidth n w) =
              if LENGTH w < n then
                 n - LENGTH w <= i /\ EL (i - (n - LENGTH w)) w
              else
                 EL (i + (LENGTH w - n)) w)
Proof
  lrw [fixwidth_def, el_zero_extend, rich_listTheory.EL_DROP]
QED

Theorem el_field:
  !v h l i. i < SUC h - l ==>
             (EL i (field h l v) <=>
              SUC h <= i + LENGTH v /\ EL (i + LENGTH v - SUC h) v)
Proof
  lrw [field_def, shiftr_def, el_fixwidth, rich_listTheory.EL_TAKE]
  \\ Cases_on `l < LENGTH v` \\ lrw []
  \\ `LENGTH v - SUC h < LENGTH v - l` by decide_tac
  \\ lrw [rich_listTheory.EL_TAKE]
QED

val shiftr_field = Q.prove(
   `!n l v. LENGTH l <> 0 ==> (shiftr l n = field (LENGTH l - 1) n l)`,
   rpt strip_tac
   \\ `SUC (LENGTH l - 1) - n = LENGTH (shiftr l n)`
   by (rw [length_shiftr] \\ decide_tac)
   \\ lrw [field_def, fixwidth_id])

Theorem el_w2v:
    !w: 'a word n.
      n < dimindex (:'a) ==> (EL n (w2v w) = w ' (dimindex (:'a) - 1 - n))
Proof
      lrw [w2v_def]
QED

Theorem el_shiftr:
  !i v n d.
       n < d /\ i < d - n /\ 0 < d ==>
       (EL i (shiftr (fixwidth d v) n) <=>
        d <= i + LENGTH v /\ EL (i + LENGTH v - d) v)
Proof
  simp_tac(std_ss++ARITH_ss)
    [shiftr_field, length_fixwidth, el_field, el_fixwidth,
     arithmeticTheory.ADD1] \\ rw[]
QED

Theorem shiftr_0:  !v. shiftr v 0 = v
Proof lrw [shiftr_def]
QED

Theorem field_fixwidth:
   !h v. field h 0 v = fixwidth (SUC h) v
Proof
  rw [field_def, shiftr_0]
QED

Theorem testbit:
   !b v. testbit b v = let n = LENGTH v in b < n /\ EL (n - 1 - b) v
Proof
  lrw [zero_extend_def, testbit_def, field_def, fixwidth_def, shiftr_def,
       listTheory.PAD_LEFT, arithmeticTheory.SUB_LEFT_SUB, bitTheory.SUC_SUB]
  \\ Induct_on `v`
  \\ lrw [listTheory.DROP_def]
  \\ lfs [arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL,
          arithmeticTheory.ADD1]
  >- (`b = LENGTH v` by decide_tac \\ lrw [])
  \\ imp_res_tac arithmeticTheory.LESS_ADD_1
  \\ lfs [REWRITE_RULE [arithmeticTheory.ADD1] listTheory.EL_restricted]
QED

Theorem testbit_geq_len:
    !v i. LENGTH v <= i ==> ~testbit i v
Proof
   simp [testbit, LET_THM]
QED

Theorem testbit_el:
    !v i. i < LENGTH v ==> (testbit i v = EL (LENGTH v - 1 - i) v)
Proof
   simp [testbit, LET_THM]
QED

Theorem bit_v2w:
  !n v. word_bit n (v2w v : 'a word) <=> n < dimindex(:'a) /\ testbit n v
Proof
  rw [v2w_def, wordsTheory.word_bit_def]
  \\ Cases_on `n < dimindex(:'a)`
  \\ wrw []
  \\ assume_tac wordsTheory.DIMINDEX_GT_0
  \\ `~(n <= dimindex(:'a) - 1)` by decide_tac
  \\ asm_rewrite_tac []
QED

Theorem word_index_v2w:
   !v i. (v2w v : 'a word) ' i =
         if i < dimindex(:'a) then
            testbit i v
         else
            FAIL $' ^(Term.mk_var ("index too large", Type.bool))
                 (v2w v : 'a word) i
Proof
  rw [wordsTheory.word_bit, bit_v2w, combinTheory.FAIL_THM]
QED

Theorem testbit_w2v:
   !n w. testbit n (w2v (w : 'a word)) = word_bit n w
Proof
  lrw [w2v_def, testbit, wordsTheory.word_bit_def]
  \\ Cases_on `n < dimindex(:'a)`
  \\ lrw []
  \\ assume_tac wordsTheory.DIMINDEX_GT_0
  \\ `~(n <= dimindex(:'a) - 1)` by decide_tac
  \\ asm_rewrite_tac []
QED

val word_bit_lem =
  wordsTheory.word_bit
    |> Q.SPECL [`w`, `dimindex(:'a) - 1 - i`]
    |> SIMP_RULE arith_ss [wordsTheory.DIMINDEX_GT_0,
          DECIDE ``0 < n ==> (0 < i + n)``]
    |> GEN_ALL

Theorem w2v_v2w:
  !v. w2v (v2w v : 'a word) = fixwidth (dimindex(:'a)) v
Proof
  lrw [w2v_def, bit_v2w, testbit, fixwidth_def, zero_extend_def,
       listTheory.PAD_LEFT, listTheory.LIST_EQ_REWRITE,
       rich_listTheory.EL_DROP, word_bit_lem]
  \\ Cases_on `x < dimindex(:'a) - LENGTH v`
  \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

Theorem v2w_w2v:
  !w. v2w (w2v w) = w
Proof
  wrw [w2v_def, v2w_def, testbit]
QED

Theorem v2w_append:
  v2w (xs ++ ys) = (v2w xs) << (LENGTH ys) || v2w ys
Proof
  wrw[word_bit,bit_v2w,word_bit_or,word_bit_lsl]
  \\ rw[testbit,rich_listTheory.EL_APPEND]
  \\ fs[SF DNF_ss]
QED

Theorem v2w_NIL:
  v2w [] = 0w
Proof
  wrw[v2w_def,testbit,word_0]
QED

Theorem v2w_T:
  v2w [T] = 1w
Proof
  wrw[v2w_def,testbit,n2w_def]
QED

Theorem v2w_F:
  v2w [F] = 0w
Proof
  wrw[v2w_def,testbit,n2w_def]
QED

Theorem v2w_thm:
  (v2w [] = 0w) /\
  (v2w (x :: xs) = (if x then ((1w << (LENGTH xs)) || v2w xs) else v2w xs))
Proof
  rw[]
  >- rw[v2w_NIL]
  >> simp_tac pure_ss [Once rich_listTheory.CONS_APPEND,v2w_append]
  >> rw[v2w_T,v2w_F]
QED

Theorem v2w_fixwidth:
   !v. v2w (fixwidth (dimindex(:'a)) v) = v2w v : 'a word
Proof
  wrw [v2w_def, testbit, length_fixwidth, el_fixwidth]
  \\ Cases_on `i < LENGTH v`
  \\ lrw []
QED

Theorem fixwidth_fixwidth:
   !n v. fixwidth n (fixwidth n v) = fixwidth n v
Proof
  lrw [fixwidth_def] \\ lfs [length_zero_extend]
QED

Theorem bitstring_nchotomy:
   !w:'a word. ?v. (w = v2w v)
Proof metis_tac [v2w_w2v]
QED

Theorem ranged_bitstring_nchotomy:
   !w:'a word. ?v. (w = v2w v) /\ (Abbrev (LENGTH v = dimindex(:'a)))
Proof
  strip_tac
  \\ qspec_then `w` STRUCT_CASES_TAC bitstring_nchotomy
  \\ qexists_tac `fixwidth (dimindex(:'a)) v`
  \\ rw [markerTheory.Abbrev_def, length_fixwidth, v2w_fixwidth]
QED

val BACKWARD_LIST_EQ_REWRITE = Q.prove(
  `!l1 l2. (l1 = l2) <=>
           (LENGTH l1 = LENGTH l2) /\
           !x. x < LENGTH l1 ==>
               (EL (LENGTH l1 - 1 - x) l1 = EL (LENGTH l1 - 1 - x) l2)`,
  lrw [listTheory.LIST_EQ_REWRITE]
  \\ eq_tac \\ lrw []
  \\ `LENGTH l1 - 1 - x < LENGTH l1` by decide_tac
  \\ res_tac
  \\ `x < LENGTH l1` by decide_tac
  \\ lfs []);

Theorem fixwidth_eq:
  !n v w. (fixwidth n v = fixwidth n w) =
           (!i. i < n ==> (testbit i v = testbit i w))
Proof
  lrw [el_fixwidth, testbit, length_fixwidth, BACKWARD_LIST_EQ_REWRITE]
  \\ rpt BasicProvers.FULL_CASE_TAC
  \\ lfs [DECIDE ``v < n ==> (n <= n + v - (i + 1) <=> i < v)``]
QED

Theorem v2w_11:
   !v w. (v2w v = v2w w : 'a word) =
         (fixwidth (dimindex(:'a)) v = fixwidth (dimindex(:'a)) w)
Proof
  wrw [wordsTheory.word_bit, bit_v2w, fixwidth_eq]
QED

(* ------------------------------------------------------------------------- *)

val take_id_imp =
   metisLib.METIS_PROVE [listTheory.TAKE_LENGTH_ID]
     ``!n w: 'a list. (n = LENGTH w) ==> (TAKE n w = w)``

Theorem field_concat_right:
    !h a b. (LENGTH b = SUC h) ==> (field h 0 (a ++ b) = b)
Proof
   lrw [field_def, shiftr_def, take_id_imp]
   \\ lrw [fixwidth_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem field_concat_left:
    !h l a b.
       l <= h /\ LENGTH b <= l ==>
       (field h l (a ++ b) = field (h - LENGTH b) (l - LENGTH b) a)
Proof
   srw_tac [][field_def, shiftr_def]
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ pop_assum kall_tac
   \\ pop_assum SUBST_ALL_TAC
   \\ lfs [listTheory.TAKE_APPEND1]
   \\ simp [DECIDE ``p + l <= h ==> (SUC h - (p + l) = SUC (h - l) - p)``]
QED

Theorem field_id_imp:
    !n v. (SUC n = LENGTH v) ==> (field n 0 v = v)
Proof
   metis_tac [fixwidth_id_imp, field_fixwidth]
QED

(* ------------------------------------------------------------------------- *)

Theorem shiftl_replicate_F:
    !v n. shiftl v n = v ++ replicate [F] n
Proof
   lrw [shiftl_def, replicate_def, listTheory.PAD_RIGHT]
   \\ Induct_on `n`
   \\ lrw [listTheory.GENLIST_CONS]
QED

(* ------------------------------------------------------------------------- *)

Theorem word_lsb_v2w:
  !v. word_lsb (v2w v) <=> v <> [] /\ LAST v
Proof
  lrw [wordsTheory.word_lsb_def, wordsTheory.word_bit, bit_v2w, testbit,
       rich_listTheory.LENGTH_NOT_NULL, rich_listTheory.NULL_EQ_NIL]
  \\ Cases_on `v = []`
  \\ rw [GSYM rich_listTheory.EL_PRE_LENGTH, arithmeticTheory.PRE_SUB1]
QED

Theorem word_msb_v2w:
   !v. word_msb (v2w v : 'a word) = testbit (dimindex(:'a) - 1) v
Proof
  lrw [wordsTheory.word_msb_def, wordsTheory.word_bit, bit_v2w]
QED

Theorem w2w_v2w:
  !v. w2w (v2w v : 'a word) : 'b word =
       v2w (fixwidth (if dimindex(:'b) < dimindex(:'a) then
                         dimindex(:'b)
                      else
                         dimindex(:'a)) v)
Proof
  wrw [wordsTheory.w2w]
  \\ Cases_on `i < dimindex(:'a)`
  \\ lrw [wordsTheory.word_bit, el_fixwidth, bit_v2w, testbit,
          length_fixwidth]
  \\ lfs [arithmeticTheory.NOT_LESS_EQUAL]
  >| [
    `dimindex (:'b) <= LENGTH v + dimindex (:'b) - (i + 1) <=> i < LENGTH v`
    by decide_tac,
    `dimindex (:'a) <= LENGTH v + dimindex (:'a) - (i + 1) <=> i < LENGTH v`
    by decide_tac]
  THEN simp []
QED

Theorem sw2sw_v2w:
   !v. sw2sw (v2w v : 'a word) : 'b word =
       if dimindex (:'a) < dimindex (:'b) then
          v2w (sign_extend (dimindex(:'b)) (fixwidth (dimindex(:'a)) v))
       else
          v2w (fixwidth (dimindex(:'b)) v)
Proof
  wrw [wordsTheory.sw2sw]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, word_msb_v2w,
          length_sign_extend, length_fixwidth, el_sign_extend, el_fixwidth]
  \\ lfs [arithmeticTheory.NOT_LESS,
          DECIDE ``0 < d ==> (v - 1 - (d - 1) = v - d)``]
  >- (Cases_on `i < LENGTH v` \\ lrw [])
  >- (Cases_on `LENGTH v = 0`
      \\ lrw [DECIDE ``0n < d ==> ~(d < 1)``, arithmeticTheory.LE_LT1])
  \\ Cases_on `i < LENGTH v` \\ lrw []
QED

Theorem n2w_v2n:
  !v. n2w (v2n v) = v2w v
Proof
  wrw [wordsTheory.word_bit, bit_v2w, wordsTheory.word_bit_n2w, v2n_def,
       testbit]
  \\ Cases_on `i < LENGTH v`
  \\ rw []
  >| [
    `i < LENGTH (bitify [] v)` by metis_tac [length_bitify_null]
    \\ qspecl_then [‘i’, ‘REVERSE (bitify [] v)’]
                   (mp_tac o SRULE[num_from_bin_list_def])
                   BIT_num_from_bin_list
    \\ rw [every_bit_bitify, el_bitify],
    match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
    \\ qspecl_then [`bitify [] v`, `2`] assume_tac l2n_lt
    \\ fs [arithmeticTheory.NOT_LESS, num_from_bin_list_def]
    \\ metis_tac [length_bitify_null, bitTheory.TWOEXP_MONO2,
                  arithmeticTheory.LESS_LESS_EQ_TRANS]
  ]
QED

val v2n_n2v_lem = Q.prove(
  `!l. EVERY ($> 2) l ==>
       (MAP ((\b. if b then 1 else 0) o (\n. n <> 0)) l = l)`,
  Induct \\ lrw [])

Theorem v2n_n2v:
   !n. v2n (n2v n) = n
Proof
  lrw [n2v_def, v2n_def, bitify_def, num_from_bin_list_def, l2n_def,
       num_to_bin_list_def, bitify_reverse_map, boolify_reverse_map,
       rich_listTheory.MAP_REVERSE, listTheory.MAP_MAP_o, v2n_n2v_lem,
       numposrepTheory.n2l_BOUND, numposrepTheory.l2n_n2l]
QED

Theorem v2w_n2v:
   !n. v2w (n2v n) = n2w n
Proof
  rewrite_tac [GSYM n2w_v2n, v2n_n2v]
QED

Theorem w2n_v2w:
   !v. w2n (v2w v : 'a word) = MOD_2EXP (dimindex(:'a)) (v2n v)
Proof
  rw [Once (GSYM n2w_v2n), wordsTheory.MOD_2EXP_DIMINDEX]
QED

Theorem v2n_lt:
   !v. v2n v < 2 ** LENGTH v
Proof
    metis_tac [v2n_def, length_bitify_null, num_from_bin_list_def,
               l2n_lt, DECIDE ``0 < 2n``]
QED

Theorem v2n_APPEND:
  !a b. v2n (a ++ b) = v2n b + (2 ** LENGTH b * v2n a)
Proof
  rw[v2n_def, bitify_reverse_map, listTheory.REVERSE_APPEND] >>
  gvs[num_from_bin_list_def, l2n_APPEND]
QED

Theorem v2n:
  v2n [] = 0 /\
  v2n (b::bs) = if b then 2 ** LENGTH bs + v2n bs else v2n bs
Proof
  rw[] >> once_rewrite_tac[rich_listTheory.CONS_APPEND]
  >- simp[v2n_def, bitify_reverse_map, l2n_def] >>
  once_rewrite_tac[v2n_APPEND] >> simp[] >>
  simp[v2n_def, bitify_reverse_map, l2n_def]
QED

(* ------------------------------------------------------------------------- *)

fun bitwise_tac x y =
  qabbrev_tac `l = ZIP (fixwidth (LENGTH ^x) v,fixwidth (LENGTH ^x) w)`
  \\ `LENGTH (fixwidth (LENGTH ^x) ^y) = LENGTH (fixwidth (LENGTH ^x) ^x)`
  by rewrite_tac [length_fixwidth]
  \\ `0 < LENGTH l`
  by (`0 < LENGTH ^x` by decide_tac
      \\ fs [Abbr `l`, listTheory.LENGTH_ZIP, length_fixwidth])
  \\ `arithmetic$- (LENGTH l) (i + 1n) < LENGTH l` by decide_tac
  \\ `arithmetic$- (LENGTH l) (i + 1) < LENGTH (fixwidth (LENGTH ^x) v)`
  by fs [Abbr `l`, listTheory.LENGTH_ZIP, length_fixwidth]
  \\ lrw [Abbr `l`, listTheory.LENGTH_ZIP, fixwidth_id, el_fixwidth,
          listTheory.EL_MAP,
          Q.ISPECL [`fixwidth (LENGTH ^x) v`, `fixwidth (LENGTH ^x) w`]
                   listTheory.EL_ZIP]
  \\ Cases_on `i < LENGTH ^y`
  \\ lrw []

val bitwise_tac =
  srw_tac [boolSimps.LET_ss, fcpLib.FCP_ss, ARITH_ss, boolSimps.CONJ_ss]
       [v2w_def, bitwise_def, length_fixwidth,
        testbit, arithmeticTheory.MAX_DEF, band_def, bor_def, bxor_def,
        wordsTheory.word_and_def, wordsTheory.word_or_def,
        wordsTheory.word_xor_def]
  >- (bitwise_tac ``w:bitstring`` ``v:bitstring``)
  \\ Cases_on `LENGTH w < LENGTH v`
  >- (bitwise_tac ``v:bitstring`` ``w:bitstring``)
  \\ `LENGTH v = LENGTH w` by decide_tac
  \\ rw [fixwidth_id]
  \\ Cases_on `LENGTH w = 0`
  >- fs [listTheory.LENGTH_NIL]
  \\ `arithmetic$- (LENGTH (ZIP (v,w))) (i + 1) < LENGTH (ZIP (v,w))`
  by lrw [listTheory.LENGTH_ZIP]
  \\ lrw [listTheory.LENGTH_ZIP, listTheory.EL_MAP, listTheory.EL_ZIP]
  \\ decide_tac

Theorem word_and_v2w:
   !v w. v2w v && v2w w = v2w (band v w)
Proof bitwise_tac
QED

Theorem word_or_v2w:
   !v w. v2w v || v2w w = v2w (bor v w)
Proof bitwise_tac
QED

Theorem word_xor_v2w:
   !v w. v2w v ?? v2w w = v2w (bxor v w)
Proof bitwise_tac
QED

fun bitwise_tac x y =
  qabbrev_tac `l = ZIP (fixwidth (dimindex(:'a)) v,fixwidth (dimindex(:'a)) w)`
  \\ `LENGTH (fixwidth (dimindex(:'a)) ^y) =
      LENGTH (fixwidth (dimindex(:'a)) ^x)`
  by rewrite_tac [length_fixwidth]
  \\ `arithmetic$- (LENGTH l) (i + 1n) < LENGTH l` by decide_tac
  \\ `arithmetic$- (LENGTH l) (i + 1) < LENGTH (fixwidth (LENGTH ^x) v)`
  by fs [Abbr `l`, listTheory.LENGTH_ZIP, length_fixwidth]
  \\ lrw [Abbr `l`, listTheory.LENGTH_ZIP, fixwidth_id, el_fixwidth,
          listTheory.EL_MAP,
          Q.ISPECL [`fixwidth (LENGTH ^x) v`, `fixwidth (LENGTH ^x) w`]
                   listTheory.EL_ZIP]
  \\ Cases_on `i < LENGTH ^y`
  \\ lrw []

val bitwise_tac =
  srw_tac [boolSimps.LET_ss, fcpLib.FCP_ss, ARITH_ss, boolSimps.CONJ_ss]
       [v2w_def, bitwise_def, length_fixwidth, fixwidth_fixwidth,
        testbit, arithmeticTheory.MAX_DEF, bxnor_def, bnand_def, bnor_def,
        wordsTheory.word_xnor_def, wordsTheory.word_nand_def,
        wordsTheory.word_nor_def,
        listTheory.LENGTH_ZIP, listTheory.EL_MAP, listTheory.EL_ZIP]
  \\ lrw [el_fixwidth, DECIDE ``0 < d ==> (d <= v + d - (i + 1) <=> i < v)``];

Theorem word_nand_v2w:
   !v w. v2w v ~&& (v2w w) : 'a word =
         v2w (bnand (fixwidth (dimindex(:'a)) v)
                    (fixwidth (dimindex(:'a)) w))
Proof bitwise_tac
QED

Theorem word_nor_v2w:
   !v w. v2w v ~|| (v2w w) : 'a word =
         v2w (bnor (fixwidth (dimindex(:'a)) v)
                   (fixwidth (dimindex(:'a)) w))
Proof bitwise_tac
QED

Theorem word_xnor_v2w:
   !v w. v2w v ~?? (v2w w) : 'a word =
         v2w (bxnor (fixwidth (dimindex(:'a)) v)
                    (fixwidth (dimindex(:'a)) w))
Proof bitwise_tac
QED

Theorem word_1comp_v2w:
   !v. word_1comp (v2w v : 'a word) = v2w (bnot (fixwidth (dimindex(:'a)) v))
Proof
  wrw [v2w_def, bnot_def, wordsTheory.word_1comp_def, testbit, el_fixwidth,
       length_fixwidth, listTheory.EL_MAP]
  \\ Cases_on `i < LENGTH v`
  \\ lrw []
QED

(* ------------------------------------------------------------------------- *)

Theorem word_lsl_v2w:
   !n v. word_lsl (v2w v : 'a word) n = v2w (shiftl v n)
Proof
  wrw [wordsTheory.word_lsl_def, shiftl_def, listTheory.PAD_RIGHT]
  \\ Cases_on `n <= i`
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, length_pad_right]
  >- (Cases_on `LENGTH v = 0` \\ lrw [rich_listTheory.EL_APPEND1])
  \\ lrw [rich_listTheory.EL_APPEND2]
QED

Theorem word_lsr_v2w:
  !n v. word_lsr (v2w v : 'a word) n =
         v2w (shiftr (fixwidth (dimindex(:'a)) v) n)
Proof
  wrw [wordsTheory.word_lsr_def, shiftr_def]
  \\ Cases_on `i + n < dimindex(:'a)`
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, length_fixwidth,
          rich_listTheory.EL_TAKE, el_fixwidth,
          DECIDE ``0 < d ==> (d <= v + d - (i + (n + 1)) <=> i + n < v)``]
QED

Theorem word_modify_v2w:
  !f v. word_modify f (v2w v : 'a word) =
         v2w (modify f (fixwidth (dimindex(:'a)) v))
Proof
  wrw [wordsTheory.word_modify_def]
  \\ lrw [modify_def, wordsTheory.word_bit, bit_v2w, testbit]
  \\ `LENGTH (rev_count_list (LENGTH (fixwidth (dimindex (:'a)) v))) =
      LENGTH (fixwidth (dimindex (:'a)) v)`
  by rewrite_tac [length_rev_count_list]
  \\ `LENGTH (ZIP
         (rev_count_list (LENGTH (fixwidth (dimindex (:'a)) v)),
          fixwidth (dimindex (:'a)) v)) = dimindex(:'a)`
  by metis_tac [listTheory.LENGTH_ZIP, length_fixwidth]
  \\ `dimindex (:'a) - (i + 1) <
      LENGTH (rev_count_list (LENGTH (fixwidth (dimindex (:'a)) v)))`
  by lrw [length_rev_count_list, length_fixwidth]
  \\ lrw [listTheory.EL_MAP, listTheory.EL_ZIP, el_rev_count_list,
          length_fixwidth, el_fixwidth,
          DECIDE ``0 < d ==> (d <= v + d - (i + 1) <=> i < v)``]
QED

Theorem word_bits_v2w:
  !h l v. word_bits h l (v2w v : 'a word) =
           v2w (field h l (fixwidth (dimindex(:'a)) v))
Proof
  wrw [wordsTheory.word_bits_def]
  \\ Cases_on `i + l < dimindex(:'a)`
  \\ lrw [wordsTheory.word_bit, bit_v2w, length_field, testbit]
  \\ Cases_on `i < SUC h - l`
  \\ lrw [el_field, length_fixwidth, el_fixwidth,
          DECIDE ``0 < d ==> (d <= v + d - (i + (l + 1)) <=> i + l < v)``]
QED

Theorem word_extract_v2w:
   !h l v. word_extract h l (v2w v : 'a word) =
           w2w (word_bits h l (v2w v : 'a word))
Proof
  rw [wordsTheory.word_extract_def]
QED

Theorem word_slice_v2w:
   !h l v. word_slice h l (v2w v : 'a word) =
           v2w (shiftl (field h l (fixwidth (dimindex(:'a)) v)) l)
Proof
  rw [wordsTheory.WORD_SLICE_THM, word_bits_v2w, word_lsl_v2w]
QED

val pad_left_T_or_F = Q.prove(
   `(v2w (PAD_LEFT F (dimindex (:'a)) [F]) = 0w : 'a word) /\
    (v2w (PAD_LEFT T (dimindex (:'a)) [T]) = -1w : 'a word)`,
   wrw [wordsTheory.WORD_NEG_1_T]
   \\ wrw [wordsTheory.word_bit, bit_v2w, testbit, listTheory.PAD_LEFT]
   \\ (Cases_on `dimindex (:'a) - (i + 1) <
                LENGTH (GENLIST (K F) (dimindex (:'a) - 1))`
   >| [
      pop_assum (fn th =>
         map_every assume_tac
           [th, REWRITE_RULE [listTheory.LENGTH_GENLIST] th])
      \\ lrw [rich_listTheory.EL_APPEND1, listTheory.EL_GENLIST],
      fs [arithmeticTheory.NOT_LESS, rich_listTheory.EL_APPEND2]
      \\ `i = 0` by decide_tac
      \\ lrw []
   ]))

val hd_shiftr =
  el_shiftr
    |> Q.SPEC `0`
    |> SIMP_RULE (arith_ss++boolSimps.CONJ_ss) [listTheory.EL]

Theorem word_asr_v2w:
  !n v. word_asr (v2w v : 'a word) n =
         let l = fixwidth (dimindex(:'a)) v in
            v2w (sign_extend (dimindex(:'a))
                (if dimindex(:'a) <= n then [HD l] else shiftr l n))
Proof
  lrw [wordsTheory.ASR_LIMIT, word_msb_v2w]
  >| [
    simp_tac (arith_ss++boolSimps.LET_ss)
         [GSYM (Thm.CONJUNCT1 rich_listTheory.EL), el_fixwidth,
          wordsTheory.DIMINDEX_GT_0, testbit, sign_extend_def]
    \\ Cases_on `LENGTH v = 0`
    \\ simp [pad_left_T_or_F]
    \\ rw [pad_left_T_or_F, DECIDE ``~(v < d) <=> d < v + 1``,
           DECIDE ``0 < d ==> (v - 1 - (d - 1) = v - d)``],
    simp [wordsTheory.word_asr, word_msb_v2w, word_lsr_v2w, testbit]
    \\ Cases_on `LENGTH v = 0`
    \\ imp_res_tac listTheory.LENGTH_NIL
    \\ lrw [hd_shiftr, length_shiftr, length_fixwidth, sign_extend_def,
            wordsTheory.word_asr, listTheory.PAD_LEFT]
    \\ fsrw_tac [ARITH_ss]
          [arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL,
           word_or_def, word_slice_def]
    \\ wrw [wordsTheory.word_bit, bit_v2w, testbit, length_shiftr,
            length_fixwidth, el_shiftr,
            SIMP_RULE std_ss [wordsTheory.word_bit] WORD_NEG_1_T]
    \\ Cases_on `dimindex (:'a) - (i + 1) < n`
    \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2, el_shiftr]
  ]
QED

Theorem word_ror_v2w:
  !n v. word_ror (v2w v : 'a word) n =
         v2w (rotate (fixwidth (dimindex(:'a)) v) n)
Proof
  wrw [wordsTheory.word_ror, word_or_def, word_lsl_def, word_bits_def,
       rotate_def, length_fixwidth, v2w_fixwidth]
  \\ `?p. dimindex(:'a) = i + p + 1`
  by metis_tac [arithmeticTheory.LESS_ADD_1, arithmeticTheory.ADD_ASSOC]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit]
  \\ Cases_on `n MOD (i + (p + 1)) = 0`
  \\ rw [length_field, arithmeticTheory.ADD1]
  >- (`LENGTH (field 0 0 (fixwidth (i + (p + 1)) v)) = 1`
      by rw [length_field]
      \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, el_field, length_fixwidth,
              el_fixwidth, rich_listTheory.EL_APPEND2, arithmeticTheory.ADD1,
              DECIDE ``i + (p + 1) <= p + v <=> i < v``])
  \\ qabbrev_tac `q = n MOD (i + (p + 1))`
  \\ `q < i + p + 1` by lrw [Abbr `q`, arithmeticTheory.MOD_LESS]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit]
  \\ Cases_on `p < q`
  \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2, length_field]
  >- (lrw [el_field, length_fixwidth, arithmeticTheory.ADD1, el_fixwidth]
      \\ Cases_on `LENGTH v = 0`
      \\ lrw [DECIDE ``i + (p + 1) <= i + (2 * p + (v + 1)) - q  <=>
                       i < i + (p + (v + 1)) - q``])
  \\ Cases_on `i + q < dimdinex(:'a)`
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, el_field, length_fixwidth,
          arithmeticTheory.ADD1, el_fixwidth,
          DECIDE ``i + (p + 1) <= p + v - q <=> i + q < v``]
QED

Theorem word_ror_alt:
  !r a. (a : 'a word) #>> r =
    let d = dimindex (:'a) in a << (d - r MOD d) || a >>> (r MOD d)
Proof
  rw[] >> qspec_then `a` assume_tac ranged_bitstring_nchotomy >> gvs[] >>
  simp[word_ror_v2w, rotate_def] >> IF_CASES_TAC >> gvs[fixwidth_id] >>
  qabbrev_tac `r' = r MOD dimindex (:'a)` >>
  `r' < dimindex (:'a)` by (unabbrev_all_tac >> gvs[]) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  simp[word_lsl_v2w, word_lsr_v2w, rotate_def, word_or_v2w] >>
  simp[Once v2w_11] >> simp[field_def, arithmeticTheory.ADD1] >>
  `shiftr v 0 = v` by simp[shiftr_def] >> simp[] >>
  `~(LENGTH v < r MOD LENGTH v)` by (
    simp[arithmeticTheory.NOT_LESS] >>
    irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
    simp[arithmeticTheory.MOD_LESS]) >>
  rewrite_tac[fixwidth] >> simp[length_shiftr] >>
  qmatch_goalsub_abbrev_tac `bor a b` >>
  `~(LENGTH (bor a b) < LENGTH v)` by (
    unabbrev_all_tac >> rewrite_tac[bor_def, bitwise_def] >>
    simp[length_shiftr, shiftl_def, length_fixwidth, length_pad_right]) >>
  unabbrev_all_tac >>
  simp[bor_def, bitwise_def, shiftl_def, shiftr_def,
       listTheory.PAD_LEFT, listTheory.PAD_RIGHT, arithmeticTheory.MAX_DEF] >>
  simp[fixwidth_REPLICATE, GSYM listTheory.MAP_DROP,
       GSYM listTheory.ZIP_DROP, listTheory.DROP_APPEND] >>
  `dimindex (:'a) - r' - dimindex (:'a) = 0` by simp[] >> simp[] >>
  rw[listTheory.LIST_EQ_REWRITE, listTheory.EL_DROP, listTheory.EL_MAP, listTheory.EL_TAKE,
     listTheory.EL_ZIP, listTheory.EL_APPEND_EQN, rich_listTheory.EL_REPLICATE] >> rw[] >>
  AP_THM_TAC >> AP_TERM_TAC >> rw[]
QED

Theorem word_reverse_v2w:
  !v. word_reverse (v2w v : 'a word) =
       v2w (REVERSE (fixwidth (dimindex(:'a)) v))
Proof
  wrw [wordsTheory.word_reverse_def]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, length_fixwidth,
          listTheory.EL_REVERSE, DECIDE ``PRE (i + 1) = i``]
  \\ lrw [el_fixwidth, DECIDE ``0 < d ==> (d <= i + v <=> d < i + (v + 1))``]
  \\ Cases_on `LENGTH v = 0`
  \\ lrw []
QED

Theorem word_join_v2w:
   !v1 v2. FINITE univ(:'a) /\ FINITE univ(:'b) ==>
           (word_join (v2w v1 : 'a word) (v2w v2 : 'b word) =
            v2w (v1 ++ fixwidth (dimindex(:'b)) v2))
Proof
  wrw [wordsTheory.word_join_index, fcpTheory.index_sum]
  \\ wrw [wordsTheory.word_bit, bit_v2w, testbit, length_fixwidth,
          rich_listTheory.EL_APPEND2, fcpTheory.index_sum]
  \\ lrw [el_fixwidth, DECIDE ``0 < d ==> (d <= v + d - (i + 1) <=> i < v)``]
  \\ Cases_on `LENGTH v1 = 0` \\ lrw [rich_listTheory.EL_APPEND1]
QED

Theorem word_concat_v2w:
   !v1 v2. FINITE univ(:'a) /\ FINITE univ(:'b) ==>
           (word_concat (v2w v1 : 'a word) (v2w v2 : 'b word) : 'c word =
            v2w (fixwidth (MIN (dimindex(:'c)) (dimindex(:'a) + dimindex(:'b)))
                          (v1 ++ fixwidth (dimindex(:'b)) v2)))
Proof
  lrw [wordsTheory.word_concat_def, word_join_v2w, w2w_v2w,
       arithmeticTheory.MIN_DEF, fcpTheory.index_sum]
QED

Theorem word_join_v2w_rwt:
   !v1 v2. word_join (v2w v1 : 'a word) (v2w v2 : 'b word) =
           if FINITE univ(:'a) /\ FINITE univ(:'b) then
              v2w (v1 ++ fixwidth (dimindex(:'b)) v2)
           else
              FAIL $word_join ^(Term.mk_var("bad domain", Type.bool))
                (v2w v1 : 'a word) (v2w v2 : 'b word)
Proof
  rw [word_join_v2w, combinTheory.FAIL_THM]
QED

Theorem word_concat_v2w_rwt:
   !v1 v2.
      word_concat (v2w v1 : 'a word) (v2w v2 : 'b word) : 'c word =
        if FINITE univ(:'a) /\ FINITE univ(:'b) then
           v2w (fixwidth (MIN (dimindex(:'c)) (dimindex(:'a) + dimindex(:'b)))
                         (v1 ++ fixwidth (dimindex(:'b)) v2))
        else
           FAIL $word_concat ^(Term.mk_var("bad domain", Type.bool))
             (v2w v1 : 'a word) (v2w v2 : 'b word)
Proof
  rw [word_concat_v2w, combinTheory.FAIL_THM]
QED

val genlist_fixwidth = Q.prove(
   `!d v. 0 < d ==>
          (GENLIST (\i. (d < i + (LENGTH v + 1) /\ 0 < LENGTH v) /\
                        EL (LENGTH v - 1 - (d - (i + 1))) v) d =
          fixwidth d v)`,
   lrw [listTheory.LIST_EQ_REWRITE, length_fixwidth, el_fixwidth]
   \\ Cases_on `LENGTH v = 0`
   \\ lrw [DECIDE ``0 < d ==> (d <= x + v <=> d < x + (v + 1))``]);

Theorem word_reduce_v2w:
   !f v. word_reduce f (v2w v : 'a word) =
         let l = fixwidth (dimindex(:'a)) v in
            v2w [FOLDL f (HD l) (TL l)] : 1 word
Proof
  wrw [word_reduce_def]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit]
  \\ match_mp_tac listTheory.FOLDL_CONG
  \\ lrw [genlist_fixwidth]
QED

val reduce_and_v2w =
   wordsTheory.reduce_and_def
     |> Rewrite.REWRITE_RULE [boolTheory.FUN_EQ_THM]
     |> Q.SPEC `v2w v`
     |> Drule.GEN_ALL
     |> Lib.curry Theory.save_thm "reduce_and_v2w"

val reduce_or_v2w =
   wordsTheory.reduce_or_def
     |> Rewrite.REWRITE_RULE [boolTheory.FUN_EQ_THM]
     |> Q.SPEC `v2w v`
     |> Drule.GEN_ALL
     |> Lib.curry Theory.save_thm "reduce_or_v2w"

(* ------------------------------------------------------------------------- *)

Theorem extract_v2w:
   !h l v.
     (LENGTH v <= dimindex(:'a)) /\ (dimindex(:'b) = SUC h - l) /\
     dimindex(:'b) <= dimindex(:'a) ==>
     ((h >< l) (v2w v : 'a word) : 'b word = v2w (field h l v))
Proof
  lrw [word_extract_v2w, word_bits_v2w, fixwidth_fixwidth, fixwidth_eq,
       testbit, w2w_v2w, length_shiftr, length_fixwidth, length_field, v2w_11]
  \\ `(SUC h - (i + (l + 1))) < (SUC h - l)` by decide_tac
  \\ qspecl_then [`(SUC h - (i + (l + 1)))`, `(SUC h - l)`] imp_res_tac
        el_fixwidth
  \\ ntac 2 (pop_assum (kall_tac))
  \\ pop_assum (qspec_then `(field h l (fixwidth (dimindex (:'a)) v))`
        SUBST1_TAC)
  \\ simp [length_field, el_field, length_fixwidth, el_fixwidth]
  \\ Cases_on `EL (LENGTH v - (i + (l + 1))) v`
  \\ lrw []
QED

val DROP_LAST = Q.prove(
   `!l. ~NULL l ==> (DROP (LENGTH l - 1) l = [LAST l])`,
   rw[rich_listTheory.DROP_LASTN,arithmeticTheory.SUB_LEFT_SUB,
      rich_listTheory.LASTN_1,rich_listTheory.NULL_EQ_NIL]
   \\ `(LENGTH l = 0) \/ (LENGTH l = 1)` by decide_tac
   \\ fs[listTheory.LENGTH_EQ_NUM_compute,rich_listTheory.LASTN_1]);

Theorem word_bit_last_shiftr:
  !i v. i < dimindex(:'a) ==>
         (word_bit i (v2w v : 'a word) =
          let l = shiftr v i in ~NULL l /\ LAST l)
Proof
  lrw [bit_v2w, testbit_def, field_def, DECIDE ``SUC i - i = 1``, fixwidth_def]
  >- lfs [listTheory.PAD_LEFT, zero_extend_def]
  \\ `LENGTH (shiftr v i) <> 0` by (strip_tac \\ gvs[])
  \\ lfs [GSYM listTheory.NULL_LENGTH, DROP_LAST]
QED

(* ------------------------------------------------------------------------- *)

Theorem ops_to_v2w:
    (!v n. v2w v || n2w n = v2w v || v2w (n2v n)) /\
    (!v n. n2w n || v2w v = v2w (n2v n) || v2w v) /\
    (!v n. v2w v && n2w n = v2w v && v2w (n2v n)) /\
    (!v n. n2w n && v2w v = v2w (n2v n) && v2w v) /\
    (!v n. v2w v ?? n2w n = v2w v ?? v2w (n2v n)) /\
    (!v n. n2w n ?? v2w v = v2w (n2v n) ?? v2w v) /\
    (!v n. v2w v ~|| n2w n = v2w v ~|| v2w (n2v n)) /\
    (!v n. n2w n ~|| v2w v = v2w (n2v n) ~|| v2w v) /\
    (!v n. v2w v ~&& n2w n = v2w v ~&& v2w (n2v n)) /\
    (!v n. n2w n ~&& v2w v = v2w (n2v n) ~&& v2w v) /\
    (!v n. v2w v ~?? n2w n = v2w v ~?? v2w (n2v n)) /\
    (!v n. n2w n ~?? v2w v = v2w (n2v n) ~?? v2w v) /\
    (!v n. (v2w v : 'a word) @@ (n2w n : 'b word) =
           (v2w v : 'a word) @@ (v2w (n2v n) : 'b word)) /\
    (!v n. (n2w n : 'a word) @@ (v2w v : 'b word) =
           (v2w (n2v n) : 'a word) @@ (v2w v : 'b word)) /\
    (!v n. word_join (v2w v) (n2w n) = word_join (v2w v) (v2w (n2v n))) /\
    (!v n. word_join (n2w n) (v2w v) = word_join (v2w (n2v n)) (v2w v))
Proof
   rewrite_tac [v2w_n2v]
QED

Theorem ops_to_n2w:
   (!v. word_2comp (v2w v) = word_2comp (n2w (v2n v))) /\
   (!v. word_log2 (v2w v) = word_log2 (n2w (v2n v))) /\
   (!v n. (v2w v = n2w n : 'a word) = (n2w (v2n v) = n2w n : 'a word)) /\
   (!v n. (n2w n = v2w v : 'a word) = (n2w n = n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v + w) = (n2w (v2n v) + w)) /\
   (!v w. (w + v2w v) = (w + n2w (v2n v))) /\
   (!v w. (v2w v - w) = (n2w (v2n v) - w)) /\
   (!v w. (w - v2w v) = (w - n2w (v2n v))) /\
   (!v w. (v2w v * w) = (n2w (v2n v) * w)) /\
   (!v w. (w * v2w v) = (w * n2w (v2n v))) /\
   (!v w. (v2w v / w) = (n2w (v2n v) / w)) /\
   (!v w. (w / v2w v) = (w / n2w (v2n v))) /\
   (!v w. (v2w v // w) = (n2w (v2n v) // w)) /\
   (!v w. (w // v2w v) = (w // n2w (v2n v))) /\
   (!v w. word_mod (v2w v) w = word_mod (n2w (v2n v)) w) /\
   (!v w. word_mod w (v2w v) = word_mod w (n2w (v2n v))) /\
   (!v w. (v2w v < w : 'a word) = (n2w (v2n v) < w : 'a word)) /\
   (!v w. (w < v2w v : 'a word) = (w < n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v > w : 'a word) = (n2w (v2n v) > w : 'a word)) /\
   (!v w. (w > v2w v : 'a word) = (w > n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v <= w : 'a word) = (n2w (v2n v) <= w : 'a word)) /\
   (!v w. (w <= v2w v : 'a word) = (w <= n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v >= w : 'a word) = (n2w (v2n v) >= w : 'a word)) /\
   (!v w. (w >= v2w v : 'a word) = (w >= n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v <+ w : 'a word) = (n2w (v2n v) <+ w : 'a word)) /\
   (!v w. (w <+ v2w v : 'a word) = (w <+ n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v >+ w : 'a word) = (n2w (v2n v) >+ w : 'a word)) /\
   (!v w. (w >+ v2w v : 'a word) = (w >+ n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v <=+ w : 'a word) = (n2w (v2n v) <=+ w : 'a word)) /\
   (!v w. (w <=+ v2w v : 'a word) = (w <=+ n2w (v2n v) : 'a word)) /\
   (!v w. (v2w v >=+ w : 'a word) = (n2w (v2n v) >=+ w : 'a word)) /\
   (!v w. (w >=+ v2w v : 'a word) = (w >=+ n2w (v2n v) : 'a word))
Proof
   rewrite_tac [n2w_v2n]
QED

(* ------------------------------------------------------------------------- *)

val () = bossLib.export_rewrites
   ["length_w2v", "length_fixwidth", "length_field",
    "length_bitify", "length_shiftr", "length_rotate",
    "v2w_w2v", "v2n_n2v", "v2w_n2v",
    "fixwidth_fixwidth", "fixwidth_id_imp"]

val _ = computeLib.add_persistent_funs [
     "testbit",
     "ops_to_v2w",
     "ops_to_n2w",
     "fixwidth",
     "extend",
     "v2w_11",
     "bit_v2w",
     "w2n_v2w",
     "w2v_v2w",
     "w2w_v2w",
     "sw2sw_v2w",
     "word_index_v2w",
     "word_lsl_v2w",
     "word_lsr_v2w",
     "word_asr_v2w",
     "word_ror_v2w",
     "word_1comp_v2w",
     "word_and_v2w",
     "word_or_v2w",
     "word_xor_v2w",
     "word_nand_v2w",
     "word_nor_v2w",
     "word_xnor_v2w",
     "word_lsb_v2w",
     "word_msb_v2w",
     "word_reverse_v2w",
     "word_modify_v2w",
     "word_bits_v2w",
     "word_extract_v2w",
     "word_slice_v2w",
     "word_join_v2w_rwt",
     "word_concat_v2w_rwt",
     "word_reduce_v2w",
     "reduce_and_v2w",
     "reduce_or_v2w"
  ]

(*

time (List.map EVAL)
  [``(v2w [T;T;F;F] : word8) ' 2``,
   ``word_lsb (v2w [T;T;F;F] : word8)``,
   ``word_msb (v2w [T;T;F;F] : word8)``,
   ``word_bit 2 (v2w [T;T;F;F] : word8)``,
   ``word_bits 5 2 (v2w [T;T;F;F] : word8)``,
   ``word_slice 5 2 (v2w [T;T;F;F] : word8)``,
   ``word_extract 5 2 (v2w [T;T;F;F] : word8) : word4``,
   ``word_reverse (v2w [T;T;F;F] : word8)``,
   ``word_replicate 2 (v2w [T;T;F;F] : word8) : word16``,

   ``reduce_and (v2w [T;T;F;F] : word8)``,
   ``reduce_or (v2w [T;T;F;F] : word8)``,
   ``reduce_xor (v2w [T;T;F;F] : word8)``,
   ``reduce_nand (v2w [T;T;F;F] : word8)``,
   ``reduce_nor (v2w [T;T;F;F] : word8)``,
   ``reduce_xnor (v2w [T;T;F;F] : word8)``,

   ``(v2w [T;T;F;F] : word4) #>> 3``,

   ``(v2w [T;T;F;F] : word8) >>> 2``,
   ``(v2w [T;T;F;F] : word8) << 2``,
   ``(v2w [T;T;F;F] : word8) >> 2``,
   ``(v2w [T;F;F;F;T;T;F;F] : word8) >> 2``,
   ``(v2w [T;T;F;F] : word8) #>> 3``,
   ``(v2w [T;T;F;F] : word8) #<< 2``,

   ``word_modify (\i b. b \/ ODD i) (v2w [T;T;F;F] : word8)``,

   ``~(v2w [T;T;F;F] : word8)``,
   ``-(v2w [T;T;F;F] : word8)``,
   ``word_log2 (v2w [T;T;F;F] : word8)``,
   ``word_log2 (v2w [] : word8)``,

   ``w2w (v2w [T;T;F;F] : word8) : word12``,
   ``w2w (v2w [T;T;F;F] : word8) : word6``,

   ``sw2sw (v2w [T;T;F;F] : word8) : word12``,
   ``sw2sw (v2w [T;T;F;F] : word8) : word6``,

   ``sw2sw (v2w [T;F;F;F;T;T;F;F] : word8) : word12``,
   ``sw2sw (v2w [T;F;F;F;T;T;F;F] : word8) : word6``,

   ``((v2w [T;T;F;F]:word4) @@ (v2w [T;F;T;F]:word4)) : word8``,
   ``((v2w [T;T;F;F]:word4) @@ (10w:word4)) : word8``,
   ``((12w:word4) @@ (v2w [T;F;T;F]:word4)) : word8``,

   ``v2w [T;T;F;F] = v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] = 10w : word8``,
   ``12w = v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] + v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] + 10w : word8``,
   ``12w + v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] - v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] - 10w : word8``,
   ``12w - v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] * v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] * 10w : word8``,
   ``12w * v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] / v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] / 10w : word8``,
   ``12w / v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] // v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] // 10w : word8``,
   ``12w // v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] < v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] < 10w : word8``,
   ``12w < v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] > v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] > 10w : word8``,
   ``12w > v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] && v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] && 10w : word8``,
   ``12w && v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] || v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] || 10w : word8``,
   ``12w || v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] ?? v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] ?? 10w : word8``,
   ``12w ?? v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] ~&& v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] ~&& 10w : word8``,
   ``12w ~&& v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] ~|| v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] ~|| 10w : word8``,
   ``12w ~|| v2w [T;F;T;F] : word8``,

   ``v2w [T;T;F;F] ~?? v2w [T;F;T;F] : word8``,
   ``v2w [T;T;F;F] ~?? 10w : word8``,
   ``12w ~?? v2w [T;F;T;F] : word8``]

*)

(* ------------------------------------------------------------------------- *)

