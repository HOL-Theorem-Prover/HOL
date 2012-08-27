(* ========================================================================= *)
(* FILE          : bitstringScript.sml                                       *)
(* DESCRIPTION   : Boolean lists as Bitstrings                               *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* ========================================================================= *)

open HolKernel boolLib bossLib;
open bitTheory wordsTheory fcpLib;
open lcsymtacs wordsLib;
open numposrepTheory

val _ = new_theory "bitstring";

(* ------------------------------------------------------------------------- *)

(* MSB is head of list, e.g. [T, F] represents 2 *)

val _ = Parse.type_abbrev ("bitstring", ``:bool list``);

val extend_def = Define`
   (extend _ 0 l = l) /\
   (extend c (SUC n) l = extend c n (c::l))`;

val boolify_def = Define`
  (boolify a [] = a) /\
  (boolify a (n :: l) = boolify ((n <> 0)::a) l)`;

val bitify_def = Define`
  (bitify a [] = a) /\
  (bitify a (F :: l) = bitify (0::a) l) /\
  (bitify a (T :: l) = bitify (1::a) l)`;

val n2v_def = Define`
  n2v n =
    if n = 0 then
      [F]
    else let w = LOG2 n in
      PAD_LEFT F (w + 1) (boolify [] (num_to_bin_list (BITS w 0 n)))`;

val v2n_def = Define`
  v2n l = num_from_bin_list (bitify [] l)`;

val s2v_def = Define`
  s2v = MAP (\c. (c = #"1") \/ (c = #"T"))`;

val v2s_def = Define`
  v2s = MAP (\b. if b then #"1" else #"0")`;

val zero_extend_def = zDefine`
  zero_extend n v = PAD_LEFT F n v`;

val sign_extend_def = zDefine`
  sign_extend n v = PAD_LEFT (HD v) n v`;

val shiftl_def = Define`
  shiftl v m = PAD_RIGHT F (LENGTH v + m) v`;

val shiftr_def = Define`
  shiftr v m = TAKE (LENGTH v - m) v`;

val fixwidth_def = zDefine`
  fixwidth n v =
     let l = LENGTH v in
       if l < n then
          zero_extend n v
       else
          DROP (l - n) v`;

val field_def = Define`
  field h l v = fixwidth (SUC h - l) (shiftr v l)`;

val testbit_def = zDefine`
  testbit b v = (field b b v = [T])`;

val w2v_def = Define`
  w2v (w : 'a word) =
    GENLIST (\i. w ' (dimindex(:'a) - 1 - i)) (dimindex(:'a))`;

val v2w_def = zDefine`
  v2w v : 'a word = FCP i. testbit i v`;

val rev_count_list_def = Define`
  rev_count_list n = GENLIST (\i. n - 1 - i) n`;

val modify_def = Define`
  modify f (v : bitstring) =
    MAP (UNCURRY f) (ZIP (rev_count_list (LENGTH v), v)) : bitstring`;

val field_insert_def = Define`
  field_insert h l s =
    modify (\i. COND (l <= i /\ i <= h) (testbit (i - l) s))`;

val add_def = Define`
   add a b =
     let m = MAX (LENGTH a) (LENGTH b) in
       zero_extend m (n2v (v2n a + v2n b))`;

val bitwise_def = Define`
   bitwise f v1 v2 =
     let m = MAX (LENGTH v1) (LENGTH v2) in
        MAP (UNCURRY f) (ZIP (fixwidth m v1, fixwidth m v2)) : bitstring`;

val bnot_def = Define `bnot = MAP (bool$~)`;
val bor_def  = Define `bor  = bitwise (\/)`;
val band_def = Define `band = bitwise (/\)`;
val bxor_def = Define `bxor = bitwise (<>)`;

val bnor_def = Define `bnor = bitwise (\x y. ~(x \/ y))`;
val bxnor_def = Define `bxnor = bitwise (=)`;
val bnand_def = Define `bnand = bitwise (\x y. ~(x /\ y))`;

val replicate_def = Define`
  replicate v n = FLAT (GENLIST (K v) n) : bitstring`;

(* ------------------------------------------------------------------------- *)

infix \\
val op \\ = op THEN;

val wrw = srw_tac [boolSimps.LET_ss, fcpLib.FCP_ss, ARITH_ss]

val extend_cons = Q.store_thm("extend_cons",
  `!n c l. extend c (SUC n) l = c :: extend c n l`,
   Induct \\ metis_tac [extend_def]);

val pad_left_extend = Q.store_thm("pad_left_extend",
   `!n l c. PAD_LEFT c n l = extend c (n - LENGTH l) l`,
   ntac 2 strip_tac
   \\ Cases_on `n <= LENGTH l`
   >- lrw [listTheory.PAD_LEFT, DECIDE ``n <= l ==> (n - l = 0)``,
           Thm.CONJUNCT1 extend_def]
   \\ Induct_on `n` \\ lrw [listTheory.PAD_LEFT]
   \\ Cases_on `LENGTH l = n`
   \\ lrw [bitTheory.SUC_SUB,
           extend_cons |> Q.SPEC `0`
                       |> SIMP_RULE std_ss [Thm.CONJUNCT1 extend_def]]
   \\ `SUC n - LENGTH l = SUC (n - LENGTH l)` by decide_tac
   \\ `LENGTH l < n` by decide_tac
   \\ fs [extend_cons, listTheory.PAD_LEFT, listTheory.GENLIST_CONS,
          DECIDE ``l < n ==> ~(n <= l : num)``]);

val extend = Q.store_thm("extend",
  `(!n v. zero_extend n v = extend F (n - LENGTH v) v) /\
   (!n v. sign_extend n v = extend (HD v) (n - LENGTH v) v)`,
  simp [zero_extend_def, sign_extend_def, pad_left_extend])

val fixwidth = Q.store_thm("fixwidth",
   `!n v.
      fixwidth n v =
        let l = LENGTH v in
           if l < n then
              extend F (n - l) v
           else
              DROP (l - n) v`,
   lrw [fixwidth_def, extend]);

val fixwidth_id = Q.store_thm("fixwidth_id",
  `!w. fixwidth (LENGTH w) w = w`,
  lrw [fixwidth_def]);

val fixwidth_id_imp = Theory.save_thm ("fixwidth_id_imp",
  metisLib.METIS_PROVE [fixwidth_id]
    ``!n w. (n = LENGTH w) ==> (fixwidth n w = w)``)

val boolify_reverse_map = Q.store_thm("boolify_reverse_map",
   `!v a. boolify a v = REVERSE (MAP (\n. n <> 0) v) ++ a`,
   Induct \\ lrw [boolify_def]);

val bitify_reverse_map = Q.store_thm("bitify_reverse_map",
   `!v a. bitify a v = REVERSE (MAP (\b. if b then 1 else 0) v) ++ a`,
   Induct \\ lrw [bitify_def]);

val every_bit_bitify = Q.store_thm("every_bit_bitify",
   `!v. EVERY ($> 2) (bitify [] v)`,
   lrw [bitify_reverse_map, rich_listTheory.ALL_EL_REVERSE,
        listTheory.EVERY_MAP]
   \\ rw [listTheory.EVERY_EL] \\ rw []);

val length_pad_left = Q.store_thm("length_pad_left",
   `!x n a. LENGTH (PAD_LEFT x n a) = if LENGTH a < n then n else LENGTH a`,
   lrw [listTheory.PAD_LEFT]);

val length_pad_right = Q.store_thm("length_pad_right",
   `!x n a. LENGTH (PAD_RIGHT x n a) = if LENGTH a < n then n else LENGTH a`,
   lrw [listTheory.PAD_RIGHT]);

val length_zero_extend = Q.store_thm("length_zero_extend",
  `!n v. LENGTH v < n ==> (LENGTH (zero_extend n v) = n)`,
  lrw [zero_extend_def, length_pad_left]);

val length_sign_extend = Q.store_thm("length_sign_extend",
  `!n v. LENGTH v < n ==> (LENGTH (sign_extend n v) = n)`,
  lrw [sign_extend_def, length_pad_left]);

val length_fixwidth = Q.store_thm("length_fixwidth",
  `!n v. LENGTH (fixwidth n v) = n`,
  lrw [fixwidth_def, length_zero_extend]);

val length_field = Q.store_thm("length_field",
  `!h l v. LENGTH (field h l v) = SUC h - l`,
  rw [field_def, length_fixwidth]);

val length_bitify = Q.store_thm("length_bitify",
  `!v l. LENGTH (bitify l v) = LENGTH l + LENGTH v`,
  lrw [bitify_reverse_map]);

val length_bitify_null = Q.store_thm("length_bitify_null",
  `!v l. LENGTH (bitify [] v) = LENGTH v`,
  rw [length_bitify]);

val length_shiftr = Q.store_thm("length_shiftr",
   `!v n. LENGTH (shiftr v n) = LENGTH v - n`,
   lrw [shiftr_def]);

val length_rev_count_list = Q.store_thm("length_rev_count_list",
  `!n. LENGTH (rev_count_list n) = n`,
  Induct \\ lrw [rev_count_list_def]);

val length_w2v = Q.store_thm("length_w2v",
  `!w:'a word. LENGTH (w2v w) = dimindex(:'a)`,
  lrw [w2v_def]);

val el_rev_count_list = Q.store_thm("el_rev_count_list",
  `!n i. i < n ==> (EL i (rev_count_list n) = n - 1 - i)`,
  Induct \\ lrw [rev_count_list_def]);

val el_bitify = Q.prove(
   `!v i a. i < LENGTH v ==>
            (EL (LENGTH v - (i + 1)) v = (EL i (bitify a v) = 1))`,
   lrw [bitify_def, bitify_reverse_map, rich_listTheory.EL_APPEND1,
        listTheory.EL_REVERSE, listTheory.EL_MAP, arithmeticTheory.PRE_SUB1]);

val el_zero_extend = Q.store_thm("el_zero_extend",
  `!n i v. EL i (zero_extend n v) =
           n - LENGTH v <= i /\ EL (i - (n - LENGTH v)) v`,
  lrw [zero_extend_def, listTheory.PAD_LEFT]
  \\ Cases_on `i < n - LENGTH v`
  \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]);

val el_sign_extend = Q.store_thm("el_sign_extend",
  `!n i v. EL i (sign_extend n v) =
           if i < n - LENGTH v then
              EL 0 v
           else
              EL (i - (n - LENGTH v)) v`,
  lrw [sign_extend_def, listTheory.PAD_LEFT,
       rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]);

val el_fixwidth = Q.store_thm("el_fixwidth",
  `!i n w. i < n ==>
           (EL i (fixwidth n w) =
              if LENGTH w < n then
                 n - LENGTH w <= i /\ EL (i - (n - LENGTH w)) w
              else
                 EL (i + (LENGTH w - n)) w)`,
  lrw [fixwidth_def, el_zero_extend, rich_listTheory.EL_DROP]);

val el_field = Q.store_thm("el_field",
  `!v h l i. i < SUC h - l ==>
             (EL i (field h l v) =
              SUC h <= i + LENGTH v /\ EL (i + LENGTH v - SUC h) v)`,
  lrw [field_def, shiftr_def, el_fixwidth, rich_listTheory.EL_TAKE]
  \\ Cases_on `l < LENGTH v` \\ lrw []
  \\ `LENGTH v - SUC h < LENGTH v - l` by decide_tac
  \\ lrw [rich_listTheory.EL_TAKE]);

val shiftr_field = Q.prove(
   `!n l v. LENGTH l <> 0 ==> (shiftr l n = field (LENGTH l - 1) n l)`,
   rpt strip_tac
   \\ `SUC (LENGTH l - 1) - n = LENGTH (shiftr l n)`
   by (rw [length_shiftr] \\ decide_tac)
   \\ lrw [field_def, fixwidth_id]);

val el_w2v = Q.store_thm("el_w2v",
   `!w: 'a word n.
      n < dimindex (:'a) ==> (EL n (w2v w) = w ' (dimindex (:'a) - 1 - n))`,
      lrw [w2v_def])

val el_shiftr = Q.store_thm("el_shiftr",
  `!i v n d.
       n < d /\ i < d - n /\ 0 < d ==>
       (EL i (shiftr (fixwidth d v) n) =
       d <= i + LENGTH v /\ EL (i + LENGTH v - d) v)`,
  lrw [shiftr_field, length_fixwidth, el_field, el_fixwidth,
       arithmeticTheory.ADD1]);

val shiftr_0 = Q.store_thm("shiftr_0", `!v. shiftr v 0 = v`, lrw [shiftr_def]);

val field_fixwidth = Q.store_thm("field_fixwidth",
  `!h v. field h 0 v = fixwidth (SUC h) v`,
  rw [field_def, shiftr_0]);

val testbit = Q.store_thm("testbit",
  `!b v. testbit b v = let n = LENGTH v in b < n /\ EL (n - 1 - b) v`,
  lrw [zero_extend_def, testbit_def, field_def, fixwidth_def, shiftr_def,
       listTheory.PAD_LEFT, arithmeticTheory.SUB_LEFT_SUB, bitTheory.SUC_SUB]
  \\ Induct_on `v`
  \\ lrw []
  \\ lfs [arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL,
          arithmeticTheory.ADD1]
  >- (`b = LENGTH v` by decide_tac \\ lrw [])
  \\ imp_res_tac arithmeticTheory.LESS_ADD_1
  \\ lfs [REWRITE_RULE [arithmeticTheory.ADD1] listTheory.EL_restricted]);

val testbit_geq_len = Q.store_thm("testbit_geq_len",
   `!v i. LENGTH v <= i ==> ~testbit i v`,
   simp [testbit])

val testbit_el = Q.store_thm("testbit_el",
   `!v i. i < LENGTH v ==> (testbit i v = EL (LENGTH v - 1 - i) v)`,
   simp [testbit])

val bit_v2w = Q.store_thm("bit_v2w",
  `!n v. word_bit n (v2w v : 'a word) = n < dimindex(:'a) /\ testbit n v`,
  rw [v2w_def, wordsTheory.word_bit_def]
  \\ Cases_on `n < dimindex(:'a)`
  \\ wrw []
  \\ assume_tac wordsTheory.DIMINDEX_GT_0
  \\ `~(n <= dimindex(:'a) - 1)` by decide_tac
  \\ asm_rewrite_tac []);

val word_index_v2w = Q.store_thm("word_index_v2w",
  `!v i. (v2w v : 'a word) ' i =
         if i < dimindex(:'a) then
            testbit i v
         else
            FAIL $' ^(Term.mk_var ("index too large", Type.bool))
                 (v2w v : 'a word) i`,
  rw [wordsTheory.word_bit, bit_v2w, combinTheory.FAIL_THM]);

val testbit_w2v = Q.store_thm("testbit_w2v",
  `!n w. testbit n (w2v (w : 'a word)) = word_bit n w`,
  lrw [w2v_def, testbit, wordsTheory.word_bit_def]
  \\ Cases_on `n < dimindex(:'a)`
  \\ lrw []
  \\ assume_tac wordsTheory.DIMINDEX_GT_0
  \\ `~(n <= dimindex(:'a) - 1)` by decide_tac
  \\ asm_rewrite_tac []);

val word_bit_lem =
  wordsTheory.word_bit
    |> Q.SPECL [`w`, `dimindex(:'a) - 1 - i`]
    |> SIMP_RULE arith_ss [wordsTheory.DIMINDEX_GT_0,
          DECIDE ``0 < n ==> (0 < i + n)``]
    |> GEN_ALL;

val w2v_v2w = Q.store_thm("w2v_v2w",
  `!v. w2v (v2w v : 'a word) = fixwidth (dimindex(:'a)) v`,
  lrw [w2v_def, bit_v2w, testbit, fixwidth_def, zero_extend_def,
       listTheory.PAD_LEFT, listTheory.LIST_EQ_REWRITE,
       rich_listTheory.EL_DROP, word_bit_lem]
  \\ Cases_on `x < dimindex(:'a) - LENGTH v`
  \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]);

val v2w_w2v = Q.store_thm("v2w_w2v",
  `!w. v2w (w2v w) = w`,
  wrw [w2v_def, v2w_def, testbit]);

val v2w_fixwidth = Q.store_thm("v2w_fixwidth",
  `!v. v2w (fixwidth (dimindex(:'a)) v) = v2w v : 'a word`,
  wrw [v2w_def, testbit, length_fixwidth, el_fixwidth]
  \\ Cases_on `i < LENGTH v`
  \\ lrw []);

val fixwidth_fixwidth = Q.store_thm("fixwidth_fixwidth",
  `!n v. fixwidth n (fixwidth n v) = fixwidth n v`,
  lrw [fixwidth_def] \\ lfs [length_zero_extend]);

val bitstring_nchotomy = Q.store_thm("bitstring_nchotomy",
  `!w:'a word. ?v. (w = v2w v)`, metis_tac [v2w_w2v]);

val ranged_bitstring_nchotomy = Q.store_thm("ranged_bitstring_nchotomy",
  `!w:'a word. ?v. (w = v2w v) /\ (Abbrev (LENGTH v = dimindex(:'a)))`,
  strip_tac
  \\ qspec_then `w` STRUCT_CASES_TAC bitstring_nchotomy
  \\ qexists_tac `fixwidth (dimindex(:'a)) v`
  \\ rw [markerTheory.Abbrev_def, length_fixwidth, v2w_fixwidth]);

val BACKWARD_LIST_EQ_REWRITE = Q.prove(
  `!l1 l2. (l1 = l2) =
           (LENGTH l1 = LENGTH l2) /\
           !x. x < LENGTH l1 ==>
               (EL (LENGTH l1 - 1 - x) l1 = EL (LENGTH l1 - 1 - x) l2)`,
  lrw [listTheory.LIST_EQ_REWRITE]
  \\ eq_tac \\ lrw []
  \\ `LENGTH l1 - 1 - x < LENGTH l1` by decide_tac
  \\ res_tac
  \\ `x < LENGTH l1` by decide_tac
  \\ lfs []);

val fixwidth_eq = Q.store_thm("fixwidth_eq",
  `!n v w. (fixwidth n v = fixwidth n w) =
           (!i. i < n ==> (testbit i v = testbit i w))`,
  lrw [el_fixwidth, testbit, length_fixwidth, BACKWARD_LIST_EQ_REWRITE]
  \\ rpt BasicProvers.FULL_CASE_TAC
  \\ lfs [DECIDE ``v < n ==> (n <= n + v - (i + 1) = i < v)``]);

val v2w_11 = Q.store_thm("v2w_11",
  `!v w. (v2w v = v2w w : 'a word) =
         (fixwidth (dimindex(:'a)) v = fixwidth (dimindex(:'a)) w)`,
  wrw [wordsTheory.word_bit, bit_v2w, fixwidth_eq]);

(* ------------------------------------------------------------------------- *)

val take_id_imp =
   metisLib.METIS_PROVE [listTheory.TAKE_LENGTH_ID]
     ``!n w: 'a list. (n = LENGTH w) ==> (TAKE n w = w)``

val field_concat_right = Q.store_thm("field_concat_right",
   `!h a b. (LENGTH b = SUC h) ==> (field h 0 (a ++ b) = b)`,
   lrw [field_def, shiftr_def, take_id_imp]
   \\ lrw [fixwidth_def, rich_listTheory.DROP_LENGTH_APPEND])

val field_concat_left = Q.store_thm("field_concat_left",
   `!h l a b.
       l <= h /\ LENGTH b <= l ==>
       (field h l (a ++ b) = field (h - LENGTH b) (l - LENGTH b) a)`,
   rw [field_def, shiftr_def]
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ pop_assum kall_tac
   \\ pop_assum SUBST_ALL_TAC
   \\ lfs [listTheory.TAKE_APPEND1]
   \\ simp [DECIDE ``p + l <= h ==> (SUC h - (p + l) = SUC (h - l) - p)``])

val field_id_imp = Q.store_thm("field_id_imp",
   `!n v. (SUC n = LENGTH v) ==> (field n 0 v = v)`,
   metis_tac [fixwidth_id_imp, field_fixwidth])

(* ------------------------------------------------------------------------- *)

val shiftl_replicate_F = Q.store_thm("shiftl_replicate_F",
   `!v n. shiftl v n = v ++ replicate [F] n`,
   lrw [shiftl_def, replicate_def, listTheory.PAD_RIGHT]
   \\ Induct_on `n`
   \\ lrw [listTheory.GENLIST_CONS])

(* ------------------------------------------------------------------------- *)

val word_lsb_v2w = Q.store_thm("word_lsb_v2w",
  `!v. word_lsb (v2w v) = v <> [] /\ LAST v`,
  lrw [wordsTheory.word_lsb_def, wordsTheory.word_bit, bit_v2w, testbit,
       rich_listTheory.LENGTH_NOT_NULL, rich_listTheory.NULL_EQ_NIL]
  \\ Cases_on `v = []`
  \\ rw [GSYM rich_listTheory.EL_PRE_LENGTH, arithmeticTheory.PRE_SUB1]);

val word_msb_v2w = Q.store_thm("word_msb_v2w",
  `!v. word_msb (v2w v : 'a word) = testbit (dimindex(:'a) - 1) v`,
  lrw [wordsTheory.word_msb_def, wordsTheory.word_bit, bit_v2w]);

val w2w_v2w = Q.store_thm("w2w_v2w",
  `!v. w2w (v2w v : 'a word) : 'b word =
       v2w (fixwidth (if dimindex(:'b) < dimindex(:'a) then
                         dimindex(:'b)
                      else
                         dimindex(:'a)) v)`,
  wrw [wordsTheory.w2w]
  \\ Cases_on `i < dimindex(:'a)`
  \\ lrw [wordsTheory.word_bit, el_fixwidth, bit_v2w, testbit,
          length_fixwidth]
  \\ lfs [arithmeticTheory.NOT_LESS_EQUAL]
  >| [
    `dimindex (:'b) <= LENGTH v + dimindex (:'b) - (i + 1) = i < LENGTH v`
    by decide_tac,
    `dimindex (:'a) <= LENGTH v + dimindex (:'a) - (i + 1) = i < LENGTH v`
    by decide_tac]
  THEN simp []);

val sw2sw_v2w = Q.store_thm("sw2sw_v2w",
  `!v. sw2sw (v2w v : 'a word) : 'b word =
       if dimindex (:'a) < dimindex (:'b) then
          v2w (sign_extend (dimindex(:'b)) (fixwidth (dimindex(:'a)) v))
       else
          v2w (fixwidth (dimindex(:'b)) v)`,
  wrw [wordsTheory.sw2sw]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, word_msb_v2w,
          length_sign_extend, length_fixwidth, el_sign_extend, el_fixwidth]
  \\ lfs [arithmeticTheory.NOT_LESS,
          DECIDE ``0 < d ==> (v - 1 - (d - 1) = v - d)``]
  >- (Cases_on `i < LENGTH v` \\ lrw [])
  >- (Cases_on `LENGTH v = 0`
      \\ lrw [DECIDE ``0n < d ==> ~(d < 1)``, arithmeticTheory.LE_LT1])
  \\ Cases_on `i < LENGTH v` \\ lrw []);

val n2w_v2n = Q.store_thm("n2w_v2n",
  `!v. n2w (v2n v) = v2w v`,
  wrw [wordsTheory.word_bit, bit_v2w, wordsTheory.word_bit_n2w, v2n_def,
       testbit]
  \\ Cases_on `i < LENGTH v`
  \\ rw []
  >| [
    `i < LENGTH (bitify [] v)` by metis_tac [length_bitify_null]
    \\ rw [bitTheory.BIT_num_from_bin_list, every_bit_bitify, el_bitify],
    match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
    \\ qspecl_then [`bitify [] v`, `2`] assume_tac l2n_lt
    \\ fs [arithmeticTheory.NOT_LESS, num_from_bin_list_def]
    \\ metis_tac [length_bitify_null, bitTheory.TWOEXP_MONO2,
                  arithmeticTheory.LESS_LESS_EQ_TRANS]
  ]);

val v2n_n2v_lem = Q.prove(
  `!l. EVERY ($> 2) l ==>
       (MAP ((\b. if b then 1 else 0) o (\n. n <> 0)) l = l)`,
  Induct \\ lrw []);

val v2n_n2v = Q.store_thm("v2n_n2v",
  `!n. v2n (n2v n) = n`,
  lrw [n2v_def, v2n_def, bitify_def, num_from_bin_list_def,
       l2n_def, num_to_bin_list_def,
       bitify_reverse_map, bitify_reverse_map, boolify_reverse_map,
       listTheory.PAD_LEFT, listTheory.MAP_GENLIST, listTheory.REVERSE_APPEND,
       listTheory.REVERSE_GENLIST, rich_listTheory.MAP_REVERSE,
       listTheory.MAP_MAP_o, bitTheory.BITS_LOG2_ZERO_ID, LENGTH_n2l,
       GSYM bitTheory.LOG2_def, DECIDE ``a + 1 - SUC a = 0``,
       v2n_n2v_lem, n2l_BOUND, l2n_n2l]);

val v2w_n2v = Q.store_thm("v2w_n2v",
  `!n. v2w (n2v n) = n2w n`,
  rewrite_tac [GSYM n2w_v2n, v2n_n2v]);

val w2n_v2w = Q.store_thm("w2n_v2w",
  `!v. w2n (v2w v : 'a word) = MOD_2EXP (dimindex(:'a)) (v2n v)`,
  rw [Once (GSYM n2w_v2n), wordsTheory.MOD_2EXP_DIMINDEX]);

val v2n_lt = Q.store_thm("v2n_lt",
  `!v. v2n v < 2 ** LENGTH v`,
    metis_tac [v2n_def, length_bitify_null, num_from_bin_list_def,
               l2n_lt, DECIDE ``0 < 2n``]);

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
  \\ decide_tac;

val word_and_v2w = Q.store_thm("word_and_v2w",
  `!v w. v2w v && v2w w = v2w (band v w)`, bitwise_tac);

val word_or_v2w = Q.store_thm("word_or_v2w",
  `!v w. v2w v || v2w w = v2w (bor v w)`, bitwise_tac);

val word_xor_v2w = Q.store_thm("word_xor_v2w",
  `!v w. v2w v ?? v2w w = v2w (bxor v w)`, bitwise_tac);

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
  \\ lrw [el_fixwidth, DECIDE ``0 < d ==> (d <= v + d - (i + 1) = i < v)``]

val word_nand_v2w = Q.store_thm("word_nand_v2w",
  `!v w. v2w v ~&& (v2w w) : 'a word =
         v2w (bnand (fixwidth (dimindex(:'a)) v)
                    (fixwidth (dimindex(:'a)) w))`, bitwise_tac);

val word_nor_v2w = Q.store_thm("word_nor_v2w",
  `!v w. v2w v ~|| (v2w w) : 'a word =
         v2w (bnor (fixwidth (dimindex(:'a)) v)
                   (fixwidth (dimindex(:'a)) w))`, bitwise_tac);

val word_xnor_v2w = Q.store_thm("word_xnor_v2w",
  `!v w. v2w v ~?? (v2w w) : 'a word =
         v2w (bxnor (fixwidth (dimindex(:'a)) v)
                    (fixwidth (dimindex(:'a)) w))`, bitwise_tac);

val word_1comp_v2w = Q.store_thm("word_1comp_v2w",
  `!v. word_1comp (v2w v : 'a word) = v2w (bnot (fixwidth (dimindex(:'a)) v))`,
  wrw [v2w_def, bnot_def, wordsTheory.word_1comp_def, testbit, el_fixwidth,
       length_fixwidth, listTheory.EL_MAP]
  \\ Cases_on `i < LENGTH v`
  \\ lrw []);

(* ------------------------------------------------------------------------- *)

val word_lsl_v2w = Q.store_thm("word_lsl_v2w",
  `!n v. word_lsl (v2w v : 'a word) n = v2w (shiftl v n)`,
  wrw [wordsTheory.word_lsl_def, shiftl_def, listTheory.PAD_RIGHT]
  \\ Cases_on `n <= i`
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, length_pad_right]
  >- (Cases_on `LENGTH v = 0` \\ lrw [rich_listTheory.EL_APPEND1])
  \\ lrw [rich_listTheory.EL_APPEND2]);

val word_lsr_v2w = Q.store_thm("word_lsr_v2w",
  `!n v. word_lsr (v2w v : 'a word) n =
         v2w (shiftr (fixwidth (dimindex(:'a)) v) n)`,
  wrw [wordsTheory.word_lsr_def, shiftr_def]
  \\ Cases_on `i + n < dimindex(:'a)`
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, length_fixwidth,
          rich_listTheory.EL_TAKE, el_fixwidth,
          DECIDE ``0 < d ==> (d <= v + d - (i + (n + 1)) = i + n < v)``]);

val word_modify_v2w = Q.store_thm("word_modify_v2w",
  `!f v. word_modify f (v2w v : 'a word) =
         v2w (modify f (fixwidth (dimindex(:'a)) v))`,
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
          DECIDE ``0 < d ==> (d <= v + d - (i + 1) = i < v)``]);

val word_bits_v2w = Q.store_thm("word_bits_v2w",
  `!h l v. word_bits h l (v2w v : 'a word) =
           v2w (field h l (fixwidth (dimindex(:'a)) v))`,
  wrw [wordsTheory.word_bits_def]
  \\ Cases_on `i + l < dimindex(:'a)`
  \\ lrw [wordsTheory.word_bit, bit_v2w, length_field, testbit]
  \\ Cases_on `i < SUC h - l`
  \\ lrw [el_field, length_fixwidth, el_fixwidth,
          DECIDE ``0 < d ==> (d <= v + d - (i + (l + 1)) = i + l < v)``]);

val word_extract_v2w = Q.store_thm("word_extract_v2w",
  `!h l v. word_extract h l (v2w v : 'a word) =
           w2w (word_bits h l (v2w v : 'a word))`,
  rw [wordsTheory.word_extract_def]);

val word_slice_v2w = Q.store_thm("word_slice_v2w",
  `!h l v. word_slice h l (v2w v : 'a word) =
           v2w (shiftl (field h l (fixwidth (dimindex(:'a)) v)) l)`,
  rw [wordsTheory.WORD_SLICE_THM, word_bits_v2w, word_lsl_v2w]);

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
   ]));

val hd_shiftr =
  el_shiftr
    |> Q.SPEC `0`
    |> SIMP_RULE (arith_ss++boolSimps.CONJ_ss) [listTheory.EL]

val word_asr_v2w = Q.store_thm("word_asr_v2w",
  `!n v. word_asr (v2w v : 'a word) n =
         let l = fixwidth (dimindex(:'a)) v in
            v2w (sign_extend (dimindex(:'a))
                (if dimindex(:'a) <= n then [HD l] else shiftr l n))`,
  lrw [wordsTheory.ASR_LIMIT, word_msb_v2w]
  >| [
    simp_tac (arith_ss++boolSimps.LET_ss)
         [GSYM (Thm.CONJUNCT1 rich_listTheory.EL), el_fixwidth,
          wordsTheory.DIMINDEX_GT_0, testbit, sign_extend_def]
    \\ Cases_on `LENGTH v = 0`
    \\ simp [pad_left_T_or_F]
    \\ rw [pad_left_T_or_F, DECIDE ``~(v < d) = d < v + 1``,
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
  ]);

val word_ror_v2w = Q.store_thm("word_ror_v2w",
  `!n v. word_ror (v2w v : 'a word) n =
         let l = fixwidth (dimindex(:'a)) v
         and x = n MOD dimindex(:'a)
         in
            v2w (field (x - 1) 0 l ++ field (dimindex(:'a) - 1) x l)`,
  wrw [wordsTheory.word_ror, word_or_def, word_lsl_def, word_bits_def]
  \\ `?p. dimindex(:'a) = i + p + 1`
  by metis_tac [arithmeticTheory.LESS_ADD_1, arithmeticTheory.ADD_ASSOC]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit]
  \\ Cases_on `n MOD (i + (p + 1)) = 0`
  \\ rw [length_field, arithmeticTheory.ADD1]
  >- (`LENGTH (field 0 0 (fixwidth (i + (p + 1)) v)) = 1`
      by rw [length_field]
      \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, el_field, length_fixwidth,
              el_fixwidth, rich_listTheory.EL_APPEND2, arithmeticTheory.ADD1,
              DECIDE ``i + (p + 1) <= p + v = i < v``])
  \\ qabbrev_tac `q = n MOD (i + (p + 1))`
  \\ `q < i + p + 1` by lrw [Abbr `q`, arithmeticTheory.MOD_LESS]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit]
  \\ Cases_on `p < q`
  \\ lrw [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2, length_field]
  >- (lrw [el_field, length_fixwidth, arithmeticTheory.ADD1, el_fixwidth]
      \\ Cases_on `LENGTH v = 0`
      \\ lrw [DECIDE ``i + (p + 1) <= i + (2 * p + (v + 1)) - q  =
                       i < i + (p + (v + 1)) - q``])
  \\ Cases_on `i + q < dimdinex(:'a)`
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, el_field, length_fixwidth,
          arithmeticTheory.ADD1, el_fixwidth,
          DECIDE ``i + (p + 1) <= p + v - q = i + q < v``]);

val word_reverse_v2w = Q.store_thm("word_reverse_v2w",
  `!v. word_reverse (v2w v : 'a word) =
       v2w (REVERSE (fixwidth (dimindex(:'a)) v))`,
  wrw [wordsTheory.word_reverse_def]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit, length_fixwidth,
          listTheory.EL_REVERSE, DECIDE ``PRE (i + 1) = i``]
  \\ lrw [el_fixwidth, DECIDE ``0 < d ==> (d <= i + v = d < i + (v + 1))``]
  \\ Cases_on `LENGTH v = 0`
  \\ lrw []);

val word_join_v2w = Q.store_thm("word_join_v2w",
  `!v1 v2. FINITE univ(:'a) /\ FINITE univ(:'b) ==>
           (word_join (v2w v1 : 'a word) (v2w v2 : 'b word) =
            v2w (v1 ++ fixwidth (dimindex(:'b)) v2))`,
  wrw [wordsTheory.word_join_index]
  \\ wrw [wordsTheory.word_bit, bit_v2w, testbit, length_fixwidth,
          rich_listTheory.EL_APPEND2]
  \\ lrw [el_fixwidth, DECIDE ``0 < d ==> (d <= v + d - (i + 1) = i < v)``]
  \\ Cases_on `LENGTH v1 = 0` \\ lrw [rich_listTheory.EL_APPEND1]);

val word_concat_v2w = Q.store_thm("word_concat_v2w",
  `!v1 v2. FINITE univ(:'a) /\ FINITE univ(:'b) ==>
           (word_concat (v2w v1 : 'a word) (v2w v2 : 'b word) : 'c word =
            v2w (fixwidth (MIN (dimindex(:'c)) (dimindex(:'a) + dimindex(:'b)))
                          (v1 ++ fixwidth (dimindex(:'b)) v2)))`,
  lrw [wordsTheory.word_concat_def, word_join_v2w, w2w_v2w,
       arithmeticTheory.MIN_DEF]);

val word_join_v2w_rwt = Q.store_thm("word_join_v2w_rwt",
  `!v1 v2. word_join (v2w v1 : 'a word) (v2w v2 : 'b word) =
           if FINITE univ(:'a) /\ FINITE univ(:'b) then
              v2w (v1 ++ fixwidth (dimindex(:'b)) v2)
           else
              FAIL $word_join ^(Term.mk_var("bad domain", Type.bool))
                (v2w v1 : 'a word) (v2w v2 : 'b word)`,
  rw [word_join_v2w, combinTheory.FAIL_THM]);

val word_concat_v2w_rwt = Q.store_thm("word_concat_v2w_rwt",
  `!v1 v2.
      word_concat (v2w v1 : 'a word) (v2w v2 : 'b word) : 'c word =
        if FINITE univ(:'a) /\ FINITE univ(:'b) then
           v2w (fixwidth (MIN (dimindex(:'c)) (dimindex(:'a) + dimindex(:'b)))
                         (v1 ++ fixwidth (dimindex(:'b)) v2))
        else
           FAIL $word_concat ^(Term.mk_var("bad domain", Type.bool))
             (v2w v1 : 'a word) (v2w v2 : 'b word)`,
  rw [word_concat_v2w, combinTheory.FAIL_THM]);

val genlist_fixwidth = Q.prove(
   `!d v. 0 < d ==>
          (GENLIST (\i. (d < i + (LENGTH v + 1) /\ 0 < LENGTH v) /\
                        EL (LENGTH v - 1 - (d - (i + 1))) v) d =
          fixwidth d v)`,
   lrw [listTheory.LIST_EQ_REWRITE, length_fixwidth, el_fixwidth]
   \\ Cases_on `LENGTH v = 0`
   \\ lrw [DECIDE ``0 < d ==> (d <= x + v = d < x + (v + 1))``]);

val word_reduce_v2w = Q.store_thm("word_reduce_v2w",
  `!f v. word_reduce f (v2w v : 'a word) =
         let l = fixwidth (dimindex(:'a)) v in
            v2w [FOLDL f (HD l) (TL l)] : 1 word`,
  wrw [word_reduce_def]
  \\ lrw [wordsTheory.word_bit, bit_v2w, testbit]
  \\ match_mp_tac listTheory.FOLDL_CONG
  \\ lrw [genlist_fixwidth]);

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

val extract_v2w = Q.store_thm("extract_v2w",
  `!h l v.
     (LENGTH v <= dimindex(:'a)) /\ (dimindex(:'b) = SUC h - l) /\
     dimindex(:'b) < dimindex(:'a) ==>
     ((h >< l) (v2w v : 'a word) : 'b word = v2w (field h l v))`,
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
  \\ lrw [])

val DROP_LAST = Q.prove(
   `!l. ~NULL l ==> (DROP (LENGTH l - 1) l = [LAST l])`,
   lrw [listTheory.NULL_LENGTH]
   \\ `LENGTH l - 1 <= LENGTH l` by decide_tac
   \\ imp_res_tac rich_listTheory.DROP_LASTN
   \\ lfs []
   \\ lfs [rich_listTheory.LASTN_1, listTheory.LENGTH_NIL])

val word_bit_last_shiftr = Q.store_thm("word_bit_last_shiftr",
  `!i v. i < dimindex(:'a) ==>
         (word_bit i (v2w v : 'a word) =
          let l = shiftr v i in ~NULL l /\ LAST l)`,
  lrw [bit_v2w, testbit_def, field_def, DECIDE ``SUC i - i = 1``, fixwidth_def]
  >- (`LENGTH (shiftr v i) = 0` by decide_tac
      \\ lfs [listTheory.LENGTH_NIL, listTheory.PAD_LEFT, zero_extend_def])
  \\ `LENGTH (shiftr v i) <> 0` by decide_tac
  \\ lfs [GSYM listTheory.NULL_LENGTH, DROP_LAST])

(* ------------------------------------------------------------------------- *)

val ops_to_v2w = Q.store_thm("ops_to_v2w",
   `(!v n. v2w v || n2w n = v2w v || v2w (n2v n)) /\
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
    (!v n. word_join (n2w n) (v2w v) = word_join (v2w (n2v n)) (v2w v))`,
   rewrite_tac [v2w_n2v]);

val ops_to_n2w = Q.store_thm("ops_to_n2w",
  `(!v. word_2comp (v2w v) = word_2comp (n2w (v2n v))) /\
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
   (!v w. (w >=+ v2w v : 'a word) = (w >=+ n2w (v2n v) : 'a word))`,
   rewrite_tac [n2w_v2n]);

(* ------------------------------------------------------------------------- *)

val () = bossLib.export_rewrites
   ["length_w2v", "length_fixwidth", "length_field",
    "length_bitify", "length_shiftr",
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
     "word_join_v2w",
     "word_concat_v2w",
     "word_reduce_v2w",
     "reduce_and_v2w",
     "reduce_or_v2w"
  ];

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

val _ = export_theory();
