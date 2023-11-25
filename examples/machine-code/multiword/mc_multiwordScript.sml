open HolKernel Parse boolLib bossLib;
open multiwordTheory helperLib;
open wordsTheory wordsLib addressTheory arithmeticTheory listTheory pairSyntax;
open addressTheory pairTheory set_sepTheory rich_listTheory integerTheory;
local open mc_tailrecLib blastLib intLib in end

val _ = new_theory "mc_multiword";
val _ = ParseExtras.temp_loose_equality()
val _ = temp_delsimps ["NORMEQ_CONV"]

val REV = Tactical.REVERSE;

fun tailrec_define name tm = let
  val (def,t1,pre,t2) = tailrecLib.tailrec_define_from_step name tm NONE;
  val _ = save_thm(name ^ "_def", def)
  val _ = save_thm(name ^ "_pre_def", pre)
  in (def,t1,pre,t2) end

val EVEN_BIT0 = bitTheory.BIT0_ODD |> REWRITE_RULE [ODD_EVEN,FUN_EQ_THM]

(* TODO: move? *)

val EVEN_BIT_SUC = Q.store_thm("EVEN_BIT_SUC",
  `EVEN n ==> !i. (BIT i (SUC n) = if i = 0 then T else BIT i n)`,
  completeInduct_on`n` \\ rw[]
  \\ Cases_on`i=0` \\ fs[]
  >- (
    CCONTR_TAC \\ fs[EVEN_BIT0,EVEN] )
  \\ Cases_on`i` \\ fs[]
  \\ fs[GSYM bitTheory.BIT_DIV2]
  \\ fs[ADD1,ADD_DIV_RWT,EVEN_MOD2]);

val EVEN_MOD = Q.store_thm("EVEN_MOD",
  `0 < m /\ EVEN m ==> (EVEN (n MOD m) <=> EVEN n)`,
  strip_tac
  \\ first_x_assum(CHANGED_TAC o strip_assume_tac o REWRITE_RULE[EVEN_EXISTS])
  \\ rw[EVEN_MOD2]
  \\ rw[MOD_MULT_MOD]);

val word_msb_double_lsr_1 = Q.store_thm("word_msb_double_lsr_1",
  `word_msb w <=> (w <> (word_lsr (word_add w w) 1))`,
  rw[d_word_msb,DIV_LE_X]
  \\ qspecl_then[`w`,`1`](mp_tac o SYM)WORD_MUL_LSL \\ rw[]
  \\ reverse(rw[EQ_IMP_THM])
  >- (
    CCONTR_TAC
    \\ qpat_x_assum`_ <> _`mp_tac \\ simp[]
    \\ match_mp_tac EQ_SYM
    \\ match_mp_tac lsl_lsr \\ fs[] )
  \\ fsrw_tac[wordsLib.WORD_BIT_EQ_ss][]
  \\ qexists_tac`dimindex(:'a)-1`
  \\ assume_tac DIMINDEX_GT_0
  \\ simp[GSYM word_msb_def,d_word_msb,DIV_LE_X]);

val xor_one_add_one = Q.store_thm("xor_one_add_one",
  `~w ' 0 ==> (w ?? 1w = w + 1w)`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][word_index]
  \\ Cases_on`i=0` \\ fs[WORD_ADD_BIT0,word_index]
  \\ Cases_on`w` \\ fs[word_add_n2w,word_index,EVEN_BIT0]
  \\ simp[GSYM ADD1,EVEN_BIT_SUC]);

val add_one_xor_one = Q.store_thm("add_one_xor_one",
  `~w ' 0 ==> (w + 1w ?? 1w = w)`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][word_index]
  \\ Cases_on`i=0` \\ fs[WORD_ADD_BIT0,word_index]
  \\ Cases_on`w` \\ fs[word_add_n2w,word_index,EVEN_BIT0]
  \\ simp[GSYM ADD1,EVEN_BIT_SUC]);

val one_neq_zero_word = SIMP_CONV(srw_ss())[]``1w = 0w``

(* -- *)

(*

  This file produces functions that resemble machine code. The
  functions perform any of the following arithmetic functions over
  arbitrary size integer inputs.

    + - * div mod compare print-to-dec

*)

(* compare *)

val (mc_cmp_def, _,
     mc_cmp_pre_def, _) =
  tailrec_define "mc_cmp" ``
    (\(l,r10,xs,ys).
      if r10 = 0x0w then (INR (l,r10,xs,ys),T)
      else
        (let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r8 = EL (w2n r10) xs in
         let cond = cond /\ w2n r10 < LENGTH ys in
         let r9 = EL (w2n r10) ys
         in
           if r8 = r9 then (INL (l-1,r10,xs,ys),cond /\ l <> 0n)
           else if r8 <+ r9
           then (let r10 = 0x1w in (INR (l,r10,xs,ys),cond))
           else (let r10 = 0x2w in (INR (l,r10,xs,ys),cond))))
    :num # α word # α word list # α word list -> (num # α word # α word list # α
     word list + num # α word # α word list # α word list) # bool``;

val (mc_compare_def, _,
     mc_compare_pre_def, _) =
  tailrec_define "mc_compare" ``
    (\(l,r10,r11,xs,ys).
      if r10 <+ r11 then (let r10 = 0x1w in (INR (l,r10,xs,ys),T))
      else if r11 <+ r10 then (let r10 = 0x2w in (INR (l,r10,xs,ys),T))
      else
        (let cond = mc_cmp_pre (l-1,r10,xs,ys) /\ l <> 0 in
         let (l,r10,xs,ys) = mc_cmp (l-1,r10,xs,ys)
         in
           (INR (l,r10,xs,ys),cond)))
    :num # α word # α word # α word list # α word list -> (num # α
     word # α word # α word list # α word list + num # α word # α word
     list # α word list) # bool``;

val mc_header_def = Define `
  mc_header (s,xs:α word list) = n2w (LENGTH xs * 2) + if s then 1w else 0w:α word`;

val (mc_icompare_def, _,
     mc_icompare_pre_def, _) =
  tailrec_define "mc_icompare" ``
    (\(l,r10,r11,xs,ys).
      if r10 && 0x1w = 0x0w then
        if r11 && 0x1w = 0x0w then
          (let r10 = r10 >>> 1 in
           let r11 = r11 >>> 1 in
           let cond = mc_compare_pre (l,r10,r11,xs,ys) in
           let (l,r10,xs,ys) = mc_compare (l,r10,r11,xs,ys)
           in
             (INR (l,r10,xs,ys),cond))
        else (let r10 = 0x2w in (INR (l,r10,xs,ys),T))
      else if r11 && 0x1w = 0x0w then
        (let r10 = 0x1w in (INR (l,r10,xs,ys),T))
      else
        (let r10 = r10 >>> 1 in
         let r11 = r11 >>> 1 in
         let cond = mc_compare_pre (l,r10,r11,xs,ys) in
         let (l,r10,xs,ys) = mc_compare (l,r10,r11,xs,ys)
         in
           if r10 = 0x0w then (INR (l,r10,xs,ys),cond)
           else (let r10 = r10 ?? 0x3w in (INR (l,r10,xs,ys),cond))))
    :num # α word # α word # α word list # α word list -> (num # α
     word # α word # α word list # α word list + num # α word # α word
     list # α word list) # bool``;

val cmp2w_def = Define `
  (cmp2w NONE = 0w:α word) /\
  (cmp2w (SOME T) = 1w) /\
  (cmp2w (SOME F) = 2w)`;

val mc_cmp_thm = prove(
  ``!xs ys xs1 ys1 l.
      (LENGTH ys = LENGTH xs) /\ LENGTH (xs:α word list) < dimword(:α) /\
      LENGTH xs <= l ==>
      mc_cmp_pre (l,n2w (LENGTH xs),xs++xs1,ys++ys1) /\
      ?l2.
        (mc_cmp (l,n2w (LENGTH xs),xs++xs1,ys++ys1) =
          (l2,cmp2w (mw_cmp xs ys),xs++xs1,ys++ys1)) /\
        l <= l2 + LENGTH xs``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mc_cmp_def,Once mc_cmp_pre_def]
    \\ FULL_SIMP_TAC std_ss [Once mw_cmp_def,cmp2w_def,APPEND])
  \\ NTAC 8 STRIP_TAC
  \\ `(ys = []) \/ ?y ys2. ys = SNOC y ys2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,ADD1]
  \\ `LENGTH xs < dimword (:α)` by (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ RES_TAC \\ ONCE_REWRITE_TAC [mc_cmp_def,mc_cmp_pre_def]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC (srw_ss()) [n2w_11,word_add_n2w,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.EL_LENGTH_APPEND]
  \\ Q.PAT_X_ASSUM `LENGTH ys2 = LENGTH xs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.EL_LENGTH_APPEND]
  \\ reverse IF_CASES_TAC THEN1
   (fs [] \\ SIMP_TAC std_ss [Once mw_cmp_def]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
    \\ SRW_TAC [] [cmp2w_def])
  \\ fs []
  \\ SIMP_TAC std_ss [Once mw_cmp_def]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
  \\ `LENGTH ys2 <= l-1` by decide_tac
  \\ `LENGTH ys2 = LENGTH ys2` by decide_tac
  \\ res_tac
  \\ rpt (first_x_assum (qspecl_then [`y::ys1`,`y::xs1`] mp_tac))
  \\ rpt strip_tac \\ fs [])
  |> Q.SPECL [`xs`,`ys`,`[]`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL];

val mc_compare_thm = prove(
  ``LENGTH (xs:α word list) < dimword (:α) /\ LENGTH ys < dimword (:α) /\
    LENGTH xs + 1 <= l ==>
    ?l2. mc_compare_pre (l,n2w (LENGTH xs),n2w (LENGTH ys),xs,ys) /\
         (mc_compare (l,n2w (LENGTH xs),n2w (LENGTH ys),xs,ys) =
           (l2,cmp2w (mw_compare xs ys),xs,ys)) /\
         l <= l2 + LENGTH xs + 1``,
  SIMP_TAC (srw_ss()) [mc_compare_def,mc_compare_pre_def,
    n2w_11,WORD_LO,LET_DEF,mw_compare_def]
  \\ SRW_TAC [] [cmp2w_def]
  \\ fs []
  \\ `LENGTH xs = LENGTH ys` by DECIDE_TAC
  \\ MP_TAC mc_cmp_thm \\ FULL_SIMP_TAC (srw_ss()) []
  \\ disch_then (qspec_then `l-1` mp_tac) \\ fs []
  \\ strip_tac \\ fs []);

val mc_header_AND_1 = store_thm("mc_header_AND_1",
  ``mc_header (s,xs) && (0x1w:'a word) = b2w s``,
  rw[mc_header_def,GSYM word_mul_n2w,b2w_def,b2n_def]
  \\ Q.SPEC_TAC (`n2w (LENGTH xs) :α word`,`w`)
  \\ rw[fcpTheory.CART_EQ]
  \\ rw[word_and_def,WORD_ADD_BIT0,fcpTheory.FCP_BETA]
  \\ rw[word_mul_def,dimword_def,word_index]
  \\ Cases_on`i=0` \\ fs[word_add_n2w,word_index]
  \\ fs[bitTheory.ADD_BIT0]
  \\ simp[EVEN_BIT0,EVEN_MULT]
  \\ rw[EVEN_MULT] \\ disj2_tac
  THEN_LT USE_SG_THEN ACCEPT_TAC 1 2
  \\ qmatch_goalsub_abbrev_tac`EVEN (n MOD m)`
  \\ `0 < m ∧ EVEN m`
  by ( simp[Abbr`m`,Abbr`n`,EVEN_EXP] )
  \\ simp[EVEN_MOD,Abbr`n`]);

val mc_header_sign = prove(
  ``(mc_header (s,xs) && 1w = (0w:'a word)) = ~s``,
  Cases_on`s` \\ rw[mc_header_AND_1]
  \\ EVAL_TAC \\ simp[]);

val mc_length_lemma = prove(
  ``(w * 2w + if s then 0x1w else 0x0w) >>> 1 = (w * 2w:'a word) >>> 1``,
  Cases_on `s` \\ FULL_SIMP_TAC std_ss [] \\ blastLib.BBLAST_TAC
  \\ Cases_on`w` \\ fs[WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ rewrite_tac[Once(GSYM w2n_11),w2n_lsr]
  \\ simp[]
  \\ simp[dimword_def]
  \\ Cases_on`dimindex(:'a)`\\fs[EXP]
  \\ fs[GSYM DIV_MOD_MOD_DIV]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ once_rewrite_tac[MULT_COMM]
  \\ simp[DIV_MULT,MULT_DIV]);

val mc_length = prove(
  ``LENGTH (xs:'a word list) < dimword (:'a) DIV 2 ==>
    (mc_header (s,xs) >>> 1 = n2w (LENGTH xs))``,
  FULL_SIMP_TAC std_ss [mc_header_def,GSYM word_mul_n2w,mc_length_lemma]
  \\ SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w,word_mul_n2w]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ fs[X_LT_DIV]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]);

val dim63_IMP_dim64 = prove(
  ``n < dimword (:'a) DIV 2 ==> n < dimword (:'a)``,
  fs[X_LT_DIV]);

val mc_icompare_thm = prove(
  ``LENGTH (xs:'a word list) < dimword (:'a) DIV 2 /\
    LENGTH ys < dimword (:'a) DIV 2 /\
    LENGTH xs + 1 <= l ==>
    ?l2. mc_icompare_pre (l,mc_header (s,xs),mc_header (t,ys),xs,ys) /\
        (mc_icompare (l,mc_header (s,xs),mc_header (t,ys),xs,ys) =
          (l2,cmp2w (mwi_compare (s,xs) (t,ys)),xs,ys)) /\
        l <= l2 + LENGTH xs + 1``,
  strip_tac \\
  FULL_SIMP_TAC std_ss [mc_icompare_def,mc_icompare_pre_def,mc_header_sign,
    mc_length,LET_DEF] \\ IMP_RES_TAC dim63_IMP_dim64
  \\ mp_tac mc_compare_thm \\ fs [] \\ strip_tac \\ fs []
  \\ FULL_SIMP_TAC std_ss [mwi_compare_def]
  \\ Cases_on `s` \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [cmp2w_def] \\ fs []
  \\ Cases_on `mw_compare xs ys` \\ FULL_SIMP_TAC std_ss [cmp2w_def,option_eq_def]
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,option_eq_def,n2w_11]
  \\ rw[]
  \\ rfs[MOD_EQ_0_DIVISOR]
  \\ Cases_on`d` \\ fs[MULT]
  \\ Cases_on`dimword(:'a)` \\ fs[ADD1]
  \\ Cases_on`n` \\ fs[MULT]
  >- (
    Cases_on`xs` \\ fs[] \\
    Cases_on`ys` \\ fs[] \\
    fs[mw_compare_def] \\
    fs[Once mw_cmp_def] )
  \\ qmatch_asmsub_rename_tac`2n = 2 * k + _`
  \\ Cases_on`k` \\ fs[]
  \\ Cases_on`xs` \\ fs[]
  \\ Cases_on`ys` \\ fs[]
  \\ fs[mw_compare_def]
  \\ fs[Once mw_cmp_def]);

(* addition *)

val single_add_word_def = Define `
  single_add_word w1 w2 c =
    let (z,c) = single_add w1 w2 (c <> 0w:'a word) in
      (z:'a word, (b2w c) :'a word)`;

val single_add_word_thm =
  single_add_word_def
  |> SIMP_RULE std_ss [LET_DEF]
  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV);

val (mc_add_loop2_def, _,
     mc_add_loop2_pre_def, _) =
  tailrec_define "mc_add_loop2" ``
    (\(l,r1:'a word,r3:'a word,r8:'a word,r9:'a word,r10:'a word,xs,zs).
      if r1 = 0x1w then
        (let r1 = 0x0w
         in
           (INR (l,r1:'a word,r3,r8,r9,r10,xs,zs),T))
      else
        (let r1 = r1 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r8 = EL (w2n r10) xs in
         let cond = cond /\ (r3 <> 0w ==> (r3 = 1w)) in
         let (r8,r3) = single_add_word r8 r9 r3 in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r8 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r3,r8,r9,r10,xs,zs),cond /\ l <> 0n)))``;

val (mc_add_loop1_def, _,
     mc_add_loop1_pre_def, _) =
  tailrec_define "mc_add_loop1" ``
    (\(l,r1:'a word,r3:'a word,r8:'a word,r9:'a word,r10:'a word,xs,ys,zs).
      if r1 = 0x1w then
        (let r1 = 0x0w:'a word
         in
           (INR (l,r1,r3,r8,r9,r10,xs,ys,zs),T))
      else
        (let r1 = r1 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r8 = EL (w2n r10) xs in
         let cond = cond /\ w2n r10 < LENGTH ys in
         let r9 = EL (w2n r10) ys in
         let cond = cond /\ (r3 <> 0w ==> (r3 = 1w)) in
         let (r8,r3) = single_add_word r8 r9 r3 in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r8 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r3,r8,r9,r10,xs,ys,zs),cond /\ l <> 0n)))``;

val (mc_add_loop_def, _,
     mc_add_loop_pre_def, _) =
  tailrec_define "mc_add_loop" ``
    (\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r1 = r1 + 0x1w in
       let r2 = r2 + 0x1w in
       let r3 = 0w in
       let cond = mc_add_loop1_pre (l-1,r1,r3,r8,r9,r10,xs,ys,zs) /\ l <> 0 in
       let (l,r1,r3,r8,r9,r10,xs,ys,zs) = mc_add_loop1 (l-1,r1,r3,r8,r9,r10,xs,ys,zs) in
       let r1 = r2 in
       let r9 = 0x0w in
       let cond = cond /\ mc_add_loop2_pre (l-1,r1,r3,r8,r9,r10,xs,zs) /\ l <> 0 in
       let (l,r1,r3,r8,r9,r10,xs,zs) = mc_add_loop2 (l-1,r1,r3,r8,r9,r10,xs,zs)
       in
         if r3 = 0w then
           (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond)
         else
           (let r8 = 0x1w in
            let cond = cond /\ w2n r10 < LENGTH zs in
            let zs = LUPDATE r8 (w2n r10) zs in
            let r10 = r10 + 0x1w
            in
              (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond))))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word
     list # 'a word list # 'a word list -> (num # 'a word # 'a word #
     'a word # 'a word # 'a word # 'a word list # 'a word list # 'a
     word list + num # 'a word # 'a word # 'a word # 'a word # 'a word
     # 'a word list # 'a word list # 'a word list) # bool``;

val mc_add_loop_def =
  LIST_CONJ [mc_add_loop_def,mc_add_loop_pre_def,
             mc_add_loop1_def,mc_add_loop1_pre_def,
             mc_add_loop2_def,mc_add_loop2_pre_def]

val (mc_add_def, _,
     mc_add_pre_def, _) =
  tailrec_define "mc_add" ``
    (\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r2 = r2 - r1 in
       let cond = mc_add_loop_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
       let (l,r1,r2,r8,r9,r10,xs,ys,zs) =
             mc_add_loop (l,r1,r2,r8,r9,r10,xs,ys,zs)
       in
         (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word
     list # 'a word list # 'a word list -> (num # 'a word # 'a word #
     'a word # 'a word # 'a word # 'a word list # 'a word list # 'a
     word list + num # 'a word # 'a word # 'a word # 'a word # 'a word
     # 'a word list # 'a word list # 'a word list) # bool``;

val SNOC_INTRO = prove(
  ``xs1 ++ x::(xs ++ xs2) = SNOC x xs1 ++ (xs ++ xs2)``,
  FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);

val LUPDATE_SNOC = prove(
  ``(LENGTH zs1 = LENGTH xs1) ==>
    (LUPDATE x (LENGTH xs1) (SNOC y zs1 ++ (t ++ zs2)) =
     (SNOC x zs1 ++ (t ++ zs2)))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]);

val b2n_thm = prove(``!b. b2n b = b2n b``,Cases \\ EVAL_TAC)

val b2w_eq = store_thm("b2w_eq[simp]",
  ``((b2w b = 0w) <=> ~b) /\ ((b2w b = 1w) <=> b)``,
  Cases_on `b` \\ EVAL_TAC \\ fs[]);

val mc_add_loop1_thm = prove(
  ``!(xs:'a word list) ys zs xs1 ys1 zs1 xs2 ys2 zs2 r8 r9 c l.
      (LENGTH ys1 = LENGTH xs1) /\ (LENGTH zs1 = LENGTH xs1) /\
      (LENGTH ys = LENGTH xs) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < dimword(:'a) /\
      LENGTH xs <= l ==>
      ?r8' r9' l2.
        mc_add_loop1_pre (l,n2w (LENGTH xs + 1),b2w c,r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,zs1 ++ zs ++ zs2) /\
        (mc_add_loop1 (l,n2w (LENGTH xs + 1),b2w c,r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,zs1 ++ zs ++ zs2) =
          (l2,0w,b2w (SND (mw_add xs ys c)),r8',r9',n2w (LENGTH (xs1++xs)),
           xs1 ++ xs ++ xs2,ys1 ++ ys ++ ys2,
           zs1 ++ FST (mw_add xs ys c) ++ zs2)) /\
        l <= l2 + LENGTH xs``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def]
    \\ ONCE_REWRITE_TAC [mc_add_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def,LET_DEF])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [mc_add_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,single_add_word_thm]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword(:'a) /\
      LENGTH xs + 1 < dimword(:'a) /\
      LENGTH xs + 1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ `LENGTH xs1 < dimword(:'a) /\
      LENGTH xs1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ Q.PAT_X_ASSUM `LENGTH ys1 = LENGTH xs1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h' xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "mc_add_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_add_def,
       LET_DEF,single_add_def,b2n_thm]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def] \\ DECIDE_TAC);

val mc_add_loop2_thm = prove(
  ``!(xs:'a word list) zs xs1 zs1 xs2 zs2 r8 c l.
      (LENGTH zs1 = LENGTH xs1) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < dimword(:'a) /\
      LENGTH xs <= l ==>
      ?r8' r9' l2.
        mc_add_loop2_pre (l,n2w (LENGTH xs + 1),b2w c,r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,zs1 ++ zs ++ zs2) /\
        (mc_add_loop2 (l,n2w (LENGTH xs + 1),b2w c,r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,zs1 ++ zs ++ zs2) =
          (l2,0w,b2w ((SND (mw_add xs (MAP (\x.0w) xs) c))),
           r8',r9',n2w (LENGTH (xs1++xs)),xs1 ++ xs ++ xs2,
           zs1 ++ FST (mw_add xs (MAP (\x.0w) xs) c) ++ zs2)) /\
        l <= l2 + LENGTH xs``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def]
    \\ ONCE_REWRITE_TAC [mc_add_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def,LET_DEF])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [mc_add_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,single_add_word_thm]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword(:'a) /\
      LENGTH xs + 1 < dimword(:'a) /\
      LENGTH xs + 1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ `LENGTH xs1 < dimword(:'a) /\
      LENGTH xs1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "mc_add_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_add_def,
       LET_DEF,single_add_def,b2n_thm]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ DECIDE_TAC)

val mc_add_thm = prove(
  ``!(xs:'a word list) ys zs zs2 l.
      LENGTH ys <= LENGTH xs /\ (LENGTH zs = LENGTH (mw_addv xs ys F)) /\
      LENGTH xs + 1 < dimword(:'a) /\ LENGTH xs + 2 <= l ==>
      ?r1' r2' r8' r9' r10' l2.
        mc_add_pre (l,n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) /\
        (mc_add (l,n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) =
          (l2,r1',r2',r8',r9',n2w (LENGTH (mw_addv xs ys F)),xs,ys,
            mw_addv xs ys F ++ zs2)) /\
        l <= l2 + LENGTH xs + 2``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,mc_add_def,mc_add_pre_def,LET_DEF]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ONCE_REWRITE_TAC [mc_add_loop_def]
  \\ SIMP_TAC (srw_ss()) [LET_DEF,w2n_n2w,word_add_n2w]
  \\ `~((dimword(:'a) <= (LENGTH ys + 1) MOD dimword(:'a)))` by (fs[])
  \\ FULL_SIMP_TAC std_ss []
  \\ (mc_add_loop1_thm |> Q.SPECL [`xs1`,`ys`,`zs`,`[]`,`[]`,`[]`,
         `xs2`,`[]`,`zs2`,`r8`,`r9`,`F`] |> SIMP_RULE std_ss [EVAL ``b2w F``]
      |> GEN_ALL |> MP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,APPEND_NIL] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH xs1 = LENGTH ys` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw_addv_EQ_mw_add,LET_DEF]
  \\ `?qs1 c1. mw_add xs1 ys F = (qs1,c1)` by METIS_TAC [PAIR]
  \\ `?qs2 c2. mw_add xs2 (MAP (\x.0w) xs2) c1 = (qs2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `qs3 = if c2 then [0x1w] else []:'a word list`
  \\ `?zs1 zs3 zs4. (zs = zs1 ++ zs3 ++ zs4) /\
        (LENGTH zs1 = LENGTH xs1) /\
        (LENGTH zs3 = LENGTH xs2) /\
        (LENGTH zs4 = LENGTH qs3)` by
   (IMP_RES_TAC LENGTH_mw_add
    \\ `LENGTH xs1 <= LENGTH zs` by
          (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
    \\ IMP_RES_TAC LESS_EQ_LENGTH \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `xs1'` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH xs2 <= LENGTH xs2'` by
          (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
    \\ IMP_RES_TAC LESS_EQ_LENGTH \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`xs1''`,`xs2''`]
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,LENGTH_APPEND]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ SEP_I_TAC "mc_add_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ (mc_add_loop2_thm |> Q.SPECL [`xs`,`ys`,`xs1`,`zs1`,`[]`] |> GEN_ALL
       |> SIMP_RULE std_ss [GSYM APPEND_ASSOC,APPEND_NIL] |> ASSUME_TAC)
  \\ SEP_I_TAC "mc_add_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (IMP_RES_TAC LENGTH_mw_add \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [b2w_eq]
  \\ REV (Cases_on `c2`) \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.UNABBREV_TAC `qs3`
         \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND_NIL,LENGTH_APPEND]
         \\ fs [])
  \\ `LENGTH xs1 + LENGTH xs2 < dimword(:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC LENGTH_mw_add
  \\ Q.UNABBREV_TAC `qs3` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ Cases_on `zs4` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,word_add_n2w,ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,GSYM LENGTH_APPEND,LUPDATE_LENGTH]
  \\ fs []);

(* subtraction *)

val single_sub_word_def = Define `
  single_sub_word w1 w2 c =
    let (z,c) = single_sub w1 w2 (c <> 0w:'a word) in
      (z:'a word, (b2w c) :'a word)`;

val single_sub_word_thm =
  single_sub_word_def
  |> SIMP_RULE std_ss [LET_DEF]
  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV);

val (mc_sub_loop2_def, _,
     mc_sub_loop2_pre_def, _) =
  tailrec_define "mc_sub_loop2" ``
    (\(l,r1:'a word,r3:'a word,r8:'a word,r9:'a word,r10:'a word,xs,zs).
      if r1 = 0x1w then
        (let r1 = 0x0w:'a word
         in
           (INR (l,r1,r3,r8,r9,r10,xs,zs),T))
      else
        (let r1 = r1 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r8 = EL (w2n r10) xs in
         let cond = cond /\ (r3 <> 0w ==> (r3 = 1w)) in
         let (r8,r3) = single_sub_word r8 r9 r3 in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r8 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r3,r8,r9,r10,xs,zs),cond /\ l <> 0n)))``;

val (mc_sub_loop1_def, _,
     mc_sub_loop1_pre_def, _) =
  tailrec_define "mc_sub_loop1" ``
    (\(l,r1:'a word,r3:'a word,r8:'a word,r9:'a word,r10:'a word,xs,ys,zs).
      if r1 = 0x1w then
        (let r1 = 0x0w:'a word
         in
           (INR (l,r1,r3,r8,r9,r10,xs,ys,zs),T))
      else
        (let r1 = r1 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r8 = EL (w2n r10) xs in
         let cond = cond /\ w2n r10 < LENGTH ys in
         let r9 = EL (w2n r10) ys in
         let cond = cond /\ (r3 <> 0w ==> (r3 = 1w)) in
         let (r8,r3) = single_sub_word r8 r9 r3 in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r8 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r3,r8,r9,r10,xs,ys,zs),cond /\ l <> 0n)))``;

val (mc_sub_loop_def, _,
     mc_sub_loop_pre_def, _) =
  tailrec_define "mc_sub_loop" ``
    (\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r1 = r1 + 0x1w in
       let r2 = r2 + 0x1w in
       let r3 = 1w in
       let r8 = r8 - 0x0w in
       let cond = mc_sub_loop1_pre (l-1,r1,r3,r8,r9,r10,xs,ys,zs) /\ l <> 0n in
       let (l,r1,r3,r8,r9,r10,xs,ys,zs) = mc_sub_loop1 (l-1,r1,r3,r8,r9,r10,xs,ys,zs) in
       let r1 = r2 in
       let r9 = 0x0w in
       let cond = cond /\ mc_sub_loop2_pre (l-1,r1,r3,r8,r9,r10,xs,zs) /\ l <> 0n in
       let (l,r1,r3,r8,r9,r10,xs,zs) = mc_sub_loop2 (l-1,r1,r3,r8,r9,r10,xs,zs)
       in
         (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond)))
  :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word
   list # 'a word list # 'a word list -> (num # 'a word # 'a word # 'a
   word # 'a word # 'a word # 'a word list # 'a word list # 'a word
   list + num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a
   word list # 'a word list # 'a word list) # bool``

val mc_sub_loop_def =
  LIST_CONJ [mc_sub_loop_def,mc_sub_loop_pre_def,
             mc_sub_loop1_def,mc_sub_loop1_pre_def,
             mc_sub_loop2_def,mc_sub_loop2_pre_def]

val (mc_fix_def, _,
     mc_fix_pre_def, _) =
  tailrec_define "mc_fix" ``
    (\(l:num,r8:'a word,r10:'a word,zs:'a word list).
      if r10 = 0x0w then (INR (l,r8,r10,zs),T)
      else
        (let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH zs in
         let r8 = EL (w2n r10) zs
         in
           if r8 = 0x0w then (INL (l-1,r8,r10,zs),cond /\ l <> 0)
           else (let r10 = r10 + 0x1w in (INR (l,r8,r10,zs),cond))))``;

val mc_fix_def =
  LIST_CONJ [mc_fix_def,mc_fix_pre_def]

val (mc_sub_def, _,
     mc_sub_pre_def, _) =
  tailrec_define "mc_sub" ``
    (\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r2 = r2 - r1 in
       let cond = mc_sub_loop_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
       let (l,r1,r2,r8,r9,r10,xs,ys,zs) = mc_sub_loop (l,r1,r2,r8,r9,r10,xs,ys,zs) in
       let cond = cond /\ mc_fix_pre (l-1,r8,r10,zs) /\ l <> 0 in
       let (l,r8,r10,zs) = mc_fix (l-1,r8,r10,zs)
       in
         (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word
     list # 'a word list # 'a word list -> (num # 'a word # 'a word #
     'a word # 'a word # 'a word # 'a word list # 'a word list # 'a
     word list + num # 'a word # 'a word # 'a word # 'a word # 'a word
     # 'a word list # 'a word list # 'a word list) # bool``;

val mc_sub_def =
  LIST_CONJ [mc_sub_def,mc_sub_pre_def]

val mc_fix_thm = prove(
  ``!(zs:'a word list) zs1 r8 l.
      LENGTH zs < dimword(:'a) /\ LENGTH zs <= l ==>
      ?r8' l2.
        mc_fix_pre (l,r8,n2w (LENGTH zs),zs++zs1) /\
        (mc_fix (l,r8,n2w (LENGTH zs),zs++zs1) =
         (l2,r8',n2w (LENGTH (mw_fix zs)),
          mw_fix zs ++ REPLICATE (LENGTH zs - LENGTH (mw_fix zs)) 0w ++ zs1)) /\
        l <= l2 + LENGTH zs``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mc_fix_def,mw_fix_def]
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,ADD1,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n + 1 < k ==> n < k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ REV (Cases_on `x = 0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,REPLICATE,APPEND,
      GSYM APPEND_ASSOC,word_add_n2w] \\ DECIDE_TAC)
  \\ SEP_I_TAC "mc_fix" \\ FULL_SIMP_TAC std_ss [] \\ rfs []
  \\ `LENGTH (mw_fix zs) <= LENGTH zs` by
      FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
  \\ `LENGTH zs + 1 - LENGTH (mw_fix zs) =
        SUC (LENGTH zs - LENGTH (mw_fix zs))` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [REPLICATE_SNOC]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND])

val sub_borrow_lemma = prove(
  ``!h:'a word h':'a word c.
     (dimword(:'a) <= b2n ~c + (w2n h' + w2n (~h))) =
      ~(w2n h' < b2n c + w2n h)``,
  Cases \\ Cases \\ Cases
  \\ `(dimword(:'a) - 1 - n) < dimword(:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [b2n_def,word_1comp_n2w] \\ DECIDE_TAC);

val mc_sub_loop1_thm = prove(
  ``!(xs:'a word list) ys zs xs1 ys1 zs1 xs2 ys2 zs2 c r8 r9 l.
      (LENGTH ys1 = LENGTH xs1) /\ (LENGTH zs1 = LENGTH xs1) /\
      (LENGTH ys = LENGTH xs) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < dimword(:'a) /\
      LENGTH xs <= l ==>
      ?r8' r9' l2.
        mc_sub_loop1_pre (l,n2w (LENGTH xs + 1),b2w c,r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,zs1 ++ zs ++ zs2) /\
        (mc_sub_loop1 (l,n2w (LENGTH xs + 1),b2w c,r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,zs1 ++ zs ++ zs2) =
          (l2,0w,b2w (SND (mw_sub xs ys c)),r8',r9',n2w (LENGTH (xs1++xs)),
           xs1 ++ xs ++ xs2,ys1 ++ ys ++ ys2,
           zs1 ++ FST (mw_sub xs ys c) ++ zs2)) /\
        l <= l2 + LENGTH xs``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def]
    \\ ONCE_REWRITE_TAC [mc_sub_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def,LET_DEF])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [mc_sub_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,single_sub_word_thm]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword(:'a) /\
      LENGTH xs + 1 < dimword(:'a) /\
      LENGTH xs + 1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ `LENGTH xs1 < dimword(:'a) /\
      LENGTH xs1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ Q.PAT_X_ASSUM `LENGTH ys1 = LENGTH xs1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h' xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "mc_sub_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_sub_def,
       LET_DEF,single_sub_def,b2n_thm,single_add_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ DECIDE_TAC);

val mc_sub_loop2_thm = prove(
  ``!(xs:'a word list) zs xs1 zs1 xs2 zs2 c r8 l.
      (LENGTH zs1 = LENGTH xs1) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < dimword(:'a) /\ LENGTH xs <= l ==>
      ?r8' r9' l2.
        mc_sub_loop2_pre (l,n2w (LENGTH xs + 1),b2w c,r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,zs1 ++ zs ++ zs2) /\
        (mc_sub_loop2 (l,n2w (LENGTH xs + 1),b2w c,r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,zs1 ++ zs ++ zs2) =
          (l2,0w,b2w (SND (mw_sub xs [] c)),r8',r9',n2w (LENGTH (xs1++xs)),
           xs1 ++ xs ++ xs2,zs1 ++ FST (mw_sub xs [] c) ++ zs2)) /\
        l <= l2 + LENGTH xs``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def]
    \\ ONCE_REWRITE_TAC [mc_sub_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def,LET_DEF])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [mc_sub_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,single_sub_word_thm]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword(:'a) /\
      LENGTH xs + 1 < dimword(:'a) /\
      LENGTH xs + 1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ `LENGTH xs1 < dimword(:'a) /\
      LENGTH xs1 + 1 < dimword(:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "mc_sub_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_sub_def,
       LET_DEF,single_add_def,b2n_thm,single_sub_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def] \\ DECIDE_TAC);

val mc_sub_thm = prove(
  ``!(xs:'a word list) ys zs zs2 l.
      LENGTH ys <= LENGTH xs /\ (LENGTH zs = LENGTH xs) /\
      LENGTH xs + 1 < dimword(:'a) /\ LENGTH xs + LENGTH xs + 3 <= l ==>
      ?r1' r2' r8' r9' r10' l2.
        mc_sub_pre (l,n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) /\
        (mc_sub (l,n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) =
          (l2,r1',r2',r8',r9',n2w (LENGTH (mw_subv xs ys)),xs,ys,
           mw_subv xs ys ++ REPLICATE (LENGTH xs - LENGTH (mw_subv xs ys)) 0w ++ zs2)) /\
        l <= l2 + LENGTH xs + LENGTH xs + 3``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,mc_sub_def,LET_DEF]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ONCE_REWRITE_TAC [mc_sub_loop_def]
  \\ SIMP_TAC std_ss [LET_DEF,w2n_n2w,word_add_n2w,WORD_LO]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ (mc_sub_loop1_thm |> Q.SPECL [`xs1`,`ys`,`zs`,`[]`,`[]`,`[]`,
           `xs2`,`[]`,`zs2`,`T`]
      |> SIMP_RULE std_ss [EVAL ``b2w T``]
      |> GEN_ALL |> MP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,APPEND_NIL] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH xs1 = LENGTH ys` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw_subv_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [mw_sub_APPEND]
  \\ `?qs1 c1. mw_sub xs1 ys T = (qs1,c1)` by METIS_TAC [PAIR]
  \\ `?qs2 c2. mw_sub xs2 [] c1 = (qs2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `?zs1 zs3. (zs = zs1 ++ zs3) /\
        (LENGTH zs1 = LENGTH xs1) /\
        (LENGTH zs3 = LENGTH xs2)` by
     (IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH qs1 <= LENGTH zs` by DECIDE_TAC
      \\ IMP_RES_TAC LESS_EQ_LENGTH \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`xs1'`,`xs2'`] \\ FULL_SIMP_TAC std_ss []
      \\ sg `LENGTH (xs1' ++ xs2') = LENGTH (qs1 ++ qs2)`
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ SEP_I_TAC "mc_sub_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ fs [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ (mc_sub_loop2_thm |> Q.SPECL [`xs`,`ys`,`xs1`,`zs1`,`[]`] |> GEN_ALL
       |> SIMP_RULE std_ss [GSYM APPEND_ASSOC,APPEND_NIL] |> ASSUME_TAC)
  \\ SEP_I_TAC "mc_sub_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (IMP_RES_TAC LENGTH_mw_sub \\ fs [])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ IMP_RES_TAC LENGTH_mw_sub
  \\ `LENGTH (xs1 ++ xs2) = LENGTH (qs1 ++ qs2)` by fs [LENGTH_APPEND]
  \\ `LENGTH (qs1 ++ qs2) < dimword (:'a) /\
      LENGTH (qs1 ++ qs2) <= l2' − 1` by (fs [] \\ NO_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mc_fix_thm \\ SEP_I_TAC "mc_fix"
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,AC ADD_COMM ADD_ASSOC] \\ fs []);

(* integer addition *)

val (mc_iadd1_def, _,
     mc_iadd1_pre_def, _) =
  tailrec_define "mc_iadd1" ``
    (\(r1,r2,xs,ys).
      (let r0 = 0x0w
       in
         if r1 <+ r2 then
           (let (xs,ys) = (ys,xs) in
            let r0 = 0x1w
            in
              (INR (r1,r2,r0,xs,ys),T))
         else
           (let r8 = r1 in
            let r1 = r2 in
            let r2 = r8
            in
              (INR (r1,r2,r0,xs,ys),T))))
    :'a word # 'a word # 'a word list # 'a word list -> ('a word # 'a
     word # 'a word list # 'a word list + 'a word # 'a word # 'a word
     # 'a word list # 'a word list) # bool``;

val (mc_iadd2_def, _,
     mc_iadd2_pre_def, _) =
  tailrec_define "mc_iadd2" ``
    (\(r1,r2,r10,r12,xs,ys).
      (let r0 = 0x0w
       in
         if r10 = 0x1w then
           (let (xs,ys) = (ys,xs) in
            let r12 = r12 ?? 0x1w in
            let r0 = 0x1w
            in
              (INR (r1,r2,r0,r12,xs,ys),T))
         else
           (let r8 = r1 in
            let r1 = r2 in
            let r2 = r8
            in
              (INR (r1,r2,r0,r12,xs,ys),T))))
    :'a word # 'a word # 'a word # 'a word # 'a word list # 'a word
     list -> ('a word # 'a word # 'a word # 'a word # 'a word list #
     'a word list + 'a word # 'a word # 'a word # 'a word # 'a word
     list # 'a word list) # bool``;

val (mc_iadd3_def, _,
     mc_iadd3_pre_def, _) =
  tailrec_define "mc_iadd3" ``
    (\(r0,xs,ys).
      if r0 = 0x0w then (INR (xs,ys),T)
      else (let (xs,ys) = (ys,xs) in (INR (xs,ys),T)))
    :'a word # 'a word list # 'a word list ->
     ('a word # 'a word list # 'a word list +
      'a word list # 'a word list) # bool``;

val (mc_iadd_def, _,
     mc_iadd_pre_def, _) =
  tailrec_define "mc_iadd" ``
    (\(l,r1,r2,xs,ys,zs).
      (let r10 = r1 in
       let r10 = r10 && 0x1w in
       let r11 = r2 in
       let r11 = r11 && 0x1w
       in
         if r10 = r11 then
           (let r1 = r1 >>> 1 in
            let r2 = r2 >>> 1 in
            let (r1,r2,r0,xs,ys) = mc_iadd1 (r1,r2,xs,ys) in
            let r8 = 0x0w in
            let r9 = r8 in
            let r10 = r8 in
            let cond = mc_add_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
            let (l,r1,r2,r8,r9,r10,xs,ys,zs) =
                  mc_add (l,r1,r2,r8,r9,r10,xs,ys,zs)
            in
            let (xs,ys) = mc_iadd3 (r0,xs,ys) in
            let r10 = r10 << 1 in
            let r10 = r10 + r11
            in
              (INR (l,r10,xs,ys,zs),cond))
         else
           (let r12 = r10 in
            let r10 = r1 in
            let r10 = r10 >>> 1 in
            let r11 = r2 in
            let r11 = r11 >>> 1 in
            let cond = mc_compare_pre (l,r10,r11,xs,ys) in
            let (l,r10,xs,ys) = mc_compare (l,r10,r11,xs,ys)
            in
              if r10 = 0x0w then (INR (l,r10,xs,ys,zs),cond)
              else
                (let (r1,r2,r0,r12,xs,ys) =
                       mc_iadd2 (r1,r2,r10,r12,xs,ys)
                 in
                 let r8 = 0x0w in
                 let r9 = r8 in
                 let r10 = r8 in
                 let r1 = r1 >>> 1 in
                 let r2 = r2 >>> 1 in
                 let cond = cond /\ mc_sub_pre (l,r1,r2,r8,r9,r10,xs,ys,zs)
                 in
                 let (l,r1,r2,r8,r9,r10,xs,ys,zs) =
                       mc_sub (l,r1,r2,r8,r9,r10,xs,ys,zs)
                 in
                 let (xs,ys) = mc_iadd3 (r0,xs,ys) in
                 let r10 = r10 << 1 in
                 let r10 = r10 + r12
                 in
                   (INR (l,r10,xs,ys,zs),cond)))))
    :num # 'a word # 'a word # 'a word list # 'a word list # 'a word
     list -> (num # 'a word # 'a word # 'a word list # 'a word list #
     'a word list + num # 'a word # 'a word list # 'a word list # 'a
     word list) # bool``;

val mc_header_EQ = prove(
  ``(mc_header (s,xs) && 0x1w = mc_header (t,ys) && 0x1w) = (s = t)``,
  FULL_SIMP_TAC std_ss [mc_header_AND_1]
  \\ Cases_on `s` \\ Cases_on `t` \\ EVAL_TAC \\ simp[]);

val b2w_NOT = prove(
  ``!s. b2w s ?? 0x1w = b2w (~s):'a word``,
  Cases \\ rw[b2w_def,b2n_def]);

val mc_iadd_thm = prove(
  ``LENGTH (xs:'a word list) < dimword (:'a) DIV 2 /\
    LENGTH ys < dimword (:'a) DIV 2 /\
    LENGTH xs + LENGTH ys <= LENGTH zs /\ mw_ok xs /\ mw_ok ys /\
    4 * LENGTH xs + 4 * LENGTH ys + 4 <= l ==>
    ?zs1 l2.
      mc_iadd_pre (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
      (mc_iadd (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
        (l2,mc_header (mwi_add (s,xs) (t,ys)),xs,ys,
         SND (mwi_add (s,xs) (t,ys))++zs1)) /\
      (LENGTH (SND (mwi_add (s,xs) (t,ys))++zs1) = LENGTH zs) /\
      l <= l2 + 4 * LENGTH xs + 4 * LENGTH ys + 4``,
  FULL_SIMP_TAC std_ss [mc_iadd_def,mc_iadd_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mc_header_EQ,mwi_add_def,mc_length]
  \\ Cases_on `s <=> t` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC dim63_IMP_dim64 THEN1
   (Cases_on `LENGTH ys <= LENGTH xs` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [mc_iadd1_def,WORD_LO,GSYM NOT_LESS,LET_DEF]
    THEN1
     (ASSUME_TAC mc_add_thm
      \\ `LENGTH (mw_addv xs ys F) <= LENGTH xs + LENGTH ys` by
            FULL_SIMP_TAC std_ss [LENGTH_mw_addv,NOT_LESS]
      \\ `LENGTH (mw_addv xs ys F) <= LENGTH zs` by DECIDE_TAC
      \\ IMP_RES_TAC LESS_EQ_LENGTH
      \\ FULL_SIMP_TAC std_ss []
      \\ SEP_I_TAC "mc_add" \\ POP_ASSUM MP_TAC
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (FULL_SIMP_TAC std_ss [X_LT_DIV] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,mc_iadd3_def,mc_iadd3_pre_def,LET_DEF]
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [mc_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [mc_header_def,AC MULT_COMM MULT_ASSOC]
      \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w] \\ fs [])
    THEN1
     (ASSUME_TAC mc_add_thm
      \\ `LENGTH (mw_addv ys xs F) <= LENGTH ys + LENGTH xs` by
         (`LENGTH xs <= LENGTH ys` by DECIDE_TAC
          \\ FULL_SIMP_TAC std_ss [LENGTH_mw_addv])
      \\ `LENGTH (mw_addv ys xs F) <= LENGTH zs` by DECIDE_TAC
      \\ IMP_RES_TAC LESS_EQ_LENGTH
      \\ FULL_SIMP_TAC std_ss []
      \\ SEP_I_TAC "mc_add" \\ POP_ASSUM MP_TAC
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (FULL_SIMP_TAC std_ss [X_LT_DIV] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,mc_iadd3_def,mc_iadd3_pre_def,LET_DEF]
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [mc_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [mc_header_def,AC MULT_COMM MULT_ASSOC]
      \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w] \\ fs []))
  \\ mp_tac mc_compare_thm
  \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs []
  \\ strip_tac
  \\ FULL_SIMP_TAC std_ss [mw_compare_thm]
  \\ Cases_on `mw2n ys = mw2n xs` \\ FULL_SIMP_TAC std_ss [cmp2w_def]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [mc_header_def,APPEND,LENGTH] \\ fs [])
  \\ Cases_on `mw2n xs < mw2n ys` \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,mc_iadd2_def,LET_DEF]
  THEN1
   (`LENGTH ys <= LENGTH zs` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC mc_sub_thm
    \\ FULL_SIMP_TAC (srw_ss()) [mc_length]
    \\ SEP_I_TAC "mc_sub" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ `mw2n xs <= mw2n ys` by DECIDE_TAC
    \\ IMP_RES_TAC mw2n_LESS
    THEN1 (FULL_SIMP_TAC std_ss [X_LT_DIV] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,mc_iadd3_def,
         mc_iadd3_pre_def,LET_DEF,one_neq_zero_word]
    \\ SIMP_TAC (srw_ss()) [GSYM APPEND_ASSOC,LENGTH_REPLICATE]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [mc_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [mc_header_def,AC MULT_COMM MULT_ASSOC]
      \\ FULL_SIMP_TAC std_ss [b2w_NOT]
      \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w])
    \\ `LENGTH (mw_subv ys xs) <= LENGTH ys` by ASM_SIMP_TAC std_ss [LENGTH_mw_subv]
    \\ DECIDE_TAC)
  \\ Cases_on`2 MOD dimword(:'a) = 0` \\ fs[]
  >- (
    Cases_on`dimword(:'a)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`xs` \\ fs[]
    \\ Cases_on`ys` \\ fs[] )
  \\ Cases_on`2 MOD dimword (:'a) = 1` \\ fs[]
  >- (
    Cases_on`dimword(:'a)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`n'` \\ fs[] )
  THEN1
   (`LENGTH xs <= LENGTH zs` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC mc_sub_thm
    \\ FULL_SIMP_TAC (srw_ss()) [mc_length]
    \\ SEP_I_TAC "mc_sub" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ `mw2n ys <= mw2n xs` by DECIDE_TAC
    \\ IMP_RES_TAC mw2n_LESS
    THEN1 (FULL_SIMP_TAC std_ss [X_LT_DIV] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,mc_iadd3_def,mc_iadd3_pre_def,LET_DEF]
    \\ SIMP_TAC (srw_ss()) [GSYM APPEND_ASSOC,LENGTH_REPLICATE]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [mc_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [mc_header_def,AC MULT_COMM MULT_ASSOC]
      \\ FULL_SIMP_TAC std_ss [b2w_NOT]
      \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w])
    \\ `LENGTH (mw_subv xs ys) <= LENGTH xs` by ASM_SIMP_TAC std_ss [LENGTH_mw_subv]
    \\ DECIDE_TAC));

(* multiplication *)

val (mc_single_mul_add_def, _,
     mc_single_mul_add_pre_def, _) =
  tailrec_define "mc_single_mul_add" ``
    (\(r0,r1,r2,r3).
      (let cond = T in
       let (r0,r2) = single_mul r0 r2 0w in
       let (r0,r4) = single_add_word r0 r1 0w in
       let (r2,r4) = single_add_word r2 0w r4 in
       let (r0,r4) = single_add_word r0 r3 0w in
       let (r2,r4) = single_add_word r2 0w r4 in
         (INR (r0,r1,r2,r3),cond)))
    :'a word # 'a word # 'a word # 'a word -> ('a word # 'a word # 'a
     word # 'a word + 'a word # 'a word # 'a word # 'a word) # bool``;

val mc_single_mul_add_def =
  LIST_CONJ [mc_single_mul_add_def,mc_single_mul_add_pre_def]

val mc_single_mul_add_thm = prove(
  ``mc_single_mul_add_pre (p,k,q,s) /\
    (mc_single_mul_add (p,k,q,s) =
      let (x1,x2) = single_mul_add p q k s in (x1,k,x2,s))``,
  FULL_SIMP_TAC (srw_ss()) [mc_single_mul_add_def,LET_DEF]
  \\ Cases_on `k` \\ Cases_on `s` \\ Cases_on `p` \\ Cases_on `q`
  \\ FULL_SIMP_TAC (srw_ss()) [single_mul_add_def,LET_DEF,single_mul_def,b2n_thm,
       mw_add_def,single_add_def,b2n_def(*,b2w_def*),word_add_n2w,word_mul_n2w,
       single_add_word_def,EVAL ``b2w F``]
  \\ FULL_SIMP_TAC (srw_ss()) [single_mul_add_def,LET_DEF,single_mul_def,b2n_thm,
       mw_add_def,single_add_def,b2n_def,b2w_def,word_add_n2w,word_mul_n2w,
       single_add_word_def]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC]
  \\ assume_tac ZERO_LT_dimword
  \\ qmatch_assum_abbrev_tac`0n < k` \\ pop_assum kall_tac
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  \\ sg `n'' * n''' DIV k + b2n (k <= n + (n'' * n''') MOD k) =
      (n + n'' * n''') DIV k` \\ FULL_SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`n'' * n'''`,`l`) \\ STRIP_TAC
  \\ `(n + l) DIV k = l DIV k + (n + l MOD k) DIV k` by
   (SIMP_TAC std_ss [Once ADD_COMM]
    \\ STRIP_ASSUME_TAC (SIMP_RULE bool_ss [PULL_FORALL] DIVISION
         |> Q.SPECL [`k`,`l`] |> UNDISCH_ALL |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,ADD_DIV_ADD_DIV]
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `k <= n + l MOD k` \\ FULL_SIMP_TAC std_ss [b2n_def]
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ `l MOD k < k` by FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC);

val (mc_mul_pass_def, _,
     mc_mul_pass_pre_def, _) =
  tailrec_define "mc_mul_pass" ``
    (\(l,r1,r8,r9,r10,r11,ys,zs).
      if r9 = r11 then
        (let cond = w2n r10 < LENGTH zs in
         let zs = LUPDATE r1 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INR (l,r1,r9,r10,ys,zs),cond))
      else
        (let cond = w2n r10 < LENGTH zs in
         let r3 = EL (w2n r10) zs in
         let cond = cond /\ w2n r11 < LENGTH ys in
         let r2 = EL (w2n r11) ys in
         let r0 = r8 in
         let cond = cond /\ mc_single_mul_add_pre (r0,r1,r2,r3) in
         let (r0,r1,r2,r3) = mc_single_mul_add (r0,r1,r2,r3) in
         let zs = LUPDATE r0 (w2n r10) zs in
         let r1 = r2 in
         let r10 = r10 + 0x1w in
         let r11 = r11 + 0x1w
         in
           (INL (l-1,r1,r8,r9,r10,r11,ys,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word
     list # 'a word list -> (num # 'a word # 'a word # 'a word # 'a
     word # 'a word # 'a word list # 'a word list + num # 'a word # 'a
     word # 'a word # 'a word list # 'a word list) # bool``;

val (mc_mul_def, _,
     mc_mul_pre_def, _) =
  tailrec_define "mc_mul" ``
    (\(l,r7,r9,r10,r12,xs,ys,zs).
      if r7 = 0x0w then (let r10 = r10 + r9 in (INR (l,r10,xs,ys,zs),T))
      else
        (let r7 = r7 - 0x1w in
         let cond = w2n r12 < LENGTH xs in
         let r8 = EL (w2n r12) xs in
         let r12 = r12 + 0x1w in
         let r11 = 0x0w in
         let r1 = r11 in
         let cond = cond /\ mc_mul_pass_pre (l-1,r1,r8,r9,r10,r11,ys,zs) /\ l <> 0 in
         let (l,r1,r9,r10,ys,zs) = mc_mul_pass (l-1,r1,r8,r9,r10,r11,ys,zs) in
         let r10 = r10 - r9
         in
           (INL (l-1,r7,r9,r10,r12,xs,ys,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word list # 'a
     word list # 'a word list -> (num # 'a word # 'a word # 'a word #
     'a word # 'a word list # 'a word list # 'a word list + num # 'a
     word # 'a word list # 'a word list # 'a word list) # bool``;

val (mc_mul_zero_def, _,
     mc_mul_zero_pre_def, _) =
  tailrec_define "mc_mul_zero" ``
    (\(l:num,r0:'a word,r10:'a word,zs:'a word list).
      if r10 = 0x0w then (INR (l,r10,zs),T)
      else
        (let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH zs in
         let zs = LUPDATE r0 (w2n r10) zs
         in
           (INL (l-1,r0,r10,zs),cond /\ l <> 0)))``;

val (mc_imul1_def, _,
     mc_imul1_pre_def, _) =
  tailrec_define "mc_imul1" ``
    (\(r10:'a word,r11:'a word).
      if r10 = r11
      then let r13 = (0w:'a word) in (INR (r10,r11,r13),T)
      else let r13 = (1w:'a word) in (INR (r10,r11,r13),T))
    :α word # α word -> (α word # α word + α word # α word # α word) # bool``;

val (mc_imul_def, _,
     mc_imul_pre_def, _) =
  tailrec_define "mc_imul" ``
    ( \ (l,r1,r2,xs,ys,zs).
      (let r10 = 0x0w
       in
         if r1 = 0x0w then (INR (l,r10,xs,ys,zs),T)
         else if r2 = 0x0w then (INR (l,r10,xs,ys,zs),T)
         else
           (let r0 = 0x0w in
            let r10 = r2 in
            let r10 = r10 >>> 1 in
            let cond = mc_mul_zero_pre (l-1,r0,r10,zs) /\ l <> 0 in
            let (l,r10,zs) = mc_mul_zero (l-1,r0,r10,zs) in
            let r10 = r1 in
            let r10 = r10 && 0x1w in
            let r11 = r2 in
            let r11 = r11 && 0x1w in
            let (r10,r11,r13) = mc_imul1 (r10,r11) in
            let r7 = r1 in
            let r7 = r7 >>> 1 in
            let r9 = r2 in
            let r9 = r9 >>> 1 in
            let r10 = 0x0w in
            let r12 = 0x0w in
            let cond = cond /\ mc_mul_pre (l-1,r7,r9,r10,r12,xs,ys,zs) /\ l <> 0 in
            let (l,r10,xs,ys,zs) = mc_mul (l-1,r7,r9,r10,r12,xs,ys,zs) in
            let r8 = 0x0w in
            let cond = cond /\ mc_fix_pre (l-1,r8,r10,zs) /\ l <> 0 in
            let (l,r8,r10,zs) = mc_fix (l-1,r8,r10,zs) in
            let r10 = r10 << 1 in
            let r10 = r10 + r13
            in
              (INR (l,r10,xs,ys,zs),cond))))
    :num # 'a word # 'a word # 'a word list # 'a word list # 'a word
     list -> (num # 'a word # 'a word # 'a word list # 'a word list #
     'a word list + num # 'a word # 'a word list # 'a word list # 'a
     word list) # bool``;

val mc_mul_pass_thm = prove(
  ``!(ys:'a word list) ys1 x zs k zs1 zs2 z2 l.
      LENGTH (ys1++ys) < dimword (:'a) /\ (LENGTH zs = LENGTH ys) /\
      LENGTH (zs1++zs) < dimword (:'a) /\ LENGTH ys <= l ==>
      ?r1 l2.
        mc_mul_pass_pre (l,k,x,n2w (LENGTH (ys1++ys)),n2w (LENGTH zs1),
                          n2w (LENGTH ys1),ys1++ys,zs1++zs++z2::zs2) /\
        (mc_mul_pass (l,k,x,n2w (LENGTH (ys1++ys)),n2w (LENGTH zs1),
                       n2w (LENGTH ys1),ys1++ys,zs1++zs++z2::zs2) =
           (l2,r1,n2w (LENGTH (ys1++ys)),n2w (LENGTH (zs1++zs)+1),ys1++ys,
            zs1++(mw_mul_pass x ys zs k)++zs2)) /\
        l <= l2 + LENGTH ys``,
  Induct \\ Cases_on `zs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND_NIL,mw_mul_pass_def,ADD1]
  \\ ONCE_REWRITE_TAC [mc_mul_pass_def,mc_mul_pass_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,n2w_11,w2n_n2w,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,word_add_n2w,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``m+n<k ==> m < k /\ n<k:num``)
  \\ FULL_SIMP_TAC std_ss [ADD1,mc_single_mul_add_thm]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,LUPDATE_LENGTH,NULL,HD]
  \\ Cases_on `single_mul_add x h' k h` \\ FULL_SIMP_TAC std_ss [LET_DEF,TL]
  \\ ONCE_REWRITE_TAC [SNOC_INTRO |> Q.INST [`xs2`|->`[]`] |> REWRITE_RULE [APPEND_NIL]]
  \\ `((LENGTH ys1 + (LENGTH ys + 1)) = (LENGTH (SNOC h' ys1) + LENGTH ys)) /\
      ((LENGTH ys1 + 1) = (LENGTH (SNOC h' ys1))) /\
      ((LENGTH zs1 + 1) = LENGTH (SNOC q zs1))` by (FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "mc_mul_pass" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       LENGTH_APPEND,LENGTH,AC ADD_COMM ADD_ASSOC] \\ DECIDE_TAC)
  |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND,LENGTH] |> GEN_ALL;

val WORD_SUB_LEMMA = prove(
  ``v + -1w * w = v - w``,
  FULL_SIMP_TAC (srw_ss()) []);

val mc_mul_thm = prove(
  ``!(xs:'a word list) ys zs xs1 zs1 zs2 l.
      LENGTH (xs1 ++ xs) < dimword (:'a) /\ LENGTH ys < dimword (:'a) /\
      (LENGTH zs = LENGTH ys) /\ LENGTH (zs1++zs++zs2) < dimword (:'a) /\
      LENGTH xs <= LENGTH zs2 /\ ys <> [] /\
      2 * LENGTH xs + LENGTH xs * LENGTH ys <= l ==>
      ?zs3 l2.
        mc_mul_pre (l,n2w (LENGTH xs),n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH xs1),
                 xs1 ++ xs,ys,zs1 ++ zs ++ zs2) /\
       (mc_mul (l,n2w (LENGTH xs),n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH xs1),
                 xs1 ++ xs,ys,zs1 ++ zs ++ zs2) =
          (l2,n2w (LENGTH (zs1 ++ mw_mul xs ys zs)),xs1++xs,ys,zs1 ++ mw_mul xs ys zs ++ zs3)) /\
       (LENGTH (zs1 ++ zs ++ zs2) = LENGTH (zs1 ++ mw_mul xs ys zs ++ zs3)) /\
       l <= l2 + 2 * LENGTH xs + LENGTH xs * LENGTH ys``,
  Induct \\ ONCE_REWRITE_TAC [mc_mul_def,mc_mul_pre_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH,mw_mul_def,APPEND_NIL,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,word_add_n2w]
  THEN1 (METIS_TAC [])
  \\ NTAC 8 STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``m+n<k ==> m < k /\ n<k:num``)
  \\ IMP_RES_TAC (DECIDE ``SUC n < k ==> n < k``)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,LUPDATE_LENGTH,NULL,HD]
  \\ FULL_SIMP_TAC std_ss [GSYM word_sub_def,ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ Cases_on `zs2` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ ASSUME_TAC mc_mul_pass_thm
  \\ SEP_I_TAC "mc_mul_pass" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [RIGHT_ADD_DISTRIB] \\ fs [])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH (mw_mul_pass h ys zs 0x0w) = LENGTH ys + 1` by (FULL_SIMP_TAC std_ss [LENGTH_mw_mul_pass])
  \\ Cases_on `mw_mul_pass h ys zs 0x0w`
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ `n2w (LENGTH (zs1 ++ zs:'a word list) + 1) + -0x1w * n2w (LENGTH (ys:'a word list)) =
      n2w (LENGTH (SNOC h'' zs1)):'a word` by
   (FULL_SIMP_TAC std_ss [WORD_SUB_LEMMA,LENGTH,LENGTH_APPEND]
    \\ `LENGTH zs1 + LENGTH ys + 1 = (LENGTH zs1 + 1) + LENGTH ys` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,LENGTH_SNOC,ADD1])
  \\ `n2w (LENGTH xs1) + 0x1w = n2w (LENGTH (SNOC h xs1)):'a word` by (FULL_SIMP_TAC std_ss [word_add_n2w,LENGTH_SNOC,ADD1])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ ONCE_REWRITE_TAC [SNOC_INTRO |> Q.INST [`xs2`|->`[]`] |> REWRITE_RULE [APPEND_NIL]]
  \\ SEP_I_TAC "mc_mul" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs [LEFT_ADD_DISTRIB])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [word_add_n2w,TL,LENGTH_SNOC,ADD1,HD,AC ADD_COMM ADD_ASSOC]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul] \\ STRIP_TAC
  \\ full_simp_tac std_ss [DECIDE ``(m+n1=m+n2) <=> (n1 = n2:num)``,GSYM ADD_ASSOC]
  \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,ADD1]
  \\ full_simp_tac std_ss [ADD_ASSOC]
  \\ fs [LENGTH_mw_mul])
  |> Q.SPECL [`xs`,`ys`,`zs`,`[]`,`[]`,`zs2`]
  |> SIMP_RULE std_ss [LENGTH,APPEND] |> GEN_ALL;

val mc_mul_zero_thm = prove(
  ``!zs zs1 l.
      LENGTH zs < dimword(:'a) /\ LENGTH zs <= l ==>
        mc_mul_zero_pre (l,0w:'a word,n2w (LENGTH zs),zs++zs1) /\
        (mc_mul_zero (l,0w,n2w (LENGTH zs),zs++zs1) =
          (l - LENGTH zs,0w,MAP (\x.0w) zs ++ zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ NTAC 4 STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_mul_zero_def,mc_mul_zero_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,LET_DEF]
  \\ NTAC 3 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,ADD1,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n+1<k ==> n<k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
  \\ `LENGTH zs <= l-1` by fs []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,
       APPEND,LUPDATE_LENGTH,MAP_APPEND,MAP] \\ DECIDE_TAC);

val MAP_EQ_MAP_EQ = prove(
  ``!xs ys. (MAP (\x.0w) xs = MAP (\x.0w) ys) = (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val mc_imul1_thm = prove(
  ``mc_imul1_pre (r10,r11) /\
    (mc_imul1 (r10,r11) = (r10,r11,if r10 = r11 then 0w else 1w))``,
  fs [mc_imul1_def,mc_imul1_pre_def] \\ rw []);

val mc_imul_thm = prove(
  ``((mc_header (s,xs) = (0w:'a word)) = (xs = [])) /\
    ((mc_header (t,ys) = 0w) = (ys = [])) /\
    LENGTH xs < dimword (:'a) DIV 2 /\ LENGTH ys < dimword (:'a) DIV 2 /\
    LENGTH xs + LENGTH ys <= LENGTH zs /\ LENGTH zs < dimword (:'a) DIV 2 /\
    3 * LENGTH xs + 3 * LENGTH ys + LENGTH xs * LENGTH ys + 3 <= l ==>
    ?zs1 l2.
      mc_imul_pre (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
      (mc_imul (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
        (l2,mc_header (mwi_mul (s,xs) (t,ys)),xs,ys,
         SND (mwi_mul (s,xs) (t,ys))++zs1)) /\
      (LENGTH (SND (mwi_mul (s,xs) (t,ys))++zs1) = LENGTH zs) /\
      l <= l2 + 3 * LENGTH xs + 3 * LENGTH ys + LENGTH xs * LENGTH ys + 3``,
  FULL_SIMP_TAC std_ss [mc_imul_def,mc_imul_pre_def,LET_DEF,mc_imul1_thm]
  \\ FULL_SIMP_TAC std_ss [mc_header_EQ,mwi_mul_def,mc_length]
  \\ Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [APPEND]
  THEN1 (REPEAT STRIP_TAC \\ EVAL_TAC \\ simp[])
  \\ Cases_on `ys = []` \\ FULL_SIMP_TAC std_ss [APPEND]
  THEN1 (REPEAT STRIP_TAC \\ EVAL_TAC \\ simp[])
  \\ REPEAT STRIP_TAC
  \\ `LENGTH ys <= LENGTH zs` by DECIDE_TAC
  \\ `?qs1 qs2. (zs = qs1 ++ qs2) /\ (LENGTH ys = LENGTH qs1)` by
       METIS_TAC [LESS_EQ_LENGTH]
  \\ `LENGTH qs1 < dimword (:'a)` by (fs [X_LT_DIV] \\ DECIDE_TAC)
  \\ `LENGTH ys <= l-1` by fs []
  \\ REV_FULL_SIMP_TAC std_ss [mc_mul_zero_thm]
  \\ ASSUME_TAC mc_mul_thm
  \\ Q.PAT_X_ASSUM `LENGTH ys = LENGTH qs1` (ASSUME_TAC o GSYM)
  \\ `MAP (\x. 0x0w:'a word) qs1 = MAP (\x. 0x0w) ys` by
       (ASM_SIMP_TAC std_ss [MAP_EQ_MAP_EQ] \\ NO_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "mc_mul" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs [LENGTH_APPEND,X_LT_DIV])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH qs1 < dimword (:'a)` by (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ `LENGTH (mw_mul xs ys (MAP (\x. 0x0w) ys)) < dimword (:'a)` by (FULL_SIMP_TAC (srw_ss()) [LENGTH_mw_mul,LENGTH_MAP,X_LT_DIV] \\ DECIDE_TAC)
  \\ ASSUME_TAC mc_fix_thm \\ SEP_I_TAC "mc_fix" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs [LENGTH_mw_mul])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [mc_header_def,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_REPLICATE,WORD_MUL_LSL,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]
  \\ Q.ABBREV_TAC `ts = mw_mul xs ys (MAP (\x. 0x0w) ys)`
  \\ `LENGTH (mw_fix ts) <= LENGTH ts` by FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
  \\ rpt strip_tac \\ TRY decide_tac
  \\ unabbrev_all_tac \\ fs [LENGTH_mw_mul]);

(* simple div xs into zs and zs into zs *)

val single_div_pre_def = Define `
  single_div_pre r2 r0 r9 <=>
    r9 <> (0x0w:'a word) /\
    (w2n r2 * dimword(:'a) + w2n r0) DIV w2n r9 < dimword(:'a)`;

val (mc_single_div_def, _,
     mc_single_div_pre_def, _) =
  tailrec_define "mc_single_div" ``
    (\(r0,r2,r9).
      (let cond = single_div_pre r2 r0 r9 in
       let (r0,r2) = single_div r2 r0 r9
       in
         (INR (r0,r2,r9),cond)))
    :'a word # 'a word # 'a word -> ('a word # 'a word # 'a word + 'a
    word # 'a word # 'a word) # bool``;

val mc_single_div_def = LIST_CONJ [mc_single_div_def,mc_single_div_pre_def]

val MULT_LEMMA_LEMMA = prove(
  ``!m n. l < k /\ l + k * m < k + k * n ==> m <= n:num``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  THEN1 (REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val MULT_LEMMA = prove(
  ``l < k ==> (l + k * m < k + k * n = m <= n:num)``,
  REPEAT STRIP_TAC \\ REV EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (SUFF_TAC ``k * m <= k * n:num`` \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
    \\ MATCH_MP_TAC LESS_MONO_MULT2 \\ FULL_SIMP_TAC std_ss [])
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ IMP_RES_TAC MULT_LEMMA_LEMMA \\ DECIDE_TAC);

val mc_single_div_thm = prove(
  ``(mc_single_div_pre (x2,x1,y) = x1 <+ y) /\
    (mc_single_div (x2,x1,y) = let (q,r) = single_div x1 x2 y in (q,r,y))``,
  FULL_SIMP_TAC (srw_ss()) [mc_single_div_def,single_div_def,LET_DEF,
       single_div_pre_def]
  \\ Cases_on `y` \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO,DIV_LT_X]
  \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  \\ SIMP_TAC std_ss [Once ADD_COMM] \\ SIMP_TAC std_ss [Once MULT_COMM]
  \\ `w2n x2 < dimword(:'a)` by
   (ASSUME_TAC (w2n_lt |> Q.SPEC `x2`)
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [MULT_LEMMA]
  \\ DECIDE_TAC);

val (mc_simple_div_def, _,
     mc_simple_div_pre_def, _) =
  tailrec_define "mc_simple_div" ``
    (\(l,r2,r9,r10,xs,zs).
      if r10 = 0x0w then (INR (l,r2,r9,r10,xs,zs),T)
      else
        (let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r0 = EL (w2n r10) xs in
         let cond = cond /\ mc_single_div_pre (r0,r2,r9) in
         let (r0,r2,r9) = mc_single_div (r0,r2,r9) in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r0 (w2n r10) zs
         in
           (INL (l-1,r2,r9,r10,xs,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list ->
     (num # 'a word # 'a word # 'a word # 'a word list # 'a word list +
      num # 'a word # 'a word # 'a word # 'a word list # 'a word list) # bool``;

val (mc_simple_div1_def, _,
     mc_simple_div1_pre_def, _) =
  tailrec_define "mc_simple_div1" ``
    (\(l,r2,r9,r10,zs).
      if r10 = 0x0w then (INR (l,r2,r9,r10,zs),T)
      else
        (let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH zs in
         let r0 = EL (w2n r10) zs in
         let cond = cond /\ mc_single_div_pre (r0,r2,r9) in
         let (r0,r2,r9) = mc_single_div (r0,r2,r9) in
         let zs = LUPDATE r0 (w2n r10) zs
         in
           (INL (l-1,r2,r9,r10,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word list -> (num # 'a
    word # 'a word # 'a word # 'a word list + num # 'a word # 'a word
    # 'a word # 'a word list) # bool``;

val mc_simple_div_thm = prove(
  ``!(xs:'a word list) xs1 zs zs1 r2 r9 qs r l.
      LENGTH xs < dimword(:'a) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH xs <= l /\
      (mw_simple_div r2 (REVERSE xs) r9 = (qs,r,T)) ==>
      mc_simple_div_pre (l,r2,r9,n2w (LENGTH xs),xs++xs1,zs++zs1) /\
      (mc_simple_div (l,r2,r9,n2w (LENGTH xs),xs++xs1,zs++zs1) =
         (l - LENGTH xs,r,r9,0w,xs++xs1,REVERSE qs++zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH,Once mc_simple_div_pre_def,
         Once mc_simple_div_def,REVERSE_SNOC_DEF,mw_simple_div_def]
    \\ Q.SPEC_TAC (`qs`,`qs`)
    \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1])
  \\ NTAC 12 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [REVERSE_SNOC,mw_simple_div_def,LET_DEF]
  \\ `(zs = []) \/ ?z zs2. zs = SNOC z zs2` by METIS_TAC [SNOC_CASES]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH])
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC]
  \\ SIMP_TAC std_ss [LENGTH,Once mc_simple_div_pre_def,
         Once mc_simple_div_def,REVERSE_SNOC_DEF,mw_simple_div_def]
  \\ FULL_SIMP_TAC (srw_ss()) [n2w_11,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n+1<k ==> n<k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ Q.PAT_X_ASSUM `LENGTH zs2 = LENGTH xs` (ASSUME_TAC o GSYM)
  \\ `LENGTH zs2 ≤ l - 1` by fs []
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,mc_single_div_thm]
  \\ `?q1 r1. single_div r2 x r9 = (q1,r1)` by METIS_TAC [PAIR]
  \\ `?qs2 r2 c2. mw_simple_div r1 (REVERSE xs) r9 = (qs2,r2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ rfs []
  \\ `LENGTH zs2 ≤ l - 1 /\ (LENGTH zs2 = LENGTH zs2)` by fs []
  \\ res_tac \\ fs []
  \\ Q.PAT_X_ASSUM `q1::qs2 = qs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [REVERSE_SNOC_DEF,SNOC_APPEND,GSYM APPEND_ASSOC,
                           APPEND]);

val mc_simple_div1_thm = prove(
  ``!(zs:'a word list) zs1 r2 r9 qs r l.
      LENGTH zs < dimword(:'a) /\ LENGTH zs <= l /\
      (mw_simple_div r2 (REVERSE zs) r9 = (qs,r,T)) ==>
      mc_simple_div1_pre (l,r2,r9,n2w (LENGTH zs),zs++zs1) /\
      (mc_simple_div1 (l,r2,r9,n2w (LENGTH zs),zs++zs1) =
         (l - LENGTH zs,r,r9,0w,REVERSE qs++zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH,Once mc_simple_div1_pre_def,
         Once mc_simple_div1_def,REVERSE_SNOC_DEF,mw_simple_div_def]
    \\ Q.SPEC_TAC (`qs`,`qs`) \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1])
  \\ NTAC 10 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [REVERSE_SNOC,mw_simple_div_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC]
  \\ SIMP_TAC std_ss [LENGTH,Once mc_simple_div1_pre_def,
         Once mc_simple_div1_def,REVERSE_SNOC_DEF,mw_simple_div_def]
  \\ FULL_SIMP_TAC (srw_ss()) [n2w_11,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n+1<k ==> n<k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,mc_single_div_thm]
  \\ `?q1 r1. single_div r2 x r9 = (q1,r1)` by METIS_TAC [PAIR]
  \\ `?qs2 r2 c2. mw_simple_div r1 (REVERSE zs) r9 = (qs2,r2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ rfs []
  \\ `LENGTH zs ≤ l - 1` by fs []
  \\ res_tac \\ fs []
  \\ Q.PAT_X_ASSUM `q1::qs2 = qs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [REVERSE_SNOC_DEF,SNOC_APPEND,GSYM APPEND_ASSOC,
                           APPEND]);

(* mw_div -- calc_d *)

val (mc_calc_d_def, _,
     mc_calc_d_pre_def, _) =
  tailrec_define "mc_calc_d" ``
    (\(l,r1,r2).
      (if r1 < 0w then (INR (l,r2),T) else
         (let r1 = r1 + r1 in let r2 = r2 + r2 in (INL (l-1,r1,r2),l <> 0))))
    :num # 'a word # 'a word -> (num # 'a word # 'a word + num # 'a word) # bool``;

val mc_calc_d_thm = prove(
  ``!(v1:'a word) d.
      (\(v1,d).
        !l n.
          (v1 <> 0w) /\ dimword (:'a) <= w2n v1 * 2 ** n /\ n <= l ==>
          ?l2.
            mc_calc_d_pre (l,v1,d) /\
            (mc_calc_d (l,v1,d) = (l2,calc_d (v1,d))) /\
            l <= l2 + n) (v1,d)``,
  MATCH_MP_TAC (calc_d_ind)
  \\ FULL_SIMP_TAC std_ss [] \\ rpt STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_calc_d_pre_def,mc_calc_d_def,calc_d_def]
  \\ FULL_SIMP_TAC std_ss [LET_THM,GSYM wordsTheory.word_msb_neg]
  \\ IF_CASES_TAC \\ fs []
  \\ FULL_SIMP_TAC std_ss [GSYM addressTheory.WORD_TIMES2,
       AC WORD_MULT_ASSOC WORD_MULT_COMM]
  \\ Cases_on `n = 0` \\ fs []
  THEN1 (fs [w2n_lt,GSYM NOT_LESS])
  \\ first_x_assum (qspecl_then [`l-1`,`n-1`] mp_tac)
  \\ match_mp_tac IMP_IMP \\ conj_tac THEN1
   (fs [] \\ Cases_on `v1` \\ fs [word_mul_n2w]
    \\ sg `2 * n' < dimword (:'a)`
    \\ fs [] \\ Cases_on `n` \\ fs [EXP]
    \\ fs [word_msb_n2w]
    \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ Cases_on `dimindex (:α)` \\ fs []
    \\ fs [MATCH_MP (DECIDE ``0 < n ==> n <> 0n``) DIMINDEX_GT_0]
    \\ fs [ADD1,dimword_def]
    \\ fs [DIV_EQ_X]
    \\ fs [EXP,EXP_ADD])
  \\ strip_tac \\ fs []
  \\ Cases_on `n` \\ fs []
  \\ fs [w2n_lt,GSYM NOT_LESS])
  |> SIMP_RULE std_ss []
  |> Q.SPECL [`v1`,`d`,`l`,`dimindex (:'a)`]
  |> SIMP_RULE std_ss [GSYM dimword_def,
        MATCH_MP (DECIDE ``0 < n ==> n <> 0n``) ZERO_LT_dimword]
  |> GEN_ALL;

(* mw_div -- mw_div_guess *)

val (mc_single_mul_def, _,
     mc_single_mul_pre_def, _) =
  tailrec_define "mc_single_mul" ``
    (\(r0,r1,r2).
      (let cond = T in
       let (r0,r2) = single_mul r0 r2 0w in
       let (r0,r4) = single_add_word r0 r1 0w in
       let (r2,r4) = single_add_word r2 0w r4
       in
         (INR (r0,r1,r2),cond)))
    :'a word # 'a word # 'a word -> ('a word # 'a word # 'a word + 'a
    word # 'a word # 'a word) # bool``;

val mc_single_mul_def = LIST_CONJ [mc_single_mul_def,mc_single_mul_pre_def]

val single_mul_add_thm  = prove(
  ``single_mul_add p q k s =
      (let (r0,r1,r2,r3) = mc_single_mul_add (p,k,q,s) in
         (r0,r2))``,
  SIMP_TAC std_ss [mc_single_mul_add_thm]
  \\ Q.SPEC_TAC (`single_mul_add p q k s`,`w`)
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD,LET_DEF]);

val single_add_0_F = prove(
  ``(single_add w 0w F = (x,c)) <=> (x = w) /\ ~c``,
  fs [single_add_def,EVAL ``b2w F``,b2n_def,GSYM NOT_LESS,w2n_lt]
  \\ eq_tac \\ rw []);

val mc_single_mul_thm = prove(
  ``mc_single_mul_pre (p,k,q) /\
    (mc_single_mul (p,k,q) =
      let (x1,x2) = single_mul_add p q k 0w in (x1,k,x2))``,
  SIMP_TAC (srw_ss()) [single_mul_add_thm,mc_single_mul_def,LET_DEF,
    mc_single_mul_add_def,single_add_word_def] \\ SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM NOT_LESS,w2n_lt,EVAL ``b2n F``,WORD_ADD_0]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [] \\ fs [single_add_0_F] \\ rw [] \\ fs [single_add_0_F]);

val (mc_mul_by_single2_def, _,
     mc_mul_by_single2_pre_def, _) =
  tailrec_define "mc_mul_by_single2" ``
    (\(r6,r7,r8).
      (let r0 = r6 in
       let r1 = 0x0w in
       let r2 = r7 in
       let cond = mc_single_mul_pre (r0,r1,r2) in
       let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
       let r12 = r0 in
       let r0 = r6 in
       let r1 = r2 in
       let r2 = r8 in
       let cond = cond /\ mc_single_mul_pre (r0,r1,r2) in
       let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
       let r3 = r2 in
       let r2 = r0 in
       let r1 = r12
       in
         (INR (r1,r2,r3,r6,r7,r8),cond)))
    :'a word # 'a word # 'a word -> ('a word # 'a word # 'a word + 'a
     word # 'a word # 'a word # 'a word # 'a word # 'a word) # bool``;

val mc_mul_by_single2_thm = prove(
  ``!r6 r7 r8.
      ?r1 r2 r3.
        mc_mul_by_single2_pre (r6,r7,r8) /\
        (mc_mul_by_single2 (r6,r7,r8) = (r1,r2,r3,r6,r7,r8)) /\
        (mw_mul_by_single r6 [r7; r8] = [r1; r2; r3])``,
  SIMP_TAC std_ss [mw_mul_by_single_def,LENGTH,mw_mul_pass_def,mc_single_mul_thm,
    k2mw_def,HD,TL,mc_mul_by_single2_def,EVAL ``(k2mw 2 0):'a word list``,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ assume_tac ZERO_LT_dimword
  \\ ASM_SIMP_TAC std_ss [mc_mul_by_single2_pre_def,LET_DEF,mc_single_mul_add_def,ZERO_DIV]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ SIMP_TAC std_ss [mc_mul_by_single2_pre_def,LET_DEF,mc_single_mul_add_def]
  \\ SIMP_TAC std_ss [mc_single_mul_thm] \\ EVAL_TAC);

val (mc_cmp3_def, _,
     mc_cmp3_pre_def, _) =
  tailrec_define "mc_cmp3" ``
    (\(r1,r2,r3,r9,r10,r11).
      (let r0 = 0x1w
       in
         if r3 = r11 then
           if r2 = r10 then
             if r1 = r9 then
               (let r0 = 0x0w in (INR (r0,r1,r2,r3,r9,r10,r11),T))
             else if r9 <+ r1 then (INR (r0,r1,r2,r3,r9,r10,r11),T)
             else (let r0 = 0x0w in (INR (r0,r1,r2,r3,r9,r10,r11),T))
           else if r10 <+ r2 then (INR (r0,r1,r2,r3,r9,r10,r11),T)
           else (let r0 = 0x0w in (INR (r0,r1,r2,r3,r9,r10,r11),T))
         else if r11 <+ r3 then (INR (r0,r1,r2,r3,r9,r10,r11),T)
         else (let r0 = 0x0w in (INR (r0,r1,r2,r3,r9,r10,r11),T))))
    :'a word # 'a word # 'a word # 'a word # 'a word # 'a word -> ('a
     word # 'a word # 'a word # 'a word # 'a word # 'a word + 'a word
     # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word) #
     bool``;

val mc_cmp3_thm = prove(
  ``mc_cmp3_pre (r1,r2,r3,r9,r10,r11) /\
    (mc_cmp3 (r1,r2,r3,r9,r10,r11) =
      (if mw_cmp [r9;r10;r11] [r1;r2;r3] = SOME T then 1w else 0w,
       r1,r2,r3,r9,r10,r11))``,
  NTAC 5 (ONCE_REWRITE_TAC [mw_cmp_def])
  \\ SIMP_TAC (srw_ss()) [mc_cmp3_def,mc_cmp3_pre_def,LET_DEF]
  \\ Tactical.REVERSE (Cases_on `r3 = r11`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []
  \\ Tactical.REVERSE (Cases_on `r2 = r10`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []
  \\ Tactical.REVERSE (Cases_on `r1 = r9`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []);

val (mc_cmp_mul2_def, _,
     mc_cmp_mul2_pre_def, _) =
  tailrec_define "mc_cmp_mul2" ``
    (\(r6,r7,r8,r9,r10,r11).
      (let cond = mc_mul_by_single2_pre (r6,r7,r8) in
       let (r1,r2,r3,r6,r7,r8) = mc_mul_by_single2 (r6,r7,r8) in
       let (r0,r1,r2,r3,r9,r10,r11) = mc_cmp3 (r1,r2,r3,r9,r10,r11)
       in
         (INR (r0,r6,r7,r8,r9,r10,r11),cond)))
    :'a word # 'a word # 'a word # 'a word # 'a word # 'a word -> ('a
     word # 'a word # 'a word # 'a word # 'a word # 'a word + 'a word
     # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word) #
     bool``;

val mc_cmp_mul2_thm = prove(
  ``mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) /\
    (mc_cmp_mul2 (r6,r7,r8,r9,r10,r11) =
      ((if mw_cmp [r9;r10;r11] (mw_mul_by_single r6 [r7; r8]) = SOME T
            then 1w else 0w),r6,r7,r8,r9,r10,r11))``,
  SIMP_TAC std_ss [mc_cmp_mul2_pre_def,mc_cmp_mul2_def]
  \\ STRIP_ASSUME_TAC (mc_mul_by_single2_thm |> SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [LET_DEF,mc_cmp3_thm]);

val (mc_sub1_def, _,
     mc_sub1_pre_def, _) =
  tailrec_define "mc_sub1" ``
    (\r6.
      if r6 = 0x0w then (INR r6,T) else (let r6 = r6 - 0x1w in (INR r6,T)))
    :'a word -> ('a word + 'a word) # bool``;

val mc_sub1_thm = prove(
  ``!r6. mc_sub1_pre r6 /\ (mc_sub1 r6 = n2w (w2n r6 - 1))``,
  Cases \\ ASM_SIMP_TAC (srw_ss()) [mc_sub1_pre_def,mc_sub1_def]
  \\ Cases_on `n = 0` \\ FULL_SIMP_TAC std_ss [LET_DEF,GSYM word_sub_def]
  \\ `~(n < 1)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [addressTheory.word_arith_lemma2]);

val (mc_cmp2_def, _,
     mc_cmp2_pre_def, _) =
  tailrec_define "mc_cmp2" ``
    (\(r0,r2,r10,r11).
      (let r1 = 0x1w
       in
         if r2 = r11 then
           if r0 = r10 then (let r1 = 0x0w in (INR (r0,r1,r2,r10,r11),T))
           else if r10 <+ r0 then (INR (r0,r1,r2,r10,r11),T)
           else (let r1 = 0x0w in (INR (r0,r1,r2,r10,r11),T))
         else if r11 <+ r2 then (INR (r0,r1,r2,r10,r11),T)
         else (let r1 = 0x0w in (INR (r0,r1,r2,r10,r11),T))))
    :'a word # 'a word # 'a word # 'a word -> ('a word # 'a word # 'a
     word # 'a word + 'a word # 'a word # 'a word # 'a word # 'a word)
     # bool``;

val mc_cmp2_thm = prove(
  ``mc_cmp2_pre (r0,r2,r10,r11) /\
    (mc_cmp2 (r0,r2,r10,r11) =
      (r0,if mw_cmp [r10;r11] [r0;r2] = SOME T then 1w else 0w,
       r2,r10,r11))``,
  NTAC 5 (ONCE_REWRITE_TAC [mw_cmp_def])
  \\ SIMP_TAC (srw_ss()) [mc_cmp2_def,mc_cmp2_pre_def,LET_DEF]
  \\ Tactical.REVERSE (Cases_on `r2 = r11`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []
  \\ Tactical.REVERSE (Cases_on `r0 = r10`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []);

val (mc_div_test_def, _,
     mc_div_test_pre_def, _) =
  tailrec_define "mc_div_test" ``
    (\(l,r6,r7,r8,r9,r10,r11).
      (let cond = mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) in
       let (r0,r6,r7,r8,r9,r10,r11) = mc_cmp_mul2 (r6,r7,r8,r9,r10,r11)
       in
         if r0 = 0x0w then (INR (l,r6,r7,r8,r9,r10,r11),cond)
         else
           (let r6 = mc_sub1 r6 in
            let r0 = r6 in
            let r1 = 0x0w in
            let r2 = r8 in
            let r3 = r1 in
            let cond = cond /\ mc_single_mul_add_pre (r0,r1,r2,r3) in
            let (r0,r1,r2,r3) = mc_single_mul_add (r0,r1,r2,r3) in
            let r2 = r2 + 0x1w in
            let (r0,r1,r2,r10,r11) = mc_cmp2 (r0,r2,r10,r11)
            in
              if r1 = 0x0w then (INR (l,r6,r7,r8,r9,r10,r11),cond)
              else (INL (l-1,r6,r7,r8,r9,r10,r11),cond /\ l <> 0n))))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word ->
     (num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word +
      num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word) # bool``;

val single_mul_thm = prove(
  ``single_mul_add x y 0w 0w = single_mul x y 0w``,
  SIMP_TAC (srw_ss()) [single_mul_add_def,single_mul_def,LET_DEF,
    mw_add_def,single_add_def,b2n_def,b2w_def,GSYM NOT_LESS,w2n_lt]);

val mw_add_0_1 = prove(
  ``(FST (mw_add [r0;r2] [0w;1w] F) = [r0;r2+1w])``,
  SIMP_TAC (srw_ss()) [mw_add_def,HD,TL,single_add_def,b2w_def,
    LET_DEF,EVAL ``b2n F``,GSYM NOT_LESS,w2n_lt]);

val mc_div_test_lemma = prove(
  ``!q u1 u2 u3 v1 v2 l.
      w2n q <= l ==>
      ?l2.
        mc_div_test_pre (l,q,v2,v1,u3,u2,u1) /\
        (mc_div_test (l,q,v2,v1,u3,u2,u1) =
           (l2,mw_div_test q u1 u2 u3 v1 v2,v2,v1,u3,u2,u1)) /\
        l <= l2 + w2n q``,
  HO_MATCH_MP_TAC mw_div_test_ind \\ rpt strip_tac
  \\ ONCE_REWRITE_TAC [mc_div_test_def,mc_div_test_pre_def,mw_div_test_def]
  \\ SIMP_TAC std_ss [mc_cmp_mul2_thm]
  \\ Cases_on `mw_cmp [u3; u2; u1] (mw_mul_by_single q [v2; v1]) = SOME T`
  \\ ASM_SIMP_TAC std_ss [LET_DEF,GSYM one_neq_zero_word,mc_sub1_thm]
  \\ FULL_SIMP_TAC std_ss [mc_single_mul_add_thm,GSYM single_mul_thm]
  \\ Cases_on `single_mul_add (n2w (w2n q - 1)) v1 0x0w 0x0w`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,mc_cmp2_thm]
  \\ Q.MATCH_ASSUM_RENAME_TAC
       `single_mul_add (n2w (w2n q - 1)) v1 0x0w 0x0w = (q1,q2)`
  \\ FULL_SIMP_TAC std_ss [mw_add_0_1]
  \\ Cases_on `mw_cmp [u2; u1] [q1; q2 + 0x1w] = SOME T`
  \\ FULL_SIMP_TAC std_ss [GSYM one_neq_zero_word]
  \\ Cases_on `w2n q` THEN1 (
    qsuff_tac `mw_cmp [u3; u2; u1] (mw_mul_by_single 0w [v2; v1]) <> SOME T`
    THEN1 fs[] >>
    Q.PAT_ABBREV_TAC `x = mw_mul_by_single 0w [v2;v1]` >>
    Q.PAT_ABBREV_TAC `u = [u3;u2;u1]` >>
    `LENGTH x = LENGTH u` by fs[mw_mul_by_single_lemma,Abbr`x`,Abbr`u`] >>
    `~(mw2n u < mw2n x)` by rw[mw_mul_by_single_lemma,Abbr`x`] >>
    fs[mw_cmp_thm])
  \\ fs [ADD1]
  \\ Cases_on `q` \\ fs [] \\ rw []
  \\ first_x_assum (qspec_then `l-1` mp_tac)
  \\ match_mp_tac IMP_IMP \\ conj_tac \\ fs []);

val mc_div_test_thm = prove(
  ``!q u1 u2 u3 v1 (v2:'a word) l.
      dimword (:'a) <= l ==>
      ?l2.
        mc_div_test_pre (l,q,v2,v1,u3,u2,u1) /\
        (mc_div_test (l,q,v2,v1,u3,u2,u1) =
           (l2,mw_div_test q u1 u2 u3 v1 v2,v2,v1,u3,u2,u1)) /\
        l <= l2 + dimword (:'a)``,
  rw [] \\ assume_tac (Q.SPEC `q` w2n_lt)
  \\ `w2n q <= l` by fs []
  \\ imp_res_tac mc_div_test_lemma
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs []);

val (mc_div_r1_def, _,
     mc_div_r1_pre_def, _) =
  tailrec_define "mc_div_r1" ``
    (\(r0,r1,r2).
      if r2 <+ r1 then
        (let cond = single_div_pre r2 r0 r1 in
         let (r0,r2) = single_div r2 r0 r1
         in
           (INR (r0,r1,r2),cond))
      else (let r0 = 0x0w in let r0 = ~r0 in (INR (r0,r1,r2),T)))
    :'a word # 'a word # 'a word -> ('a word # 'a word # 'a word + 'a
    word # 'a word # 'a word) # bool``;

val mc_div_r1_def = LIST_CONJ [mc_div_r1_def,mc_div_r1_pre_def]

val mc_div_r1_thm = prove(
  ``mc_div_r1 (r0,r1,r2) =
      if r2 <+ r1 then
        (FST (single_div r2 r0 r1),r1,SND (single_div r2 r0 r1))
      else (~0w,r1,r2)``,
  SIMP_TAC (srw_ss()) [mc_div_r1_def,single_div_def,LET_DEF]);

val (mc_div_guess_def, _,
     mc_div_guess_pre_def, _) =
  tailrec_define "mc_div_guess" ``
    (\(l,r7,r8,r9,r10,r11).
      (let r0 = r10 in
       let r1 = r8 in
       let r2 = r11 in
       let cond = mc_div_r1_pre (r0,r1,r2) in
       let (r0,r1,r2) = mc_div_r1 (r0,r1,r2) in
       let r6 = r0 in
       let cond = cond /\ mc_div_test_pre (l-1,r6,r7,r8,r9,r10,r11) /\ l <> 0 in
       let (l,r6,r7,r8,r9,r10,r11) = mc_div_test (l-1,r6,r7,r8,r9,r10,r11)
       in
         (INR (l,r6,r7,r8,r9,r10,r11),cond)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word ->
     (num # 'a word # 'a word # 'a word # 'a word # 'a word +
      num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word) # bool``;

val mc_div_guess_thm = prove(
  ``!u1 u2 u3 v1 v2:'a word.
      dimword (:'a) + 1 <= l ==>
      ?l2.
        (mc_div_guess_pre (l,v2,v1,u3,u2,u1) <=>
           (u1 <+ v1 ==> v1 <> 0w)) /\
        (mc_div_guess (l,v2,v1,u3,u2,u1) =
           (l2,mw_div_guess (u1::u2::u3::us) (v1::v2::vs),v2,v1,u3,u2,u1)) /\
        l <= l2 + dimword (:'a) + 1``,
  rpt strip_tac
  \\ `dimword (:α) ≤ l - 1` by decide_tac
  \\ imp_res_tac mc_div_test_thm
  \\ SIMP_TAC (srw_ss()) [mc_div_guess_def,mc_div_guess_pre_def,
       mc_div_test_thm, mw_div_guess_def,HD,TL,mc_div_r1_thm,LET_DEF]
  \\ SIMP_TAC std_ss [mc_div_r1_def,LET_DEF,WORD_LO,single_div_pre_def]
  \\ REPEAT STRIP_TAC
  \\ IF_CASES_TAC \\ fs []
  \\ SEP_I_TAC "mc_div_test" \\ fs []
  \\ FULL_SIMP_TAC (srw_ss()) [single_div_def]
  \\ FULL_SIMP_TAC std_ss [EVAL ``-1w:'a word``]
  \\ fs [word_2comp_def]
  \\ Cases_on `v1 = 0w` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `v1` \\ FULL_SIMP_TAC (srw_ss()) [single_div_def]
  \\ `0 < n` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [DIV_LT_X]
  \\ Cases_on `u1` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `u2` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on`n` \\ fs[MULT]
  \\ qmatch_rename_tac`(a:num) + b * _ < _ + c  * _`
  \\ qmatch_goalsub_abbrev_tac`b * d`
  \\ `b * d <= c * d` by simp[]
  \\ decide_tac);

(* mw_div -- mw_div_adjust *)

(*

 r1 -- k1
 r6 -- x1, i.e. d
 r7 -- x2
 r8 -- accumulated result
 r9 -- length of ys
 r10 -- points into zs
 r11 -- points into ys
 r12 -- k2

*)

val (mc_adj_cmp_def, _,
     mc_adj_cmp_pre_def, _) =
  tailrec_define "mc_adj_cmp" ``
    (\(r0,r3,r8).
      if r0 = r3 then (INR (r0,r3,r8),T)
      else
        (let r8 = 0x1w
         in
           if r3 <+ r0 then (INR (r0,r3,r8),T)
           else (let r8 = 0x0w in (INR (r0,r3,r8),T))))
    :'a word # 'a word # 'a word -> ('a word # 'a word # 'a word + 'a
    word # 'a word # 'a word) # bool``;

val (mc_adjust_aux_def, _,
     mc_adjust_aux_pre_def, _) =
  tailrec_define "mc_adjust_aux" ``
    (\(l,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs).
      if r9 = r11 then
        (let r0 = r12 in
         let cond = w2n r10 < LENGTH zs in
         let r3 = EL (w2n r10) zs in
         let r10 = r10 + 0x1w in
         let (r0,r3,r8) = mc_adj_cmp (r0,r3,r8)
         in
           (INR (l,r6,r7,r8,r9,r10,r11,ys,zs),cond))
      else
        (let r0 = r6 in
         let cond = w2n r11 < LENGTH ys in
         let r2 = EL (w2n r11) ys in
         let cond = cond /\ mc_single_mul_pre (r0,r1,r2) in
         let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
         let r1 = r12 in
         let r12 = r2 in
         let r2 = r0 in
         let r0 = r7 in
         let cond = cond /\ mc_single_mul_pre (r0,r1,r2) in
         let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
         let r1 = r12 in
         let r12 = r2 in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let r3 = EL (w2n r10) zs in
         let (r0,r3,r8) = mc_adj_cmp (r0,r3,r8) in
         let r11 = r11 + 0x1w in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word #
    'a word # 'a word # 'a word list # 'a word list -> (num # 'a word
    # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word # 'a
    word # 'a word list # 'a word list + num # 'a word # 'a word # 'a
    word # 'a word # 'a word # 'a word # 'a word list # 'a word list)
    # bool``;

val (mc_div_adjust_def, _,
     mc_div_adjust_pre_def, _) =
  tailrec_define "mc_div_adjust" ``
    (\(l,r6,r7,r9,r10,ys,zs).
      (let r1 = 0x0w in
       let r8 = r1 in
       let r11 = r1 in
       let r12 = r1 in
       let cond = mc_adjust_aux_pre (l-1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) /\ l<>0 in
       let (l,r6,r7,r8,r9,r10,r11,ys,zs) =
             mc_adjust_aux (l-1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs)
       in
         if r7 = 0x0w then (INR (l,r6,r7,r9,r10,r11,ys,zs),cond)
         else if r8 = 0x0w then (INR (l,r6,r7,r9,r10,r11,ys,zs),cond)
         else (let r7 = r7 - 0x1w in (INR (l,r6,r7,r9,r10,r11,ys,zs),cond))))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word list # 'a
     word list -> (num # 'a word # 'a word # 'a word # 'a word # 'a
     word list # 'a word list + num # 'a word # 'a word # 'a word # 'a
     word # 'a word # 'a word list # 'a word list) # bool``;

val mc_adj_cmp_thm = prove(
  ``mc_adj_cmp_pre (r1,h,anything) /\
    (mc_adj_cmp (r1,h,if res = SOME T then 0x1w else 0x0w) =
      (r1,h,if mw_cmp_alt [h] [r1] res = SOME T then 0x1w else 0x0w))``,
  SIMP_TAC std_ss [mw_cmp_alt_def,HD,TL,mc_adj_cmp_def,mc_adj_cmp_pre_def,LET_DEF]
  \\ Cases_on `r1 = h` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h <+ r1` \\ FULL_SIMP_TAC std_ss []);

val EL_LENGTH = prove(
  ``(EL (LENGTH xs) (xs ++ y::ys) = y) /\
    (EL (LENGTH xs) (xs ++ y::ys ++ zs) = y)``,
  SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,
    GSYM APPEND_ASSOC,APPEND]);

val SNOC_INTRO = prove(
  ``(xs ++ y::ys = SNOC y xs ++ ys) /\
    (xs ++ y::ys ++ zs = SNOC y xs ++ ys ++ zs)``,
  FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);

val mw_cmp_alt_CONS = prove(
  ``mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys q2 q4) (mw_cmp_alt [z] [q3] res) =
    mw_cmp_alt (z::zs) (q3::mw_mul_by_single2 r6 r7 ys q2 q4) res``,
  SIMP_TAC std_ss [mw_cmp_alt_def,TL,HD]);

val mc_adjust_aux_thm = prove(
  ``!(ys:'a word list) zs ys1 zs1 zs2 res r1 r12 l.
      (LENGTH zs = LENGTH ys + 1) /\ LENGTH (ys1 ++ ys) < dimword (:'a)
                                  /\ LENGTH (zs1 ++ zs) < dimword (:'a) /\
      LENGTH ys <= l ==>
      ?l2.
        mc_adjust_aux_pre (l,r1,r6,r7,if res = SOME T then 1w else 0w,
          n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
          r12,ys1 ++ ys,zs1 ++ zs ++ zs2) /\
        (mc_adjust_aux (l,r1,r6,r7,if res = SOME T then 1w else 0w,
          n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
          r12,ys1 ++ ys,zs1 ++ zs ++ zs2) =
          (l2,r6,r7,if mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys r1 r12) res = SOME T
                 then 1w else 0w,n2w (LENGTH (ys1 ++ ys)),n2w (LENGTH (zs1 ++ zs)),
                 n2w (LENGTH (ys1 ++ ys)),ys1 ++ ys,zs1 ++ zs ++ zs2)) /\
        l <= l2 + LENGTH ys``,
  Induct THEN1
   (SIMP_TAC std_ss [APPEND_NIL,mw_mul_by_single2_def,LENGTH]
    \\ Cases \\ SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1]
    \\ ONCE_REWRITE_TAC [mc_adjust_aux_def,mc_adjust_aux_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND,LENGTH]
    \\ NTAC 7 STRIP_TAC
    \\ `LENGTH zs1 < dimword (:'a)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC,w2n_n2w,
         rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD]
    \\ REWRITE_TAC [mc_adj_cmp_thm] \\ SIMP_TAC std_ss [word_add_n2w]
    \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [mc_adjust_aux_def,mc_adjust_aux_pre_def]
  \\ Cases_on `zs` \\ SIMP_TAC std_ss [LENGTH,ADD1] \\ rpt STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (zs1 ++ z::zs) < dimword (:'a)`
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (ys1 ++ y::ys) < dimword (:'a)`
  \\ STRIP_TAC
  \\ `n2w (LENGTH (ys1 ++ y::ys)) <> n2w (LENGTH ys1):'a word` by
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH ys1 < dimword(:'a)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH,ADD1])
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,mc_adj_cmp_thm,mc_single_mul_add_thm,
        mc_single_mul_thm]
  \\ `LENGTH zs1 < dimword (:'a) /\ LENGTH ys1 < dimword (:'a)` by
       (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH,LET_DEF,mw_mul_by_single2_def]
  \\ `?q1 q2. single_mul_add r6 y r1 0x0w = (q1,q2)` by METIS_TAC [PAIR]
  \\ `?q3 q4. single_mul_add r7 q1 r12 0x0w = (q3,q4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SNOC_INTRO]
  \\ `LENGTH ys ≤ l - 1` by fs []
  \\ first_x_assum (qspecl_then [`zs`,`SNOC y ys1`,`SNOC z zs1`,`zs2`,
        `mw_cmp_alt [z] [q3] res`,`q2`,`q4`,`l-1`] mp_tac)
  \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs []
  \\ strip_tac \\ fs [ADD1]
  \\ FULL_SIMP_TAC std_ss [mw_cmp_alt_CONS])
  |> Q.SPECL [`ys`,`zs`,`[]`,`zs1`,`zs2`,`NONE`,`0w`,`0w`]
  |> SIMP_RULE std_ss [LENGTH,APPEND] |> GEN_ALL;

val mc_div_adjust_thm = prove(
  ``(LENGTH zs = LENGTH ys + 1) /\ LENGTH (ys:'a word list) < dimword (:'a)
                                /\ LENGTH (zs1 ++ zs) < dimword (:'a) /\
    LENGTH ys + 1 <= l ==>
    ?l2.
      mc_div_adjust_pre (l,r6,r7,n2w (LENGTH ys),n2w (LENGTH zs1),
                          ys,zs1 ++ zs ++ zs2) /\
      (mc_div_adjust (l,r6,r7,n2w (LENGTH ys),n2w (LENGTH zs1),
                       ys,zs1 ++ zs ++ zs2) =
        (l2,r6,mw_div_adjust r7 zs (FRONT (mw_mul_by_single r6 ys)),
         n2w (LENGTH ys),n2w (LENGTH (zs1 ++ zs)),n2w (LENGTH ys),
         ys,zs1 ++ zs ++ zs2)) /\
      l <= l2 + LENGTH ys + 1``,
  SIMP_TAC std_ss [mc_div_adjust_def,mc_div_adjust_pre_def,LET_DEF]
  \\ ASSUME_TAC mc_adjust_aux_thm \\ SEP_I_TAC "mc_adjust_aux"
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mw_div_adjust_def] \\ fs []
  \\ SIMP_TAC std_ss [GSYM mw_mul_by_single2_thm]
  \\ `mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys 0x0w 0x0w) NONE =
      mw_cmp zs (mw_mul_by_single2 r6 r7 ys 0x0w 0x0w)` by
   (MATCH_MP_TAC (GSYM mw_cmp_alt_thm)
    \\ SIMP_TAC std_ss [mw_mul_by_single2_thm,LENGTH_mw_mul_by_single]
    \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single,LENGTH_FRONT,
         GSYM LENGTH_NIL] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ `0 < dimword (:'a)` by DECIDE_TAC
  \\ Cases_on `r7` \\ FULL_SIMP_TAC std_ss [w2n_n2w,n2w_11]
  \\ Cases_on `mw_cmp zs (mw_mul_by_single2 r6 (n2w n) ys 0x0w 0x0w) = SOME T`
  \\ FULL_SIMP_TAC std_ss [GSYM one_neq_zero_word]
  \\ Cases_on `n = 0` \\ FULL_SIMP_TAC std_ss [word_arith_lemma2]
  \\ `~(n < 1)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `n` \\ fs [ADD1,GSYM word_add_n2w]);

(* mw_div -- mw_sub *)

val (mc_div_sub_def, _,
     mc_div_sub_pre_def, _) =
  tailrec_define "mc_div_sub" ``
    (\(r0,r3,r8).
      (let cond = ((r8 <> 0w) ==> (r8 = 1w)) in
       let (r3,r8) = single_sub_word r3 r0 r8 in
        (INR (r0,r3,r8),cond)))
    :'a word # 'a word # 'a word -> ('a word # 'a word # 'a word + 'a
    word # 'a word # 'a word) # bool``;

val mc_div_sub_def = LIST_CONJ [mc_div_sub_def,mc_div_sub_pre_def]

val b2n_thm = prove(
  ``b2n = b2n``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ Cases \\ EVAL_TAC);

val mc_div_sub_thm = prove(
  ``mc_div_sub_pre (r0,r3,b2w c) /\
    (mc_div_sub (r0,r3,b2w c) =
       let (r3,c) = single_sub r3 r0 c in
         (r0,r3,b2w c))``,
  SIMP_TAC std_ss [single_sub_def,mc_div_sub_def,LET_DEF,single_sub_word_def]
  \\ fs [] \\ rpt (pairarg_tac \\ fs []));

val (mc_div_sub_loop_def, _,
     mc_div_sub_loop_pre_def, _) =
  tailrec_define "mc_div_sub_loop" ``
    (\(l,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs).
      if r9 = r11 then
        (let r0 = r12 in
         let cond = w2n r10 < LENGTH zs in
         let r3 = EL (w2n r10) zs in
         let cond = cond /\ mc_div_sub_pre (r0,r3,r8) in
         let (r0,r3,r8) = mc_div_sub (r0,r3,r8) in
         let r1 = r3 in
         let zs = LUPDATE r1 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INR (l,r6,r7,r9,r10,r11,ys,zs),cond))
      else
        (let r0 = r6 in
         let cond = w2n r11 < LENGTH ys in
         let r2 = EL (w2n r11) ys in
         let cond = cond /\ mc_single_mul_pre (r0,r1,r2) in
         let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
         let r1 = r12 in
         let r12 = r2 in
         let r2 = r0 in
         let r0 = r7 in
         let cond = cond /\ mc_single_mul_pre (r0,r1,r2) in
         let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
         let r1 = r12 in
         let r12 = r2 in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let r3 = EL (w2n r10) zs in
         let cond = cond /\ mc_div_sub_pre (r0,r3,r8) in
         let (r0,r3,r8) = mc_div_sub (r0,r3,r8) in
         let r0 = r1 in
         let r1 = r3 in
         let zs = LUPDATE r1 (w2n r10) zs in
         let r1 = r0 in
         let r11 = r11 + 0x1w in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word #
    'a word # 'a word # 'a word list # 'a word list -> (num # 'a word
    # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word # 'a
    word # 'a word list # 'a word list + num # 'a word # 'a word # 'a
    word # 'a word # 'a word # 'a word list # 'a word list) # bool``;

val LUPDATE_THM = prove(
  ``(LUPDATE q (LENGTH xs) (SNOC x xs) = SNOC q xs) /\
    (LUPDATE q (LENGTH xs) (SNOC x xs ++ ys) = SNOC q xs ++ ys) /\
    (LUPDATE q (LENGTH xs) (SNOC x xs ++ ys ++ zs) = SNOC q xs ++ ys ++ zs)``,
  SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]);

val mc_div_sub_loop_thm = prove(
  ``!(ys:'a word list) zs ys1 zs1 zs2 c r1 r12 l.
      (LENGTH zs = LENGTH ys + 1) /\ LENGTH (ys1 ++ ys) < dimword (:'a)
                                  /\ LENGTH (zs1 ++ zs) < dimword (:'a) /\
      LENGTH ys <= l ==>
      ?l2.
        mc_div_sub_loop_pre (l,r1,r6,r7,b2w c,
          n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
          r12,ys1 ++ ys,zs1 ++ zs ++ zs2) /\
        (mc_div_sub_loop (l,r1,r6,r7,b2w c,
          n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
          r12,ys1 ++ ys,zs1 ++ zs ++ zs2) =
          (l2,r6,r7,n2w (LENGTH (ys1 ++ ys)),n2w (LENGTH (zs1 ++ zs)),
                 n2w (LENGTH (ys1 ++ ys)),ys1 ++ ys,
           zs1 ++ (FST (mw_sub zs (mw_mul_by_single2 r6 r7 ys r1 r12) c)) ++ zs2)) /\
        l <= l2 + LENGTH ys``,
  Induct THEN1
   (SIMP_TAC std_ss [APPEND_NIL,mw_mul_by_single2_def,LENGTH]
    \\ Cases \\ SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1]
    \\ ONCE_REWRITE_TAC [mc_div_sub_loop_def,mc_div_sub_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND,LENGTH]
    \\ rpt STRIP_TAC
    \\ `LENGTH zs1 < dimword (:'a)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,w2n_n2w,EL_LENGTH]
    \\ FULL_SIMP_TAC std_ss [LUPDATE_THM,APPEND_NIL,SNOC_INTRO]
    \\ FULL_SIMP_TAC std_ss [SNOC_INTRO,mc_div_sub_thm]
    \\ FULL_SIMP_TAC std_ss [mw_sub_def,HD,TL]
    \\ Cases_on `single_sub h r12 c`
    \\ FULL_SIMP_TAC std_ss [LET_DEF,SNOC_INTRO,APPEND_NIL] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [mc_div_sub_loop_def,mc_div_sub_loop_pre_def]
  \\ Cases_on `zs` \\ SIMP_TAC std_ss [LENGTH,ADD1] \\ rpt STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (zs1 ++ z::zs) < dimword (:'a)`
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (ys1 ++ y::ys) < dimword (:'a)`
  \\ STRIP_TAC
  \\ `n2w (LENGTH (ys1 ++ y::ys)) <> n2w (LENGTH ys1):'a word` by
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH ys1 < dimword(:'a)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH,ADD1])
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,mc_adj_cmp_thm,mc_single_mul_add_thm,
        mc_single_mul_thm]
  \\ `LENGTH zs1 < dimword (:'a) /\ LENGTH ys1 < dimword (:'a)` by
       (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH,LET_DEF,mw_mul_by_single2_def]
  \\ `?q1 q2. single_mul_add r6 y r1 0x0w = (q1,q2)` by METIS_TAC [PAIR]
  \\ `?q3 q4. single_mul_add r7 q1 r12 0x0w = (q3,q4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SNOC_INTRO,mc_div_sub_thm]
  \\ FULL_SIMP_TAC std_ss [mw_sub_def,HD,TL]
  \\ Cases_on `single_sub z q3 c`
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ SIMP_TAC std_ss [SNOC_INTRO,LUPDATE_THM]
  \\ `(LENGTH ys1 + 1 = LENGTH (SNOC y ys1)) /\
      (LENGTH zs1 + 1 = LENGTH (SNOC q zs1)) /\
      (LENGTH (SNOC y ys1 ++ ys) = LENGTH (SNOC q ys1 ++ ys)) /\
      LENGTH (SNOC q ys1 ++ ys) < dimword (:'a) /\
      LENGTH (SNOC q zs1 ++ zs) < dimword (:'a)` by
        (FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ Q.PAT_X_ASSUM `!zs. bbb` (MP_TAC o Q.SPECL [`zs`,`SNOC y ys1`,
         `SNOC q zs1`,`zs2`,`r`,`q2`,`q4`,`l-1`])
  \\ fs [] \\ strip_tac \\ fs [ADD1])
  |> Q.SPECL [`ys`,`zs`,`[]`,`zs1`,`zs2`,`T`,`0w`,`0w`]
  |> SIMP_RULE std_ss [LENGTH,APPEND,EVAL ``b2w T``] |> GEN_ALL;


(* mw_div -- mw_div_aux *)

val (mc_div_loop_def, _,
     mc_div_loop_pre_def, _) =
  tailrec_define "mc_div_loop" ``
    (\(l,r7:'a word,r9:'a word,r10:'a word,r11:'a word,
       r14:'a word,r15:'a word,ys:'a word list,zs:'a word list).
      if r10 = 0x0w then (INR (l,r7,r9,r10,r11,r14,r15,ys,zs),T)
      else
        (let r6 = r14 in
         let r3 = r15 in
         let r14 = r7 in
         let r15 = r9 in
         let r16 = r10 in
         let r10 = r10 + r9 in
         let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH zs in
         let r0 = EL (w2n r10) zs in
         let r10 = r10 - 0x1w in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let r1 = EL (w2n r10) zs in
         let r10 = r10 - 0x1w in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let r2 = EL (w2n r10) zs in
         let r11 = r0 in
         let r10 = r1 in
         let r9 = r2 in
         let r7 = r3 in
         let r8 = r6 in
         let cond = cond /\ mc_div_guess_pre (l,r7,r8,r9,r10,r11) in
         let (l,r6,r7,r8,r9,r10,r11) = mc_div_guess (l,r7,r8,r9,r10,r11) in
         let r0 = r6 in
         let r6 = r14 in
         let r9 = r15 in
         let r10 = r16 in
         let r10 = r10 - 0x1w in
         let r15 = r7 in
         let r14 = r8 in
         let r7 = r0 in
         let cond = cond /\ mc_div_adjust_pre (l,r6,r7,r9,r10,ys,zs) in
         let (l,r6,r7,r9,r10,r11,ys,zs) = mc_div_adjust (l,r6,r7,r9,r10,ys,zs) in
         let r10 = r10 - r9 in
         let r10 = r10 - 0x1w in
         let r1 = 0x0w in
         let r8 = r1 in
         let r8 = 1w in
         let r11 = r1 in
         let r12 = r1 in
         let cond =
               cond /\
               mc_div_sub_loop_pre (l-1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) /\ l <> 0
         in
         let (l,r6,r7,r9,r10,r11,ys,zs) =
               mc_div_sub_loop (l-1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs)
         in
         let r10 = r10 - 0x1w in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r7 (w2n r10) zs in
         let r10 = r10 - r9 in
         let r7 = r6
         in
           (INL (l-1,r7,r9,r10,r11,r14,r15,ys,zs),cond /\ l <> 0)))``;

val mc_div_loop_thm = prove(
  ``!(zs1:'a word list) zs ys1 zs2 c r1 r12 l.
      (LENGTH zs = LENGTH ys) /\ LENGTH (zs1 ++ zs ++ zs2) < dimword (:'a) /\
      1 < LENGTH ys /\ LAST (FRONT (mw_mul_by_single d ys)) <> 0x0w /\
      LENGTH zs1 * (dimword (:'a) + 2 * LENGTH ys + 4) <= l ==>
      ?l2.
        let ys1 = (FRONT (mw_mul_by_single d ys)) in
          mc_div_loop_pre (l,d,n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH ys),
            LAST ys1,LAST (BUTLAST ys1),ys,zs1 ++ zs ++ zs2) /\
          (mc_div_loop (l,d,n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH ys),
            LAST ys1,LAST (BUTLAST ys1),ys,zs1 ++ zs ++ zs2) =
            (l2,d,n2w (LENGTH ys),0w,n2w (LENGTH ys),LAST ys1,LAST (BUTLAST ys1),ys,
             (let (qs,rs) = mw_div_aux zs1 zs ys1 in
                rs ++ REVERSE qs ++ zs2))) /\
          l <= l2 + LENGTH zs1 * (dimword (:'a) + 2 * LENGTH ys + 4)``,
  Q.ABBREV_TAC `ys1 = FRONT (mw_mul_by_single d ys)`
  \\ SIMP_TAC std_ss [LET_DEF] \\ HO_MATCH_MP_TAC SNOC_INDUCT
  \\ STRIP_TAC THEN1 (SIMP_TAC std_ss
    [LENGTH,APPEND,Once mw_div_aux_def,APPEND_NIL,
     Once mc_div_loop_def,Once mc_div_loop_pre_def,REVERSE_DEF])
  \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_div_aux_def] \\ NTAC 5 STRIP_TAC
  \\ SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,rich_listTheory.NOT_SNOC_NIL]
  \\ NTAC 4 (SIMP_TAC std_ss [Once LET_DEF])
  \\ Q.ABBREV_TAC `guess = mw_div_guess (REVERSE (x::zs)) (REVERSE ys1)`
  \\ Q.ABBREV_TAC `adj = mw_div_adjust guess (x::zs) ys1`
  \\ Q.ABBREV_TAC `sub = (FST (mw_sub (x::zs) (mw_mul_by_single adj ys1) T))`
  \\ `?qs1 rs1. mw_div_aux zs1 (FRONT sub) ys1 = (qs1,rs1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [mc_div_loop_def,mc_div_loop_pre_def]
  \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH_APPEND]
  \\ IMP_RES_TAC (DECIDE ``n + m + k < d ==> 0 < d /\ n < d:num``)
  \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH_APPEND]
  \\ SIMP_TAC std_ss [LENGTH_SNOC,ADD1,GSYM word_add_n2w,WORD_ADD_SUB,HD,TL]
  \\ SIMP_TAC std_ss [LET_DEF,TL,HD,GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC]
  \\ `(zs1 ++ ([x] ++ (zs ++ zs2))) = (zs1 ++ x::zs ++ zs2)` by
       (FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC] \\ NO_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `~(LENGTH zs1 + 1 + LENGTH ys < 3) /\
      ~(LENGTH zs1 + 1 + LENGTH ys < 2) /\
      ~(LENGTH zs1 + 1 + LENGTH ys < 1) /\
      ~(LENGTH (zs1 ++ x::zs) < 1) /\
      ~(LENGTH (zs1 ++ x::zs) < 1 + LENGTH ys) /\
      (LENGTH zs1 + 1 + LENGTH ys - 3) < dimword (:'a) /\
      (LENGTH zs1 + 1 + LENGTH ys - 2) < dimword (:'a) /\
      (LENGTH zs1 + 1 + LENGTH ys - 1) < dimword (:'a) /\
      (LENGTH zs1 + 1 + LENGTH ys) < dimword (:'a) /\
      (LENGTH (zs1 ++ x::zs) - 1) < dimword (:'a) /\
      ~(LENGTH zs1 + 1 < 1) /\
      ~(LENGTH (zs1 ++ x::zs) < LENGTH ys + 1) /\
      (LENGTH (zs1 ++ x::zs) - (LENGTH ys + 1) = LENGTH zs1)` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_arith_lemma2]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ `(EL (LENGTH zs1 + 1 + LENGTH ys - 3) (zs1 ++ x::zs ++ zs2) =
       LAST (BUTLAST (BUTLAST (x::zs)))) /\
      (EL (LENGTH zs1 + 1 + LENGTH ys - 2) (zs1 ++ x::zs ++ zs2) =
       LAST (BUTLAST (x::zs))) /\
      (EL (LENGTH zs1 + 1 + LENGTH ys - 1) (zs1 ++ x::zs ++ zs2) =
       LAST (x::zs))` by
   (`(LENGTH zs1 + 1 + LENGTH ys - 3 = LENGTH zs1 + (LENGTH (x::zs) - 3)) /\
     (LENGTH zs1 + 1 + LENGTH ys - 2 = LENGTH zs1 + (LENGTH (x::zs) - 2)) /\
     (LENGTH zs1 + 1 + LENGTH ys - 1 = LENGTH zs1 + (LENGTH (x::zs) - 1)) /\
     (LENGTH (x::zs) - 3 < LENGTH (x::zs))` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,DECIDE ``n <= n + m:num``,
         GSYM APPEND_ASSOC,rich_listTheory.EL_APPEND1]
    \\ `(x::zs = []) \/ ?t1 t2. x::zs = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
    \\ `LENGTH ys = LENGTH t2` by
     (`LENGTH (x::zs) = LENGTH (t2 ++ [t1])` by METIS_TAC []
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD1])
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC]
    \\ `(t2 = []) \/ ?t3 t4. t2 = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
         LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ SIMP_TAC std_ss [EL_LENGTH,DECIDE ``n+1+1-2 = n:num``]
    \\ `(t4 = []) \/ ?t5 t6. t4 = SNOC t5 t6` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
         LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ SIMP_TAC std_ss [EL_LENGTH,DECIDE ``n+1+1+1-3 = n:num``])
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (mc_div_guess_thm |> GEN_ALL)
  \\ `dimword (:α) + 1 ≤ l` by
        (fs [LENGTH_APPEND,LEFT_ADD_DISTRIB] \\ NO_TAC)
  \\ SEP_I_TAC "mc_div_guess" \\ FULL_SIMP_TAC std_ss []
  \\ REV_FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`REVERSE (FRONT (FRONT ys1))`,
      `REVERSE (FRONT (FRONT (FRONT (x::zs))))`])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `mw_div_guess
        (LAST (x::zs)::LAST (FRONT (x::zs))::
             LAST (FRONT (FRONT (x::zs)))::REVERSE (FRONT (FRONT (FRONT (x::zs)))))
        (LAST ys1::LAST (FRONT ys1)::REVERSE (FRONT (FRONT ys1))) = guess` by
   (Q.UNABBREV_TAC `guess`
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x1 = x2) /\ (y1 = y2) ==> (f x1 y1 = f x2 y2)``)
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (`LENGTH ys1 = LENGTH ys` by
       (Q.UNABBREV_TAC `ys1`
        \\ FULL_SIMP_TAC std_ss [LENGTH_FRONT,LENGTH_mw_mul_by_single,GSYM LENGTH_NIL]
        \\ DECIDE_TAC)
      \\ `(ys1 = []) \/ ?t1 t2. ys1 = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
      \\ FULL_SIMP_TAC std_ss [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC]
      \\ `(t2 = []) \/ ?t3 t4. t2 = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
      \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
           LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ DECIDE_TAC)
    \\ `(x::zs = []) \/ ?t1 t2. x::zs = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
    THEN1 FULL_SIMP_TAC (srw_ss()) [ADD1] \\ ASM_SIMP_TAC std_ss []
    \\ `LENGTH ys = LENGTH t2` by
     (`LENGTH (x::zs) = LENGTH (SNOC t1 t2)` by METIS_TAC []
      \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH,ADD1])
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC]
    \\ `(t2 = []) \/ ?t3 t4. t2 = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,REVERSE_SNOC,CONS_11]
    \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
         LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ `(t4 = []) \/ ?t5 t6. t4 = SNOC t5 t6` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,REVERSE_SNOC,CONS_11]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 2 (qpat_x_assum `_ <= _` mp_tac)
  \\ NTAC 6 (POP_ASSUM (K ALL_TAC))
  \\ rpt strip_tac
  \\ ASSUME_TAC (GEN_ALL mc_div_adjust_thm)
  \\ SEP_I_TAC "mc_div_adjust" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (fs [])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_arith_lemma2]
  \\ ASSUME_TAC (GEN_ALL mc_div_sub_loop_thm)
  \\ SEP_I_TAC "mc_div_sub_loop" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_arith_lemma2]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ `LENGTH (zs1 ++ x::zs) - (1 + LENGTH ys) = LENGTH zs1` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `LUPDATE adj (LENGTH (zs1 ++ x::zs) - 1) (zs1 ++
        FST (mw_sub (x::zs) (mw_mul_by_single2 d adj ys 0x0w 0x0w) T) ++
        zs2) = zs1 ++ SNOC adj (FRONT sub) ++ zs2` by
   (FULL_SIMP_TAC std_ss [mw_mul_by_single2_thm]
    \\ `LENGTH sub = LENGTH (x::zs)` by
     (Q.UNABBREV_TAC `sub`
      \\ Cases_on `mw_sub (x::zs) (mw_mul_by_single adj ys1) T`
      \\ IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ `(sub = []) \/ ?t3 t4. sub = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,FRONT_SNOC]
    \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
    \\ `LENGTH (zs1 ++ x::zs) - 1 = LENGTH (zs1 ++ t4)` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH])
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,APPEND]
  \\ SEP_I_TAC "mc_div_loop" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (`(LENGTH (FRONT sub) = LENGTH ys)` by
      (Q.UNABBREV_TAC `sub`
       \\ Cases_on `mw_sub (x::zs) (mw_mul_by_single adj ys1) T`
       \\ FULL_SIMP_TAC std_ss []
       \\ IMP_RES_TAC LENGTH_mw_sub
       \\ Cases_on `q = []` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
       \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_FRONT,GSYM LENGTH_NIL,ADD1]
       \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
    \\ fs [])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC (srw_ss()) [GSYM CONJ_ASSOC]
  \\ Cases_on `mw_sub (x::zs) (mw_mul_by_single2 d adj ys 0x0w 0x0w) T`
  \\ IMP_RES_TAC LENGTH_mw_sub
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ fs []);

(* mw_div -- mul_by_single *)

val (mc_mul_by_single_def, _,
     mc_mul_by_single_pre_def, _) =
  tailrec_define "mc_mul_by_single" ``
    (\(l,r1,r8,r9,r10,r11,xs,zs).
      if r9 = r11 then
        (let cond = w2n r10 < LENGTH zs in
         let zs = LUPDATE r1 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INR (l,r1,r8,r9,r10,xs,zs),cond))
      else
        (let cond = w2n r11 < LENGTH xs in
         let r2 = EL (w2n r11) xs in
         let r0 = r8 in
         let r3 = 0x0w in
         let cond = cond /\ mc_single_mul_add_pre (r0,r1,r2,r3) in
         let (r0,r1,r2,r3) = mc_single_mul_add (r0,r1,r2,r3) in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r0 (w2n r10) zs in
         let r1 = r2 in
         let r10 = r10 + 0x1w in
         let r11 = r11 + 0x1w
         in
           (INL (l-1,r1,r8,r9,r10,r11,xs,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word
     list # 'a word list -> (num # 'a word # 'a word # 'a word # 'a
     word # 'a word # 'a word list # 'a word list + num # 'a word # 'a
     word # 'a word # 'a word # 'a word list # 'a word list) # bool``;

val mc_mul_by_single_thm = prove(
  ``!(xs:'a word list) xs1 x zs k zs1 zs2 z2 l.
      LENGTH (xs1++xs) < dimword (:'a) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (zs1++zs) < dimword (:'a) /\ LENGTH xs <= l ==>
      ?r1 l2.
        mc_mul_by_single_pre (l,k,x,n2w (LENGTH (xs1++xs)),n2w (LENGTH zs1),
                          n2w (LENGTH xs1),xs1++xs,zs1++zs++z2::zs2) /\
        (mc_mul_by_single (l,k,x,n2w (LENGTH (xs1++xs)),n2w (LENGTH zs1),
                       n2w (LENGTH xs1),xs1++xs,zs1++zs++z2::zs2) =
           (l2,r1,x,n2w (LENGTH (xs1++xs)),n2w (LENGTH (zs1++zs)+1),xs1++xs,
            zs1++(mw_mul_pass x xs (MAP (K 0w) xs) k)++zs2)) /\
        l <= l2 + LENGTH xs``,
  Induct \\ Cases_on `zs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND_NIL,mw_mul_pass_def,ADD1]
  \\ ONCE_REWRITE_TAC [mc_mul_by_single_def,mc_mul_by_single_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,n2w_11,w2n_n2w,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,word_add_n2w,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH,MAP,HD,TL]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``m+n<k ==> m < k /\ n<k:num``)
  \\ FULL_SIMP_TAC std_ss [ADD1,mc_single_mul_add_thm]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,LUPDATE_LENGTH,NULL,HD]
  \\ Cases_on `single_mul_add x h' k 0w` \\ FULL_SIMP_TAC std_ss [LET_DEF,TL]
  \\ ONCE_REWRITE_TAC [SNOC_INTRO |> Q.INST [`xs2`|->`[]`] |> REWRITE_RULE [APPEND_NIL]]
  \\ `((LENGTH xs1 + (LENGTH xs + 1)) = (LENGTH (SNOC h' xs1) + LENGTH xs)) /\
      ((LENGTH xs1 + 1) = (LENGTH (SNOC h' xs1))) /\
      ((LENGTH zs1 + 1) = LENGTH (SNOC q zs1))` by (FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "mc_mul_by_single" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs [])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       LENGTH_APPEND,LENGTH,AC ADD_COMM ADD_ASSOC] \\ DECIDE_TAC)
  |> Q.SPECL [`xs`,`[]`,`x`,`zs`,`0w`,`[]`]
  |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM k2mw_LENGTH_0,GSYM mw_mul_by_single_def]
  |> GEN_ALL;

(* mw_div -- mul_by_single, top two from ys *)

val (mc_top_two_def, _,
     mc_top_two_pre_def, _) =
  tailrec_define "mc_top_two" ``
    (\(l,r0,r1,r3,r8,r9,r11,ys).
      if r9 = r11 then (let r1 = r3 in (INR (l,r0,r1,r8,r9,r11,ys),T))
      else
        (let r3 = r0 in
         let cond = w2n r11 < LENGTH ys in
         let r2 = EL (w2n r11) ys in
         let r0 = r8 in
         let cond = cond /\ mc_single_mul_pre (r0,r1,r2) in
         let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
         let r1 = r2 in
         let r11 = r11 + 0x1w
         in
           (INL (l-1,r0,r1,r3,r8,r9,r11,ys),cond /\ l<>0)))
    :num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a word #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word # 'a
     word # 'a word # 'a word list + num # 'a word # 'a word # 'a word
     # 'a word # 'a word # 'a word list) # bool``;

val mc_top_two_thm = prove(
  ``!(ys:'a word list) x k1 k2 k3 ys1 l.
      LENGTH (ys1 ++ ys) < dimword (:'a) /\ LENGTH ys <= l ==>
      ?l2.
        mc_top_two_pre (l,k2,k1,k3,
                         x,n2w (LENGTH (ys1++ys)),n2w (LENGTH ys1),ys1++ys) /\
        (mc_top_two (l,k2,k1,k3,
                      x,n2w (LENGTH (ys1++ys)),n2w (LENGTH ys1),ys1++ys) =
                 (l2,FST (SND (mw_mul_pass_top x ys (k1,k2,k3))),
                  SND (SND (mw_mul_pass_top x ys (k1,k2,k3))),x,
                  n2w (LENGTH (ys1++ys)),n2w (LENGTH (ys1++ys)),ys1++ys)) /\
        l <= l2 + LENGTH ys``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,APPEND_NIL]
  \\ ONCE_REWRITE_TAC [mc_top_two_def,mc_top_two_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,n2w_11,mw_mul_pass_top_def]
  \\ rpt STRIP_TAC
  \\ `LENGTH ys1 < dimword (:'a) /\
      LENGTH (ys1 ++ h::ys) <> LENGTH ys1` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH]
  \\ FULL_SIMP_TAC std_ss [mc_single_mul_thm]
  \\ Cases_on `single_mul_add x h k1 0w`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,SNOC_INTRO]
  \\ `(LENGTH ys1 + 1) = (LENGTH (SNOC h ys1))` by
       FULL_SIMP_TAC (srw_ss()) [word_add_n2w,ADD1]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ `LENGTH ys <= l-1` by fs []
  \\ res_tac \\ SEP_I_TAC "mc_top_two"
  \\ rfs [])
  |> Q.SPECL [`ys`,`x`,`0w`,`0w`,`0w`,`[]`] |> DISCH ``1 < LENGTH (ys:'a word list)``
  |> SIMP_RULE std_ss [APPEND_NIL,APPEND,LENGTH,mw_mul_pass_top_thm]
  |> REWRITE_RULE [AND_IMP_INTRO]

(* mw_div -- copy result down *)

val (mc_copy_down_def, _,
     mc_copy_down_pre_def, _) =
  tailrec_define "mc_copy_down" ``
    (\(l,r8,r10,r11,zs).
      if r8 = 0x0w then (INR (l,zs),T)
      else
        (let cond = w2n r10 < LENGTH zs in
         let r0 = EL (w2n r10) zs in
         let r8 = r8 - 0x1w in
         let r10 = r10 + 0x1w in
         let cond = cond /\ w2n r11 < LENGTH zs in
         let zs = LUPDATE r0 (w2n r11) zs in
         let r11 = r11 + 0x1w
         in
           (INL (l-1,r8,r10,r11,zs),cond /\ l <> 0)))
    :num # 'a word # 'a word # 'a word # 'a word list -> (num # 'a
    word # 'a word # 'a word # 'a word list + num # 'a word list) # bool``;

val mc_copy_down_thm = prove(
  ``!(zs0:'a word list) zs1 zs2 zs3 l.
      LENGTH (zs0 ++ zs1 ++ zs2) < dimword (:'a) /\ zs1 <> [] /\
      LENGTH zs2 <= l ==>
      ?zs4 l2.
        mc_copy_down_pre (l,n2w (LENGTH zs2),
          n2w (LENGTH (zs0 ++ zs1)),n2w (LENGTH zs0),zs0 ++ zs1 ++ zs2 ++ zs3) /\
        (mc_copy_down (l,n2w (LENGTH zs2),
          n2w (LENGTH (zs0 ++ zs1)),n2w (LENGTH zs0),zs0 ++ zs1 ++ zs2 ++ zs3) =
           (l2,zs0 ++ zs2 ++ zs4)) /\ (LENGTH zs4 = LENGTH zs1 + LENGTH zs3) /\
        l <= l2 + LENGTH zs2``,
  Induct_on `zs2`
  \\ ONCE_REWRITE_TAC [mc_copy_down_def,mc_copy_down_pre_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND_NIL]
  \\ FULL_SIMP_TAC std_ss [APPEND_11,GSYM APPEND_ASSOC,LENGTH_APPEND]
  \\ REPEAT STRIP_TAC
  \\ `SUC (LENGTH zs2) < dimword (:'a) /\ 0 < dimword (:'a) /\
      (LENGTH zs0 + LENGTH zs1) < dimword (:'a) /\ LENGTH zs0 < dimword (:'a)`
       by (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,ADD1,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_APPEND,APPEND_ASSOC,EL_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs1` \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `z::zs <> []`
  \\ FULL_SIMP_TAC std_ss []
  \\ `(LENGTH (zs0 ++ z::zs) + 1 = LENGTH (SNOC h zs0 ++ SNOC h zs)) /\
      (LENGTH zs0 + 1 = LENGTH (SNOC h zs0))`
       by (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_SNOC] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,GSYM APPEND_ASSOC,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO] \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ Q.PAT_X_ASSUM `!xx.bb` (MP_TAC o Q.SPECL [`SNOC h zs0`,`SNOC h zs`,`zs3`,`l-1`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
    (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_SNOC,NOT_SNOC_NIL] \\ fs [])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `zs4` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_SNOC,NOT_SNOC_NIL]
  \\ fs []) |> Q.SPEC `[]` |> SIMP_RULE std_ss [APPEND,LENGTH];

(* mw_div -- copy xs into zs *)

val (mc_copy_over_def, _,
     mc_copy_over_pre_def, _) =
  tailrec_define "mc_copy_over" ``
    (\(l,r10,xs,zs).
      if r10 = 0x0w then (INR (l,xs,zs),T)
      else
        (let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH xs in
         let r0 = EL (w2n r10) xs in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r0 (w2n r10) zs
         in
           (INL (l-1,r10,xs,zs),cond /\ l<>0)))
    :num # 'a word # 'a word list # 'a word list -> (num # 'a word #
    'a word list # 'a word list + num # 'a word list # 'a word list) # bool``;

val mc_copy_over_thm = prove(
  ``!(xs0:'a word list) zs0 xs zs l.
      (LENGTH zs0 = LENGTH xs0) /\
      LENGTH (zs0++zs) < dimword (:'a) /\
      LENGTH xs0 <= l ==>
      ?l2.
        mc_copy_over_pre (l,n2w (LENGTH xs0),xs0 ++ xs,zs0 ++ zs) /\
        (mc_copy_over (l,n2w (LENGTH xs0),xs0 ++ xs,zs0 ++ zs) =
           (l2,xs0 ++ xs,xs0 ++ zs)) /\
        l <= l2 + LENGTH xs0``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1
   (ONCE_REWRITE_TAC [mc_copy_over_def,mc_copy_over_pre_def]
    \\ SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND])
  \\ rpt STRIP_TAC
  \\ `(zs0 = []) \/ ?x l. zs0 = SNOC x l` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_SNOC]
  \\ `LENGTH xs0 + 1 < dimword (:'a) /\ LENGTH xs0 < dimword (:'a)` by (FULL_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [mc_copy_over_def,mc_copy_over_pre_def]
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH,SNOC_APPEND]
  \\ Q.PAT_X_ASSUM `LENGTH l' = LENGTH xs0` (ASSUME_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [LUPDATE_LENGTH,APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ SEP_I_TAC "mc_copy_over"
  \\ pop_assum mp_tac
  \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs []
  \\ strip_tac \\ fs [])

(* mw_div -- top-level function *)

val (mc_div0_def, _,
     mc_div0_pre_def, _) =
  tailrec_define "mc_div0" ``
    ( \ (l,r0,r1,r3,xs,ys,zs).
         let r6 = r0 in
           if r3 = 0x0w then
             (let r0 = 0x0w in (INR (l,r0,r3,r6,xs,ys,zs),T))
           else
             (let r11 = r0 in
              let r10 = r1 in
              let r0 = 0x0w in
              let cond = mc_mul_zero_pre (l-1,r0,r10,zs) /\ l <> 0 in
              let (l,r10,zs) = mc_mul_zero (l-1,r0,r10,zs) in
              let r10 = r11 in
              let cond = cond /\ mc_copy_over_pre (l-1,r10,xs,zs) /\ l <> 0 in
              let (l,xs,zs) = mc_copy_over (l-1,r10,xs,zs) in
              let r0 = r1
              in
                (INR (l,r0,r3,r6,xs,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word list
     # 'a word list # 'a word list + num # 'a word # 'a word # 'a word
     # 'a word list # 'a word list # 'a word list) # bool``;


val (mc_div1_def, _,
     mc_div1_pre_def, _) =
  tailrec_define "mc_div1" ``
    ( \ (l,r0,r1,r3,xs,ys,zs).
        (let r14 = r3 in
         let r2 = 0x0w in
         let r10 = r2 in
         let cond = w2n r10 < LENGTH ys in
         let r9 = EL (w2n r10) ys in
         let r10 = r0 in
         let r8 = r0 in
         let cond = cond /\ mc_simple_div_pre (l-1,r2,r9,r10,xs,zs) /\ l <> 0 in
         let (l,r2,r9,r10,xs,zs) = mc_simple_div (l-1,r2,r9,r10,xs,zs) in
         let r6 = 0x0w in
         let r0 = r8 in
         let r3 = r14
         in
           if r3 = 0x0w then
             if r2 = 0x0w then (INR (l,r0,r3,r6,xs,ys,zs),cond)
             else (let r6 = 0x1w in (INR (l,r0,r3,r6,xs,ys,zs),cond))
           else
             (let r0 = 0x1w in
              let r10 = 0x0w:'a word in
              let cond = cond /\ w2n r10 < LENGTH zs in
              let zs = LUPDATE r2 (w2n r10) zs
              in
                if r2 = 0x0w then (INR (l,r0,r3,r6,xs,ys,zs),cond)
                else (let r6 = 0x1w in (INR (l,r0,r3,r6,xs,ys,zs),cond)))))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word list
     # 'a word list # 'a word list + num # 'a word # 'a word # 'a word
     # 'a word list # 'a word list # 'a word list) # bool``;

val (mc_div2_def, _,
     mc_div2_pre_def, _) =
  tailrec_define "mc_div2" ``
    (\(l,r7,r8,r10,r11,r18,xs,ys,zs).
         let r9 = r7 in
         let r2 = 0x0w in
         let cond = mc_simple_div1_pre (l-1,r2,r9,r10,zs) /\ l <> 0 in
         let (l,r2,r9,r10,zs) = mc_simple_div1 (l-1,r2,r9,r10,zs) in
         let r9 = r11 in
         let r10 = r9 in
         let r7 = r8 in
         let cond = cond /\ mc_fix_pre (l-1,r8,r10,zs) /\ l <> 0 in
         let (l,r8,r10,zs) = mc_fix (l-1,r8,r10,zs) in
         let r6 = r10 in
         let r10 = r9 in
         let r3 = r18 in
         let r8 = r7
         in
           if r3 = 0x0w then
             (let r11 = 0x0w in
              let cond = cond /\ mc_copy_down_pre (l-1,r8,r10,r11,zs) /\ l<>0 in
              let (l,zs) = mc_copy_down (l-1,r8,r10,r11,zs) in
              let r0 = r7
              in
                (INR (l,r0,r3,r6,xs,ys,zs),cond))
           else (let r0 = r9 in (INR (l,r0,r3,r6,xs,ys,zs),cond)))
   : num # α word # α word # α word # α word # α word # α word list #
     α word list # α word list -> (num # α word # α word # α word # α
     word # α word # α word list # α word list # α word list + num # α
     word # α word # α word # α word list # α word list # α word list)
     # bool``

val (mc_div3_def, _,
     mc_div3_pre_def, _) =
  tailrec_define "mc_div3" ``
    (\(l,r2,r7,r9,r18,r19,xs,ys,zs).
         let r1 = 0x0w in
         let r8 = r2 in
         let r10 = r1 in
         let r11 = r1 in
         let cond = mc_mul_by_single_pre (l-1,r1,r8,r9,r10,r11,xs,zs) /\ l<>0
         in
         let (l,r1,r8,r9,r10,xs,zs) =
               mc_mul_by_single (l-1,r1,r8,r9,r10,r11,xs,zs)
         in
         let r1 = 0x0w in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let zs = LUPDATE r1 (w2n r10) zs in
         let r0 = 0x0w in
         let r1 = r0 in
         let r3 = r0 in
         let r11 = r0 in
         let r9 = r7 in
         let cond = cond /\ mc_top_two_pre (l-1,r0,r1,r3,r8,r9,r11,ys) /\ l <> 0 in
         let (l,r0,r1,r8,r9,r11,ys) = mc_top_two (l-1,r0,r1,r3,r8,r9,r11,ys) in
         let r7 = r8 in
         let r11 = r9 in
         let r10 = r19 in
         let r10 = r10 - r9 in
         let r10 = r10 + 0x2w in
         let r14 = r0 in
         let r15 = r1 in
         let r17 = r10 in
         let cond = cond /\ mc_div_loop_pre (l-1,r7,r9,r10,r11,r14,r15,ys,zs) /\ l<>0 in
         let (l,r7,r9,r10,r11,r14,r15,ys,zs) =
               mc_div_loop (l-1,r7,r9,r10,r11,r14,r15,ys,zs)
         in
         let r8 = r17 in
         let r11 = r9 in
         let r10 = r9 in
         let cond = cond /\ mc_div2_pre (l,r7,r8,r10,r11,r18,xs,ys,zs) in
         let (l,r0,r3,r6,xs,ys,zs) = mc_div2 (l,r7,r8,r10,r11,r18,xs,ys,zs) in
           (INR (l,r0,r3,r6,xs,ys,zs),cond))
  : num # α word # α word # α word # α word # α word # α word list # α
    word list # α word list -> (num # α word # α word # α word # α
    word # α word # α word list # α word list # α word list + num # α
    word # α word # α word # α word list # α word list # α word list)
    # bool``

val (mc_div_def, _,
     mc_div_pre_def, _) =
  tailrec_define "mc_div" ``
    (\(l,r0,r1,r3,xs,ys,zs).
      if r0 <+ r1 then
        (let cond = mc_div0_pre (l,r0,r1,r3,xs,ys,zs) in
         let (l,r0,r3,r6,xs,ys,zs) = mc_div0 (l,r0,r1,r3,xs,ys,zs) in
           (INR (l,r0,r3,r6,xs,ys,zs),cond))
      else if r1 = 0x1w then
        (let cond = mc_div1_pre (l,r0,r1,r3,xs,ys,zs) in
         let (l,r0,r3,r6,xs,ys,zs) = mc_div1 (l,r0,r1,r3,xs,ys,zs) in
           (INR (l,r0,r3,r6,xs,ys,zs),cond))
      else
        (let r18 = r3 in
         let r19 = r0 in
         let r7 = r1 in
         let r9 = r0 in
         let r10 = r1 in
         let r10 = r10 - 0x1w in
         let cond = w2n r10 < LENGTH ys in
         let r1 = EL (w2n r10) ys in
         let r2 = 0x1w in
         let cond = cond /\ mc_calc_d_pre (l-1,r1,r2) /\ l <> 0 in
         let (l,r2) = mc_calc_d (l-1,r1,r2) in
         let cond = cond /\ mc_div3_pre (l,r2,r7,r9,r18,r19,xs,ys,zs) in
         let (l,r0,r3,r6,xs,ys,zs) = mc_div3 (l,r2,r7,r9,r18,r19,xs,ys,zs) in
           (INR (l,r0,r3,r6,xs,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word list
     # 'a word list # 'a word list + num # 'a word # 'a word # 'a word
     # 'a word list # 'a word list # 'a word list) # bool``;

val mc_div_def = mc_div_def
  |> REWRITE_RULE [mc_div0_def,mc_div0_pre_def,
                   mc_div1_def,mc_div1_pre_def,
                   mc_div2_def,mc_div2_pre_def,
                   mc_div3_def,mc_div3_pre_def]

val mc_div_pre_def = mc_div_pre_def
  |> REWRITE_RULE [mc_div0_def,mc_div0_pre_def,
                   mc_div1_def,mc_div1_pre_def,
                   mc_div2_def,mc_div2_pre_def,
                   mc_div3_def,mc_div3_pre_def]

val mw_fix_SNOC = store_thm("mw_fix_SNOC",
 ``mw_fix (SNOC 0w xs) = mw_fix xs``,
  SIMP_TAC std_ss [Once mw_fix_def,FRONT_SNOC,LAST_SNOC] \\ SRW_TAC [] []);

val mw_fix_REPLICATE = prove(
  ``!n. mw_fix (xs ++ REPLICATE n 0w) = mw_fix xs``,
  Induct THEN1 SIMP_TAC std_ss [REPLICATE,APPEND_NIL]
  \\ ASM_SIMP_TAC std_ss [REPLICATE_SNOC,APPEND_SNOC,mw_fix_SNOC]);

val MAP_K_0 = prove(
  ``!xs. MAP (\x. 0x0w) xs = REPLICATE (LENGTH xs) 0x0w``,
  Induct \\ SRW_TAC [] [REPLICATE]);

val mc_div_max_def = Define `
  mc_div_max (xs:'a word list) (ys:'a word list) (zs:'a word list) =
    2 * LENGTH ys + 2 * LENGTH zs + 5 + dimindex (:α) +
    LENGTH xs * (dimword (:α) + 2 * LENGTH ys + 4)`;

val mc_div_thm = prove(
  ``(ys:'a word list) <> [] /\ mw_ok xs /\ mw_ok ys /\
    LENGTH xs + LENGTH ys <= LENGTH zs /\
    LENGTH zs < dimword (:'a) /\ ((res,mod,T) = mw_div xs ys) /\
    mc_div_max xs ys zs <= l ==>
    ?zs2 l2.
      mc_div_pre (l,n2w (LENGTH xs),n2w (LENGTH ys),r3,xs,ys,zs) /\
      (mc_div (l,n2w (LENGTH xs),n2w (LENGTH ys),r3,xs,ys,zs) =
         (l2,n2w (LENGTH (if r3 = 0w then res else mod)),r3,
          n2w (LENGTH (mw_fix mod)),xs,ys,
          (if r3 = 0w then res else mod) ++ zs2)) /\
      (LENGTH zs = LENGTH ((if r3 = 0w then res else mod) ++ zs2)) /\
      ((r3 = 0w) ==> LENGTH zs2 <> 0) /\ LENGTH (mw_fix mod) < dimword (:'a) /\
      l <= l2 + mc_div_max xs ys zs``,
  REWRITE_TAC [mc_div_max_def]
  \\ SIMP_TAC std_ss [mw_div_def,LET_DEF] \\ STRIP_TAC
  \\ `LENGTH xs < dimword (:'a) /\ LENGTH ys < dimword (:'a)` by DECIDE_TAC
  \\ IMP_RES_TAC mw_ok_mw_fix_ID \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ Cases_on `LENGTH xs < LENGTH ys` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `r3 = 0w` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Q.EXISTS_TAC `zs`
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,APPEND]
      \\ ASM_SIMP_TAC std_ss [mc_div_def,mc_div_pre_def,LET_DEF,WORD_LO,
           w2n_n2w, mw_ok_mw_fix_ID,n2w_11,ZERO_LT_dimword,LENGTH_NIL,
           mw_fix_REPLICATE] \\ FULL_SIMP_TAC std_ss [LENGTH,GSYM LENGTH_NIL]
      \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [mc_div_def,mc_div_pre_def,LET_DEF,WORD_LO,
           w2n_n2w, mw_ok_mw_fix_ID,n2w_11,ZERO_LT_dimword,LENGTH_NIL]
    \\ `?zs1 zs2. (zs = zs1 ++ zs2) /\ (LENGTH zs1 = LENGTH ys)` by (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH zs1 ≤ l − 1` by fs []
    \\ ASSUME_TAC mc_mul_zero_thm \\ SEP_I_TAC "mc_mul_zero"
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `?zs3 zs4. (zs1 = zs3 ++ zs4) /\ (LENGTH zs3 = LENGTH xs)` by (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC]
    \\ ASSUME_TAC (mc_copy_over_thm |>
          Q.SPECL [`xs`,`MAP (\x.0w) (zs3:'a word list)`,`[]`,
                   `MAP (\x.0w) (zs4:'a word list) ++ zs2`,
                   `l − 1 − LENGTH (xs ++ zs4:'a word list)-1`]
          |> SIMP_RULE std_ss [LENGTH_MAP,APPEND_NIL,LENGTH_APPEND] |> GEN_ALL)
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,MAP_APPEND,APPEND_ASSOC]
    \\ SEP_I_TAC "mc_copy_over" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH (zs3 ++ zs4) - LENGTH xs = LENGTH zs4` by FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [mw_fix_REPLICATE,mw_ok_mw_fix_ID]
    \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE,GSYM LENGTH_NIL]
    \\ ASM_SIMP_TAC std_ss [MAP_K_0,APPEND_11]
    \\ fs [])
  \\ Cases_on `LENGTH ys = 1` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`?qs r c. mw_simple_div 0x0w (REVERSE xs) (HD ys) = (qs,r,c)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
    \\ `0 < dimword (:'a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [mc_div_def,mc_div_pre_def,LET_DEF,WORD_LO,w2n_n2w,EL]
    \\ `?zs1 zs2. (zs = zs1 ++ zs2) /\ (LENGTH zs1 = LENGTH xs)` by
         (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (mc_simple_div_thm |> Q.SPECL [`xs`,`[]`] |> GEN_ALL
        |> SIMP_RULE std_ss [APPEND_NIL])
    \\ SEP_I_TAC "mc_simple_div" \\ POP_ASSUM MP_TAC
    \\ `LENGTH xs ≤ l − 1` by fs []
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ `(LENGTH xs) = (LENGTH qs)` by
        (IMP_RES_TAC LENGTH_mw_simple_div \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Cases_on `r3 = 0w` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Q.EXISTS_TAC `zs2` \\ Cases_on `r = 0w`
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REVERSE]
      \\ fs []
      \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
      \\ fs [dimword_def])
    \\ FULL_SIMP_TAC std_ss [HD,NOT_CONS_NIL,TL,LENGTH]
    \\ Cases_on `REVERSE qs`
    THEN1 FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [APPEND,LUPDATE_def,LENGTH]
    \\ Q.EXISTS_TAC `t ++ zs2`
    \\ `LENGTH (mw_fix [r]) = if r = 0w then 0 else 1` by (EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC)
    \\ `LENGTH (REVERSE qs) = LENGTH (h::t)` by FULL_SIMP_TAC std_ss []
    \\ `LENGTH (zs1 ++ zs2) = SUC (LENGTH (t ++ zs2))` by (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_REVERSE,LENGTH_APPEND] \\ DECIDE_TAC)
    \\ `LENGTH (t ++ zs2) <> 0` by (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_REVERSE,LENGTH_APPEND] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `r = 0w` \\ FULL_SIMP_TAC std_ss [HD,NOT_CONS_NIL,TL]
    \\ fs [])
  \\ Q.ABBREV_TAC `d = calc_d (LAST ys,0x1w)`
  \\ Q.ABBREV_TAC `xs1 = mw_mul_by_single d xs ++ [0x0w]`
  \\ `?qs1 rs1. (mw_div_aux (BUTLASTN (LENGTH ys) xs1) (LASTN (LENGTH ys) xs1)
           (FRONT (mw_mul_by_single d ys))) = (qs1,rs1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REVERSE]
  \\ `LENGTH ys <> 0` by FULL_SIMP_TAC std_ss [LENGTH_NIL]
  \\ `0 < dimword (:'a) /\ LENGTH ys - 1 < dimword (:'a)` by DECIDE_TAC
  \\ `1 < dimword (:'a) /\ ~(LENGTH ys < 1) /\ 0 < LENGTH ys` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [mc_div_def,mc_div_pre_def,LET_DEF,WORD_LO,
       w2n_n2w,n2w_11,word_arith_lemma2]
  \\ `(LAST ys <> 0w) /\ (EL (LENGTH ys - 1) ys = LAST ys)` by
   (FULL_SIMP_TAC std_ss [mw_ok_def]
    \\ `(ys = []) \/ ?y ys2. ys = SNOC y ys2` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,LAST_SNOC]
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH,SNOC_APPEND])
  \\ assume_tac mc_calc_d_thm
  \\ SEP_I_TAC "mc_calc_d"
  \\ pop_assum mp_tac
  \\ match_mp_tac IMP_IMP
  \\ conj_tac THEN1 (fs [] \\ Cases_on `LAST ys` \\ fs [])
  \\ strip_tac \\ fs []
  \\ `?zs1 zs2. (zs = zs1 ++ zs2) /\ (LENGTH zs1 = LENGTH xs)` by
       (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `zs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  THEN1 (`F` by DECIDE_TAC)
  \\ ASSUME_TAC mc_mul_by_single_thm
  \\ SEP_I_TAC "mc_mul_by_single"
  \\ POP_ASSUM MP_TAC
  \\ match_mp_tac IMP_IMP
  \\ conj_tac THEN1 fs []
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  THEN1 (`F` by DECIDE_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC `zs = zs1 ++ z1::z2::zs2`
  \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single]
  \\ `LENGTH xs + 1 < dimword (:'a)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ `LUPDATE 0x0w (LENGTH xs + 1) (mw_mul_by_single d xs ++ z2::zs2) =
      xs1 ++ zs2` by
   (`LENGTH xs + 1 = LENGTH (mw_mul_by_single d xs)` by
       FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single]
    \\ ASM_SIMP_TAC std_ss [LUPDATE_LENGTH]
    \\ Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND])
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ (mc_top_two_thm |> GEN_ALL |> MP_CANON |> ASSUME_TAC)
  \\ SEP_I_TAC "mc_top_two" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 fs []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ `n2w (LENGTH xs) - n2w (LENGTH ys) + 0x2w:'a word =
      n2w (LENGTH xs1 - LENGTH ys)` by
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w,LENGTH_APPEND,
          LENGTH_mw_mul_by_single,LENGTH] \\ AP_TERM_TAC \\ DECIDE_TAC)
  \\  FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs + 2 = LENGTH xs1` by
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single,LENGTH_APPEND,LENGTH]
    \\ DECIDE_TAC)
  \\ `LENGTH ys <= LENGTH xs1` by DECIDE_TAC
  \\ `?ts1 ts2. (xs1 = ts1 ++ ts2) /\ (LENGTH ts2 = LENGTH ys)` by
        (MATCH_MP_TAC LESS_EQ_LENGTH_ALT \\ FULL_SIMP_TAC std_ss [])
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [BUTLASTN_LENGTH_APPEND,LASTN_LENGTH_APPEND]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ ASSUME_TAC (mc_div_loop_thm |> SIMP_RULE std_ss [LET_DEF] |> GEN_ALL)
  \\ `-1w * n2w (LENGTH ys) + n2w (LENGTH xs) + 2w =
      n2w (LENGTH ts1):'a word` by
         (qpat_x_assum `_ = n2w (LENGTH ts1)` (assume_tac o GSYM)
          \\ full_simp_tac std_ss [WORD_SUB_INTRO] \\ NO_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "mc_div_loop" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ fs []
    \\ rpt conj_tac \\ unabbrev_all_tac
    \\ TRY (MATCH_MP_TAC LAST_FRONT_mw_mul_by_single_NOT_ZERO \\ fs [])
    \\ Cases_on `LENGTH ys` \\ fs []
    \\ Cases_on `n` \\ fs []
    \\ fs [ADD1,GSYM ADD_ASSOC]
    \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH ys = n2 + 2`
    \\ `LENGTH xs = n2 + LENGTH ts1` by fs []
    \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [TL,HD,NOT_CONS_NIL]
  \\ `(LENGTH rs1 = LENGTH ys) /\ (LENGTH qs1 = LENGTH ts1)` by
   (`LENGTH ys = LENGTH (FRONT (mw_mul_by_single d ys))` by
     (FULL_SIMP_TAC std_ss [LENGTH_FRONT,GSYM LENGTH_NIL,
        LENGTH_mw_mul_by_single] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC LENGTH_mw_div_aux
    \\ Q.EXISTS_TAC `ts2` \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `LENGTH rs1 = LENGTH ys` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ ASSUME_TAC mc_simple_div1_thm
  \\ SEP_I_TAC "mc_simple_div1" \\ POP_ASSUM MP_TAC
  \\ `?x1 x2 x3. mw_simple_div 0x0w (REVERSE rs1) d = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ match_mp_tac IMP_IMP \\ conj_tac
  THEN1 (fs []
         \\ Cases_on `LENGTH rs1` \\ fs []
         \\ Cases_on `n` \\ fs []
         \\ fs [ADD1,GSYM ADD_ASSOC]
         \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH ys = n2 + 2`
         \\ `LENGTH xs = n2 + LENGTH ts1` by fs []
         \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB])
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ IMP_RES_TAC LENGTH_mw_simple_div
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
  \\ qpat_abbrev_tac `l5 = _ − 1 − LENGTH x1 − 1n`
  \\ (mc_fix_thm |> Q.SPECL [`REVERSE x1`,`REVERSE qs1 ++ zs2`,
        `n2w (LENGTH (ts1:'a word list))`,`l5`] |> MP_TAC)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs []
         \\ Cases_on `LENGTH x1` \\ fs []
         \\ Cases_on `n` \\ fs []
         \\ fs [ADD1,GSYM ADD_ASSOC]
         \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH ys = n2 + 2`
         \\ `LENGTH xs = n2 + LENGTH ts1` by fs []
         \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
         \\ unabbrev_all_tac \\ fs [])
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
  \\ Q.ABBREV_TAC `tt = mw_fix (REVERSE x1) ++
       REPLICATE (LENGTH x1 - LENGTH (mw_fix (REVERSE x1))) 0x0w`
  \\ `LENGTH tt = LENGTH rs1` by
   (Q.UNABBREV_TAC `tt`
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
    \\ `LENGTH (mw_fix (REVERSE x1)) <= LENGTH (REVERSE x1)` by
          FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
    \\ `LENGTH (REVERSE x1) = LENGTH x1` by SRW_TAC [] []
    \\ DECIDE_TAC)
  \\ Tactical.REVERSE (Cases_on `r3 = 0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.UNABBREV_TAC `tt` \\ FULL_SIMP_TAC std_ss
       [mw_fix_thm |> Q.SPEC `REVERSE xs` |> RW [LENGTH_REVERSE]]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,LENGTH_APPEND,LENGTH_REVERSE]
    \\ ASSUME_TAC (Q.ISPEC `REVERSE (x1:'a word list)` LENGTH_mw_fix)
    \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ fs [ADD1]
    \\ Cases_on `LENGTH rs1` \\ fs []
    \\ Cases_on `n` \\ fs []
    \\ fs [ADD1,GSYM ADD_ASSOC]
    \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH ys = n2 + 2`
    \\ `LENGTH xs = n2 + LENGTH ts1` by fs []
    \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
    \\ unabbrev_all_tac \\ fs [])
  \\ Q.MATCH_ASSUM_RENAME_TAC `l5 ≤ l6 + LENGTH x1`
  \\ MP_TAC (mc_copy_down_thm |> Q.SPECL [`tt`,`REVERSE qs1`,`zs2`,`l6-1`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac std_ss [GSYM LENGTH_NIL]
    \\ Cases_on `LENGTH x1` \\ fs []
    \\ Cases_on `n` \\ fs []
    \\ fs [ADD1,GSYM ADD_ASSOC]
    \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH ys = n2 + 2`
    \\ `LENGTH xs = n2 + LENGTH ts1` by fs []
    \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
    \\ unabbrev_all_tac \\ fs [])
  \\ STRIP_TAC \\ NTAC 3 (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE,APPEND_11]
  \\ `LENGTH (mw_fix (REVERSE x1)) < dimword (:'a)` by
      (`LENGTH (mw_fix (REVERSE x1)) <= LENGTH (REVERSE x1)` by
          FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
       \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH_NIL]
  \\ full_simp_tac std_ss [GSYM LENGTH_NIL] \\ rfs []
  \\ rpt (disch_then (assume_tac))
  \\ Cases_on `LENGTH x1` \\ fs []
  \\ Cases_on `n` \\ fs []
  \\ fs [ADD1,GSYM ADD_ASSOC]
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH ys = n2 + 2`
  \\ `LENGTH xs = n2 + LENGTH ts1` by fs []
  \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
  \\ unabbrev_all_tac \\ fs []);

(* mwi_div -- addv zs [] c *)

val (mc_add1_def, _,
     mc_add1_pre_def, _) =
  tailrec_define "mc_add1" ``
    (\(l,r2,r10,r11,zs).
      if r10 = r11 then
        (let r0 = 0x1w in
         let cond = w2n r10 < LENGTH zs in
         let zs = LUPDATE r0 (w2n r10) zs in
         let r11 = r11 + 0x1w
         in
           (INR (l,r11,zs),cond))
      else
        (let cond = w2n r10 < LENGTH zs in
         let r0 = EL (w2n r10) zs
         in
           if r0 = r2 then
             (let r0 = 0x0w in
              let zs = LUPDATE r0 (w2n r10) zs in
              let r10 = r10 + 0x1w
              in
                (INL (l-1,r2,r10,r11,zs),cond /\ l<>0))
           else
             (let r0 = r0 + 0x1w in
              let zs = LUPDATE r0 (w2n r10) zs
              in
                (INR (l,r11,zs),cond))))
    :num # 'a word # 'a word # 'a word # 'a word list -> (num # 'a
    word # 'a word # 'a word # 'a word list + num # 'a word # 'a word
    list) # bool``;

val (mc_add1_call_def, _,
     mc_add1_call_pre_def, _) =
  tailrec_define "mc_add1_call" ``
    (\(l,r2,r6,r11,zs).
      if r2 = 0x0w then (INR (l,r11,zs),T)
      else if r6 = 0x0w then (INR (l,r11,zs),T)
      else
        (let r2 = 0x0w in
         let r10 = r2 in
         let r2 = ~r2 in
         let cond = mc_add1_pre (l-1,r2,r10,r11,zs) /\ l<>0 in
         let (l,r11,zs) = mc_add1 (l-1,r2,r10,r11,zs)
         in
           (INR (l,r11,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list -> (num # 'a
    word # 'a word # 'a word # 'a word list + num # 'a word # 'a word
    list) # bool``;

val mc_add1_thm = prove(
  ``!(zs:'a word list) zs1 l.
      LENGTH (zs1 ++ zs) + 1 < dimword (:'a) /\ zs2 <> [] /\
      LENGTH zs <= l ==>
      ?rest l2.
        mc_add1_pre (l,~0w,n2w (LENGTH zs1),n2w (LENGTH (zs1 ++ zs)),
                      zs1 ++ zs ++ zs2) /\
        (mc_add1 (l,~0w,n2w (LENGTH zs1),n2w (LENGTH (zs1 ++ zs)),
                   zs1 ++ zs ++ zs2) =
         (l2,n2w (LENGTH (zs1 ++ mw_addv zs [] T)),
             zs1 ++ mw_addv zs [] T ++ rest)) /\
        LENGTH (zs1 ++ mw_addv zs [] T) < dimword (:'a) /\
        (LENGTH (zs1 ++ mw_addv zs [] T ++ rest) = LENGTH (zs1 ++ zs ++ zs2)) /\
        l <= l2 + LENGTH zs``,
  Cases_on `zs2` \\ SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`t`,`zs2`) \\ Q.SPEC_TAC (`h`,`t`) \\ STRIP_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Induct
  \\ SIMP_TAC std_ss [mw_addv_NIL,LENGTH_APPEND,APPEND,APPEND_NIL,LENGTH]
  \\ ONCE_REWRITE_TAC [mc_add1_def,mc_add1_pre_def] \\ REPEAT STRIP_TAC
  \\ `LENGTH zs1 < dimword (:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF,w2n_n2w,LENGTH_APPEND,LENGTH,
         word_add_n2w,n2w_11,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,APPEND_11,CONS_11]
  THEN1 (fs [])
  \\ `(LENGTH zs1 + SUC (LENGTH zs)) < dimword (:'a) /\
      LENGTH zs1 <> LENGTH zs1 + SUC (LENGTH zs)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF,w2n_n2w,LENGTH_APPEND,LENGTH,
       word_add_n2w,n2w_11,LUPDATE_LENGTH,EL_LENGTH]
  \\ Tactical.REVERSE (Cases_on `h = ~0x0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.EXISTS_TAC `t::zs2`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,LENGTH]
    \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.PAT_X_ASSUM `!zss.bbb` (qspecl_then [`SNOC 0w zs1`,`l-1`] mp_tac)
  \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs []
  \\ strip_tac \\ fs [ADD1,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] \\ fs [])
  |> Q.SPECL [`zs`,`[]`]
  |> SIMP_RULE std_ss [APPEND,LENGTH];

(* mwi_div -- subtraction *)

val (mc_div_sub_aux1_def, _,
     mc_div_sub_aux1_pre_def, _) =
  tailrec_define "mc_div_sub_aux1" ``
    (\(l,r1:'a word,r4:'a word,r8:'a word,r9:'a word,r10:'a word,ys,zs).
      if r1 = 0x1w then
        (let r1 = 0x0w:'a word
         in
           (INR (l,r1,r4,r8,r9,r10,ys,zs),T))
      else
        (let r1 = r1 - 0x1w in
         let cond = w2n r10 < LENGTH ys in
         let r8 = EL (w2n r10) ys in
         let cond = cond /\ w2n r10 < LENGTH zs in
         let r9 = EL (w2n r10) zs in
         let cond = cond /\ ((r4 <> 0w) ==> (r4 = 1w)) in
         let (r8,r4) = single_sub_word r8 r9 r4 in
         let zs = LUPDATE r8 (w2n r10) zs in
         let r10 = r10 + 0x1w
         in
           (INL (l-1,r1,r4,r8,r9,r10,ys,zs),cond /\ l<>0n)))``;

val (mc_div_sub_aux_def, _,
     mc_div_sub_aux_pre_def, _) =
  tailrec_define "mc_div_sub_aux" ``
    (\(l,r1,r8,r9,ys,zs).
      (let r10 = 0x0w in
       let r1 = r1 + 0x1w in
       let r4 = 1w in
       let cond = mc_div_sub_aux1_pre (l-1,r1,r4,r8,r9,r10,ys,zs) /\ l<>0 in
       let (l,r1,r4,r8,r9,r10,ys,zs) = mc_div_sub_aux1 (l-1,r1,r4,r8,r9,r10,ys,zs)
       in
         (INR (l,r1,r4,r8,r9,r10,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list
    -> (num # 'a word # 'a word # 'a word # 'a word list # 'a word
    list + num # 'a word # 'a word # 'a word # 'a word # 'a word # 'a
    word list # 'a word list) # bool``;

val mc_div_sub_aux_def =
  LIST_CONJ [mc_div_sub_aux_def,mc_div_sub_aux_pre_def,
             mc_div_sub_aux1_def,mc_div_sub_aux1_pre_def]

val (mc_div_sub1_def, _,
     mc_div_sub1_pre_def, _) =
  tailrec_define "mc_div_sub1" ``
    (\(l,r1,r8,r9,ys,zs).
      (let cond = mc_div_sub_aux_pre (l,r1,r8,r9,ys,zs) in
       let (l,r1,r4,r8,r9,r10,ys,zs) = mc_div_sub_aux (l,r1,r8,r9,ys,zs)
       in
         (INR (l,r1,r8,r9,r10,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list
     -> (num # 'a word # 'a word # 'a word # 'a word list # 'a word
     list + num # 'a word # 'a word # 'a word # 'a word # 'a word list
     # 'a word list) # bool``;

val mc_div_sub1_def =
  LIST_CONJ [mc_div_sub1_def,mc_div_sub1_pre_def]

val (mc_div_sub_call_def, _,
     mc_div_sub_call_pre_def, _) =
  tailrec_define "mc_div_sub_call" ``
    (\(l,r1,r2,r6,ys,zs).
      if r2 = 0x0w then (INR (l,r6,ys,zs),T)
      else if r6 = 0x0w then (INR (l,r6,ys,zs),T)
      else
        (let r8 = r6 in
         let r9 = r6 in
         let r3 = r1 in
         let cond = mc_div_sub1_pre (l,r1,r8,r9,ys,zs) in
         let (l,r1,r8,r9,r10,ys,zs) = mc_div_sub1 (l,r1,r8,r9,ys,zs) in
         let r10 = r3 in
         let cond = cond /\ mc_fix_pre (l-1,r8,r10,zs) /\ l<>0 in
         let (l,r8,r10,zs) = mc_fix (l-1,r8,r10,zs) in
         let r6 = r10
         in
           (INR (l,r6,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list ->
     (num # 'a word # 'a word # 'a word # 'a word list # 'a word list +
      num # 'a word # 'a word list # 'a word list) # bool``;

val mc_div_sub_aux_thm = prove(
  ``!(ys:'a word list) zs ys1 zs1 ys2 zs2 c r8 r9 l.
      (LENGTH zs1 = LENGTH ys1) /\ (LENGTH zs = LENGTH ys) /\
      LENGTH (zs1 ++ zs) + 1 < dimword (:'a) /\ LENGTH ys <= l ==>
      ?r8' r9' z_af' z_of' z_pf' z_sf' z_zf' l2.
        mc_div_sub_aux1_pre (l,n2w (LENGTH zs + 1),b2w c,r8,
           r9,n2w (LENGTH zs1),ys1 ++ ys ++ ys2,zs1 ++ zs ++ zs2) /\
        (mc_div_sub_aux1 (l,n2w (LENGTH zs + 1),b2w c,r8,
           r9,n2w (LENGTH zs1),ys1 ++ ys ++ ys2,zs1 ++ zs ++ zs2) =
          (l2,0w,b2w (SND (mw_sub ys zs c)),r8',r9',n2w (LENGTH (zs1++zs)),
           ys1 ++ ys ++ ys2,zs1 ++ FST (mw_sub ys zs c) ++ zs2)) /\
        l <= l2 + LENGTH ys``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def]
    \\ ONCE_REWRITE_TAC [mc_div_sub_aux_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def,LET_DEF])
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [mc_div_sub_aux_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,ADD1,n2w_w2n,w2n_n2w,
       single_sub_word_thm]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ `LENGTH ys1 < dimword (:'a) /\
      LENGTH zs1 < dimword (:'a) /\
      LENGTH ys + 1 + 1 < dimword (:'a) /\
      1 < dimword (:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [EL_LENGTH,LUPDATE_LENGTH,GSYM APPEND_ASSOC,APPEND]
  \\ Q.PAT_X_ASSUM `LENGTH zs1 = LENGTH ys1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EL_LENGTH,LUPDATE_LENGTH,n2w_11,GSYM APPEND_ASSOC,APPEND]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ `LENGTH zs1 + 1 = LENGTH (SNOC h' ys1)` by
        FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1]
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "mc_div_sub_aux1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (fs [])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_sub_def,
       LET_DEF,single_sub_def,b2n_thm,single_add_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ `(dimword(:'a) <= b2n ~c + (w2n h' + w2n (~h))) =
      ~(w2n h' < b2n c + w2n h)` by METIS_TAC [sub_borrow_lemma]
  \\ fs [])
  |> Q.SPECL [`ys`,`zs`,`[]`,`[]`,`ys2`,`zs2`,`T`]
  |> SIMP_RULE std_ss [APPEND,LENGTH,EVAL ``b2w T``] |> GEN_ALL;

val mc_div_sub1_thm = prove(
  ``(LENGTH (zs:'a word list) = LENGTH ys) /\ LENGTH zs + 1 < dimword (:'a) /\
    LENGTH ys + 1 <= l ==>
    ?r8' r9' l2.
      mc_div_sub1_pre (l,n2w (LENGTH ys),r8,r9,ys ++ ys2,zs ++ zs2) /\
      (mc_div_sub1 (l,n2w (LENGTH ys),r8,r9,ys ++ ys2,zs ++ zs2) =
        (l2,0x0w,r8',r9',n2w (LENGTH ys),ys ++ ys2,
         FST (mw_sub ys zs T) ++ zs2)) /\
      l <= l2 + LENGTH ys + 1``,
  SIMP_TAC std_ss [mc_div_sub1_def]
  \\ ONCE_REWRITE_TAC [mc_div_sub_aux_def]
  \\ SIMP_TAC std_ss [LET_DEF,WORD_SUB_RZERO,word_add_n2w]
  \\ REPEAT STRIP_TAC \\ ASSUME_TAC mc_div_sub_aux_thm
  \\ SEP_I_TAC "mc_div_sub_aux1" \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ fs [] \\ rfs []);

(* mwi_div -- integer division *)

val (mc_idiv_mod_header_def, _,
     mc_idiv_mod_header_pre_def, _) =
  tailrec_define "mc_idiv_mod_header" ``
    (\(r6,r11).
      if r6 = 0x0w then (INR r6,T)
      else
        (let r6 = r6 << 1
         in
           if r11 && 0x1w = 0x0w then (INR r6,T)
           else (let r6 = r6 + 0x1w in (INR r6,T))))
    :'a word # 'a word -> ('a word # 'a word + 'a word) # bool``;

val mc_idiv_mod_header_thm = prove(
  ``LENGTH (xs:'a word list) < dimword (:'a) ==>
    (mc_idiv_mod_header (n2w (LENGTH xs),mc_header (t,ys)) =
     mc_header (xs <> [] /\ t,xs))``,
  SIMP_TAC std_ss [mc_idiv_mod_header_def,mc_header_sign,n2w_11,
    ZERO_LT_dimword,LENGTH_NIL,LET_DEF,mc_header_def,word_lsl_n2w]
  \\ rw[] \\ fs[] \\ rw[]
  THEN_LT USE_SG_THEN (fn th => metis_tac[th]) 1 2
  \\ Cases_on`xs` \\ fs[]
  \\ `dimindex(:'a) = 1` by fs[DIMINDEX_GT_0]
  \\ fs[dimword_def]);

val (mc_idiv0_def, _,
     mc_idiv0_pre_def, _) =
  tailrec_define "mc_idiv0" ``
    (\(l,r0:'a word,r3:'a word,r6,r11,r20,xs:'a word list,ys,zs).
         if r3 = 0x0w then
           (let r10 = r0 in
            let r8 = r10 in
            let cond = mc_fix_pre (l-1,r8,r10,zs) /\ l<>0 in
            let (l,r8,r10,zs) = mc_fix (l-1,r8,r10,zs) in
            let r11 = r10 in
            let r2 = r20 in
            let r3 = r2 in
            let cond = cond /\ mc_add1_call_pre (l,r2,r6,r11,zs) in
            let (l,r11,zs) = mc_add1_call (l,r2,r6,r11,zs)
            in
              if r11 = 0x0w then (INR (l,r11,xs,ys,zs),cond)
              else
                (let r11 = r11 << 1 in
                 let r11 = r11 + r3
                 in
                   (INR (l,r11,xs,ys,zs),cond)))
         else
           (let r2 = r20 in
            let r1 = r11 in
            let r1 = r1 >>> 1 in
            let cond = mc_div_sub_call_pre (l,r1,r2,r6,ys,zs) in
            let (l,r6,ys,zs) = mc_div_sub_call (l,r1,r2,r6,ys,zs) in
            let r6 = mc_idiv_mod_header (r6,r11) in
            let r11 = r6
            in
              (INR (l,r11,xs,ys,zs),cond)))
    : num # α word # α word # α word # α word # α word # α word list #
      α word list # α word list -> (num # α word # α word # α word # α
      word # α word # α word list # α word list # α word list + num #
      α word # α word list # α word list # α word list) # bool``

val (mc_idiv_def, _,
     mc_idiv_pre_def, _) =
  tailrec_define "mc_idiv" ``
    (\(l,r3,r10,r11,xs,ys,zs).
      (let r0 = r10 >>> 1 in
       let r1 = r11 >>> 1 in
       let r10 = r10 ?? r11 in
       let r10 = r10 && 0x1w in
       let r20 = r10 in
       let r21 = r11 in
       let cond = mc_div_pre (l,r0,r1,r3,xs,ys,zs) in
       let (l,r0,r3,r6,xs,ys,zs) = mc_div (l,r0,r1,r3,xs,ys,zs) in
       let r11 = r21 in
       let cond = cond /\ mc_idiv0_pre (l,r0,r3,r6,r11,r20,xs,ys,zs) in
       let (l,r11,xs,ys,zs) = mc_idiv0 (l,r0,r3,r6,r11,r20,xs,ys,zs) in
         (INR (l,r11,xs,ys,zs),cond)))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word list
     # 'a word list # 'a word list + num # 'a word # 'a word list # 'a
     word list # 'a word list) # bool``;

val mc_idiv_def = mc_idiv_def |> REWRITE_RULE [mc_idiv0_def,mc_idiv0_pre_def]
val mc_idiv_pre_def = mc_idiv_pre_def |> REWRITE_RULE [mc_idiv0_def,mc_idiv0_pre_def]

val mc_header_XOR = prove(
  ``!s t. ((mc_header (s,xs) ?? mc_header (t,ys)) && 0x1w:'a word) =
          (b2w (s <> t)):'a word``,
  SIMP_TAC std_ss [WORD_RIGHT_AND_OVER_XOR,mc_header_AND_1]
  \\ Cases \\ Cases \\ rw[b2w_def,b2n_def]);

val b2w_EQ_0w = prove(
  ``!b. (b2w b = 0w:'a word) = ~b``,
  Cases \\ EVAL_TAC \\ rw[one_neq_zero_word]);

val mwi_divmod_alt_def = Define `
  mwi_divmod_alt w s_xs t_ys =
    if w = 0w then mwi_div s_xs t_ys else mwi_mod s_xs t_ys`;

val mc_idiv_thm = prove(
  ``LENGTH (xs:'a word list) + LENGTH ys <= LENGTH zs /\
    LENGTH zs < dimword (:'a) DIV 2 /\
    mw_ok xs /\ mw_ok ys /\ ys <> [] /\
    mc_div_max xs ys zs + 2 * LENGTH zs + 2 <= l ==>
    ?zs1 l2.
      mc_idiv_pre (l,r3,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
      (mc_idiv (l,r3,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
        (l2,mc_header ((mwi_divmod_alt r3 (s,xs) (t,ys))),xs,ys,
         SND ((mwi_divmod_alt r3 (s,xs) (t,ys)))++zs1)) /\
      (LENGTH (SND ((mwi_divmod_alt r3 (s,xs) (t,ys)))++zs1) = LENGTH zs) /\
      l <= l2 + mc_div_max xs ys zs + 2 * LENGTH zs + 2``,
  FULL_SIMP_TAC std_ss [mc_idiv_def,mc_idiv_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mc_header_EQ,mwi_mul_def,mc_length]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mc_header_XOR]
  \\ `LENGTH xs < dimword (:'a) DIV 2 /\ LENGTH ys < dimword (:'a) DIV 2` by DECIDE_TAC
  \\ `LENGTH zs < dimword (:'a)` by (FULL_SIMP_TAC (srw_ss()) [X_LT_DIV] \\ DECIDE_TAC)
  \\ IMP_RES_TAC mc_length \\ FULL_SIMP_TAC std_ss []
  \\ `mw2n ys <> 0` by
   (SIMP_TAC std_ss [GSYM mw_fix_NIL]
    \\ FULL_SIMP_TAC std_ss [mw_ok_mw_fix_ID])
  \\ `?res mod c. (mw_div xs ys = (res,mod,c))` by METIS_TAC [PAIR]
  \\ `c /\ (LENGTH mod = LENGTH ys)` by METIS_TAC [mw_div_thm,mw_ok_mw_fix_ID]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (mc_div_thm |> GEN_ALL)
  \\ SEP_I_TAC "mc_div"
  \\ POP_ASSUM MP_TAC
  \\ `mc_div_max xs ys zs ≤ l` by fs []
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 4 (POP_ASSUM MP_TAC) \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ Cases_on `r3 <> 0w` \\ FULL_SIMP_TAC std_ss [mwi_divmod_alt_def] THEN1
   (FULL_SIMP_TAC std_ss [mc_div_sub_call_def,mc_div_sub_call_pre_def]
    \\ FULL_SIMP_TAC std_ss [TL,mwi_mod_def,mwi_divmod_def,LET_DEF,HD,NOT_CONS_NIL,
         mc_header_XOR]
    \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss [EVAL ``b2w F``] THEN1
     (FULL_SIMP_TAC std_ss [mc_idiv_mod_header_thm]
      \\ ASSUME_TAC (Q.ISPEC `mod:'a word list` (GSYM mw_fix_thm))
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
      \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11]
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
      \\ `LENGTH (mw_fix mod) <= LENGTH mod` by METIS_TAC [LENGTH_mw_fix]
      \\ DECIDE_TAC)
    \\ Cases_on `mw_fix mod = []`
    \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,LENGTH_APPEND]
    THEN1 (SIMP_TAC std_ss [mc_idiv_mod_header_def] \\ fs [] \\ EVAL_TAC \\ simp[])
    \\ FULL_SIMP_TAC std_ss [EVAL ``b2w T = 0x0w:'a word``,n2w_11,ZERO_LT_dimword]
    \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
    \\ Cases_on`1 MOD dimword(:'a) = 0` \\ fs[]
    \\ (mc_div_sub1_thm |> Q.INST [`ys2`|->`[]`]
        |> SIMP_RULE std_ss [APPEND_NIL] |> GEN_ALL |> ASSUME_TAC)
    \\ SEP_I_TAC "mc_div_sub1" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,X_LT_DIV] \\ fs [])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH ys = LENGTH (FST (mw_sub ys mod T))` by
     (Cases_on `mw_sub ys mod T` \\ IMP_RES_TAC LENGTH_mw_sub
      \\ FULL_SIMP_TAC std_ss [])
    \\ ASM_SIMP_TAC std_ss []
    \\ ASSUME_TAC mc_fix_thm
    \\ SEP_I_TAC "mc_fix"
    \\ pop_assum mp_tac
    \\ match_mp_tac IMP_IMP \\ strip_tac THEN1 fs []
    \\ strip_tac \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM mw_subv_def]
    \\ `mw_subv ys (mw_fix mod) = mw_subv ys mod` by (SIMP_TAC std_ss [mw_subv_def,mw_sub_mw_fix])
    \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH (mw_subv ys mod) <= LENGTH ys` by (MATCH_MP_TAC LENGTH_mw_subv \\ FULL_SIMP_TAC std_ss [])
    \\ `LENGTH (mw_subv ys mod) < dimword (:'a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [mc_idiv_mod_header_thm]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11]
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
    \\ SIMP_TAC std_ss [mw_subv_def]
    \\ `LENGTH (mw_fix (FST (mw_sub ys mod T))) <= LENGTH (FST (mw_sub ys mod T))`
          by FULL_SIMP_TAC std_ss [LENGTH_mw_fix] \\ fs [])
  \\ `LENGTH res < dimword (:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [mwi_div_def]
  \\ MP_TAC (mc_fix_thm |> Q.SPECL
       [`res`,`zs2`,`n2w (LENGTH (res:'a word list))`,`l2-1`])
  \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs []
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ pop_assum mp_tac
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC)) \\ strip_tac
  \\ FULL_SIMP_TAC std_ss [mc_add1_call_def,mc_add1_call_pre_def,
                           LET_DEF,mwi_divmod_def,b2w_EQ_0w]
  \\ `LENGTH (mw_fix res) <= LENGTH res` by
        FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
  \\ `LENGTH (mw_fix res) < dimword (:'a)` by DECIDE_TAC
  \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword] THEN1
   (SIMP_TAC (srw_ss()) [word_lsl_n2w,b2w_def,b2n_def,mc_header_def]
    \\ Cases_on`dimindex(:'a) < 2` \\ fs[X_LT_DIV,LEFT_ADD_DISTRIB]
    >- (
      `dimindex(:'a) = 1` by fs[DIMINDEX_GT_0]
      \\ full_simp_tac (std_ss++ARITH_ss)[dimword_def,GSYM LENGTH_NIL] )
    \\ Cases_on `LENGTH (mw_fix res) = 0` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,
         LENGTH_APPEND,LENGTH_REPLICATE] \\ fs [])
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
  \\ Cases_on `mw_fix mod = []`
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL] THEN1
   (Cases_on `mw_fix res = []` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,
         LENGTH_APPEND,LENGTH_REPLICATE]
    \\ SIMP_TAC (srw_ss()) [word_lsl_n2w,b2w_def,b2n_def,mc_header_def]
    \\ rw[]
    \\ `dimindex(:'a) = 1` by fs[DIMINDEX_GT_0]
    \\ full_simp_tac (std_ss++ARITH_ss) [dimword_def,GSYM LENGTH_NIL])
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ Q.ABBREV_TAC `ts1 = REPLICATE (LENGTH res - LENGTH (mw_fix res)) 0x0w ++ zs2`
  \\ ASSUME_TAC (mc_add1_thm |> GEN_ALL)
  \\ SEP_I_TAC "mc_add1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
    (Q.UNABBREV_TAC `ts1`
     \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,GSYM LENGTH_NIL,
          LENGTH_REPLICATE,mc_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
     \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL]
  \\ Cases_on `mw_addv (mw_fix res) [] T = []`
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,
       mc_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
  THEN1 (Q.UNABBREV_TAC `ts1`
    \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,LENGTH_REPLICATE,
         mc_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,LENGTH_REPLICATE,
         mc_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND,APPEND_11]
  \\ FULL_SIMP_TAC std_ss [b2w_def,b2n_def]
  \\ SIMP_TAC (srw_ss()) [word_lsl_n2w,word_add_n2w]
  \\ Q.UNABBREV_TAC `ts1`
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,LENGTH_REPLICATE,
         mc_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
  \\ rw[]
  >- (
    `dimindex(:'a) = 1` by fs[DIMINDEX_GT_0]
    \\ fs[dimword_def] )
  \\ fs[word_add_n2w]);

(*

(* int to decimal conversion *)

val (mc_to_dec_def, _,
     mc_to_dec_pre_def, _) =
  tailrec_define "mc_to_dec" ``
    (\(r9,r10,zs,ss).
      (let r2 = 0x0w in
       let r11 = r10 in
       let cond = mc_simple_div1_pre (r2,r9,r10,zs) in
       let (r2,r9,r10,zs) = mc_simple_div1 (r2,r9,r10,zs) in
       let r2 = r2 + 0x30w in
       let ss = r2::ss in
       let r8 = r10 in
       let r10 = r11 in
       let cond = cond /\ mc_fix_pre (r8,r10,zs) in
       let (r8,r10,zs) = mc_fix (r8,r10,zs)
       in
         if r10 = 0x0w then (INR (zs,ss),cond)
         else (INL (r9,r10,zs,ss),cond)))
    :'a word # 'a word # 'a word list # 'a word list -> ('a word # 'a
     word # 'a word list # 'a word list + 'a word list # 'a word list)
     # bool``;

val (mc_int_to_dec_def, _,
     mc_int_to_dec_pre_def, _) =
  tailrec_define "mc_int_to_dec" ``
    (\(r10,xs,zs,ss).
      (let r1 = r10 in
       let r10 = r10 >>> 1 in
       let cond = mc_copy_over_pre (r10,xs,zs) in
       let (xs,zs) = mc_copy_over (r10,xs,zs) in
       let r10 = r1 in
       let r10 = r10 >>> 1 in
       let r9 = 0xAw in
       let cond = cond /\ mc_to_dec_pre (r9,r10,zs,ss) in
       let (zs,ss) = mc_to_dec (r9,r10,zs,ss)
       in
         if r1 && 0x1w = 0x0w then (INR (xs,zs,ss),cond)
         else (let r2 = 0x7Ew in let ss = r2::ss in (INR (xs,zs,ss),cond))))
    :'a word # 'a word list # 'a word list # 'a word list -> ('a word
     # 'a word list # 'a word list # 'a word list + 'a word list # 'a
     word list # 'a word list) # bool``;

val mc_to_dec_thm = prove(
  ``!(xs:'a word list) ys zs ss.
      LENGTH xs < dimword (:'a) /\ (mw_to_dec xs = (ys,T)) ==>
      ?zs1.
        mc_to_dec_pre (10w,n2w (LENGTH xs),xs++zs,ss) /\
        (mc_to_dec (10w,n2w (LENGTH xs),xs++zs,ss) = (zs1,ys ++ ss)) /\
        (LENGTH zs1 = LENGTH xs + LENGTH zs)``,
  HO_MATCH_MP_TAC mw_to_dec_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once mw_to_dec_def]
  \\ IF_CASES_TAC >- fs[]
  \\ `?qs r c1. mw_simple_div 0x0w (REVERSE xs) 0xAw = (qs,r,c1)` by METIS_TAC [PAIR]
  \\ `?res c2. mw_to_dec (mw_fix (REVERSE qs)) = (res,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [mc_to_dec_def,mc_to_dec_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC
  \\ sg `c1` \\ FULL_SIMP_TAC std_ss []
  THEN1 (Cases_on `LENGTH (mw_fix (REVERSE qs)) = 0` \\ FULL_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ IMP_RES_TAC mc_simple_div1_thm
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_mw_simple_div
  \\ MP_TAC (mc_fix_thm |> Q.SPECL [`REVERSE qs`,`zs`,`0w`])
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ STRIP_TAC
  \\ `LENGTH (mw_fix (REVERSE qs)) <= LENGTH (REVERSE qs)` by
        METIS_TAC [LENGTH_mw_fix]
  \\ `LENGTH (mw_fix (REVERSE qs)) < dimword (:'a)` by (FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
  \\ Cases_on `mw_fix (REVERSE qs) = []` \\ FULL_SIMP_TAC std_ss [LENGTH]
  THEN1 (SIMP_TAC std_ss [LENGTH_REPLICATE,LENGTH_APPEND] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ SEP_I_TAC "mc_to_dec"
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LENGTH_REPLICATE,LENGTH_APPEND,REVERSE_APPEND,REVERSE_DEF]
  \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC);

val mc_int_to_dec_thm = prove(
  ``(mwi_to_dec (s,xs) = (res,T)) /\ LENGTH zs < dimword (:'a) DIV 2 /\
    LENGTH (xs:'a word list) <= LENGTH zs ==>
    ?zs1.
      (mc_int_to_dec_pre (mc_header(s,xs),xs,zs,ss)) /\
      (mc_int_to_dec (mc_header(s,xs),xs,zs,ss) = (xs,zs1,res ++ ss)) /\
      (LENGTH zs1 = LENGTH zs)``,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [mc_int_to_dec_def,mc_int_to_dec_pre_def,LET_DEF] \\ STRIP_TAC
  \\ `LENGTH xs < dimword (:'a) DIV 2` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [mc_length]
  \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (mc_copy_over_thm |> Q.SPECL [`xs0`,`zs0`,`[]`] |> GEN_ALL)
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
  \\ `LENGTH xs + LENGTH xs2 < dimword (:'a)` by
        (FULL_SIMP_TAC (srw_ss()) [X_LT_DIV] \\ DECIDE_TAC)
  \\ SEP_I_TAC "mc_copy_over"
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [mwi_to_dec_def,LET_DEF]
  \\ Cases_on `mw_to_dec xs` \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ `LENGTH xs < dimword (:'a)` by DECIDE_TAC
  \\ IMP_RES_TAC mc_to_dec_thm
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`xs2`,`ss`])
  \\ FULL_SIMP_TAC std_ss [mc_header_sign]
  \\ Cases_on `s` \\ FULL_SIMP_TAC std_ss [APPEND]);

*)

(* top-level entry point *)

val int_op_rep_def = Define `
  (int_op_rep Add = 0w) /\
  (int_op_rep Sub = 1w) /\
  (int_op_rep Lt  = 2w) /\
  (int_op_rep Eq  = 3w) /\
  (int_op_rep Mul = 4w) /\
  (int_op_rep Div = 5w) /\
  (int_op_rep Mod = 6w) /\
  (int_op_rep Dec = 7w:'a word)`;

val (mc_isub_flip_def, _,
     mc_isub_flip_pre_def, _) =
  tailrec_define "mc_isub_flip" ``
    (\(r1,r3).
      if r3 = 0x0w then (INR (r1,r3),T)
      else (let r1 = r1 ?? 0x1w in (INR (r1,r3),T)))
    :'a word # 'a word -> ('a word # 'a word + 'a word # 'a word) # bool``;

val (mc_icmp_res_def, _,
     mc_icmp_res_pre_def, _) =
  tailrec_define "mc_icmp_res" ``
    (\(r10,r3).
      if r3 = 0x2w then
        if r10 = 0x1w then (let r10 = 0x1w in (INR r10,T))
        else (let r10 = 0x0w in (INR r10,T))
      else if r10 = 0x0w then (let r10 = 0x1w in (INR r10,T))
      else (let r10 = 0x0w in (INR r10,T)))
    :'a word # 'a word -> ('a word # 'a word + 'a word) # bool``;

val (mc_full_cmp_def, _,
     mc_full_cmp_pre_def, _) =
  tailrec_define "mc_full_cmp" ``
    (\(l,r3,r10,r11,xs,ys,zs).
      (let cond = mc_icompare_pre (l,r10,r11,xs,ys) in
       let (l,r10,xs,ys) = mc_icompare (l,r10,r11,xs,ys) in
       let r10 = mc_icmp_res (r10,r3)
       in
         if r10 = 0x0w then (INR (l,r10,xs,ys,zs),cond)
         else
           (let r0 = 0x1w in
            let r10 = (0x0w:'a word) in
            let cond = cond /\ w2n r10 < LENGTH zs in
            let zs = LUPDATE r0 (w2n r10) zs in
            let r10 = 0x2w
            in
              (INR (l,r10,xs,ys,zs),cond))))
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word list
     # 'a word list # 'a word list + num # 'a word # 'a word list # 'a
     word list # 'a word list) # bool``;

val NumABS_LEMMA = prove(
  ``(Num (ABS (0:int)) = 0:num) /\ (Num (ABS (1:int)) = 1:num)``,
  intLib.COOPER_TAC);

val mc_full_cmp_lt = prove(
  ``((mc_header (s,xs) = 0x0w) <=> (xs = [])) /\ mw_ok xs /\
    ((mc_header (t,ys) = 0x0w) <=> (ys = [])) /\ mw_ok ys /\
    LENGTH (xs:'a word list) < dimword (:'a) DIV 2 /\
    LENGTH ys < dimword (:'a) DIV 2 /\
    LENGTH xs + LENGTH ys < LENGTH zs /\ LENGTH zs < dimword (:'a) DIV 2 /\
    LENGTH xs + 1 <= l ==>
    ?zs1 l2.
      mc_full_cmp_pre (l,2w,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
      (mc_full_cmp (l,2w,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
       (l2,mc_header (mwi_op Lt (s,xs) (t,ys)),xs,ys,
        SND (mwi_op Lt (s,xs) (t,ys)) ++ zs1)) /\
      (LENGTH (SND (mwi_op Lt (s,xs) (t,ys)) ++ zs1) = LENGTH zs) /\
      l <= l2 + LENGTH xs + 1``,
  SIMP_TAC std_ss [mc_full_cmp_def,mc_full_cmp_pre_def,LET_DEF] \\ STRIP_TAC
  \\ MP_TAC mc_icompare_thm \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def] \\ SIMP_TAC std_ss [mwi_lt_def]
  \\ Cases_on `mwi_compare (s,xs) (t,ys)`
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,mc_icmp_res_def,n2w_11,LET_DEF]
  THEN1 (Q.EXISTS_TAC `zs` \\ SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``] \\ EVAL_TAC
    \\ fs[])
  \\ REV (Cases_on `x`)
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,mc_icmp_res_def,n2w_11,LET_DEF]
  THEN1 (Q.EXISTS_TAC `zs` \\ SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``] \\ EVAL_TAC
    \\ IF_CASES_TAC \\ fs[]
    \\ Cases_on`dimword(:'a)` \\ fs[]
    \\ Cases_on`n` \\ fs[ADD1]
    \\ Cases_on`n'` \\ fs[])
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.EXISTS_TAC `t'` \\ FULL_SIMP_TAC std_ss [LUPDATE_def]
  \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``,n2mw_1]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [ADD1] \\ fs[]);

Theorem mc_full_cmp_eq[local]:
  ((mc_header (s,xs) = 0x0w) <=> (xs = [])) /\ mw_ok xs /\
    ((mc_header (t,ys) = 0x0w) <=> (ys = [])) /\ mw_ok ys /\
    LENGTH (xs:'a word list) < dimword (:'a) DIV 2 /\
    LENGTH ys < dimword (:'a) DIV 2 /\
    LENGTH xs + LENGTH ys < LENGTH zs /\ LENGTH zs < dimword (:'a) DIV 2 /\
    LENGTH xs + 1 <= l ==>
    ?zs1 l2.
      mc_full_cmp_pre (l,3w,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
      (mc_full_cmp (l,3w,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
       (l2,mc_header (mwi_op Eq (s,xs) (t,ys)),xs,ys,
        SND (mwi_op Eq (s,xs) (t,ys)) ++ zs1)) /\
      (LENGTH (SND (mwi_op Eq (s,xs) (t,ys)) ++ zs1) = LENGTH zs) /\
      l <= l2 + LENGTH xs + 1
Proof
  SIMP_TAC std_ss [mc_full_cmp_def,mc_full_cmp_pre_def,LET_DEF] \\ STRIP_TAC
  \\ MP_TAC mc_icompare_thm \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
  \\ SIMP_TAC std_ss [mwi_eq_def]
  \\ REV (Cases_on `mwi_compare (s,xs) (t,ys)`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [cmp2w_def,mc_icmp_res_def,n2w_11,LET_DEF]
    \\ Q.EXISTS_TAC `zs` \\ SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``] \\ fs[]
    \\ Cases_on`3 < dimword(:'a)` \\ fs[]
    >- (
      EVAL_TAC \\ rw[]
      \\ pop_assum mp_tac \\ rw[]
      \\ Cases_on`x` \\ gs[cmp2w_def])
    \\ `dimword(:'a) = 2`
      by gs[dimword_def,X_LT_DIV,DECIDE “~(1n < x) ⇔ (x = 1) ∨ (x = 0)”]
    \\ fs[])
  \\ SIMP_TAC std_ss [cmp2w_def]
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,mc_icmp_res_def,n2w_11,LET_DEF]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.EXISTS_TAC `t'` \\ FULL_SIMP_TAC std_ss [LUPDATE_def]
  \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``]
  \\ Cases_on`3 < dimword(:'a)` \\ fs[n2mw_1]
  >- ( EVAL_TAC \\ rw[] )
  \\ ‘dimword(:'a) = 2’
    suffices_by (strip_tac >> gs[])
  \\ gs[dimword_def, DECIDE “~(1n < x) ⇔ (x = 1) ∨ (x = 0)”]
QED

val (mc_iop_def, _,
     mc_iop_pre_def, _) =
  tailrec_define "mc_iop" ``
    (\(l,r0,r1,r3,xs,ys,zs).
      if r3 <+ 0x2w then
        (let (r1,r3) = mc_isub_flip (r1,r3) in
         let r2 = r1 in
         let r1 = r0 in
         let cond = mc_iadd_pre (l,r1,r2,xs,ys,zs) in
         let (l,r10,xs,ys,zs) = mc_iadd (l,r1,r2,xs,ys,zs)
         in
           (INR (l,r10,xs,ys,zs),cond))
  (*  else if r3 <+ 0x4w then
        (let r10 = r0 in
         let r11 = r1 in
         let cond = mc_full_cmp_pre (r3,r10,r11,xs,ys,zs) in
         let (r10,xs,ys,zs) = mc_full_cmp (r3,r10,r11,xs,ys,zs)
         in
           (INR (r10,xs,ys,zs,ss),cond))  *)
      else if r3 = 0x4w then
        (let r2 = r1 in
         let r1 = r0 in
         let cond = mc_imul_pre (l,r1,r2,xs,ys,zs) in
         let (l,r10,xs,ys,zs) = mc_imul (l,r1,r2,xs,ys,zs)
         in
           (INR (l,r10,xs,ys,zs),cond))
      else (* if r3 <+ 0x7w then *)
        (let r3 = r3 - 0x5w in
         let r10 = r0 in
         let r11 = r1 in
         let cond = mc_idiv_pre (l,r3,r10,r11,xs,ys,zs) in
         let (l,r11,xs,ys,zs) = mc_idiv (l,r3,r10,r11,xs,ys,zs) in
         let r10 = r11
         in
           (INR (l,r10,xs,ys,zs),cond)))
  (*  else
        (let r10 = r0 in
         let cond = mc_int_to_dec_pre (r10,xs,zs,ss) in
         let (xs,zs,ss) = mc_int_to_dec (r10,xs,zs,ss) in
         let r10 = 0x0w
         in
           (INR (r10,xs,ys,zs,ss),cond)) *)
    :num # 'a word # 'a word # 'a word # 'a word list # 'a word list #
     'a word list -> (num # 'a word # 'a word # 'a word # 'a word list
     # 'a word list # 'a word list + num # 'a word # 'a word list # 'a
     word list # 'a word list) # bool``;

val mc_header_XOR_1 = prove(
  ``mc_header (s,xs) ?? 1w = mc_header (~s,xs)``,
  simp[mc_header_def,GSYM word_mul_n2w]
  \\ Q.SPEC_TAC(`n2w(LENGTH xs):'a word`,`w`)
  \\ gen_tac
  \\ qspecl_then[`w`,`1`]mp_tac (GSYM WORD_MUL_LSL)
  \\ simp[] \\ disch_then kall_tac
  \\ rw[]
  \\ FIRST (map match_mp_tac [xor_one_add_one,add_one_xor_one])
  \\ rw[word_lsl_def,fcpTheory.FCP_BETA] );

val mc_iop_thm = store_thm("mc_iop_thm",
  ``3 < dimindex(:'a) ==>
    ((mc_header (s,xs) = 0x0w) <=> (xs = [])) /\ mw_ok xs /\
    ((mc_header (t,ys) = 0x0w) <=> (ys = [])) /\ mw_ok ys /\
    LENGTH (xs:'a word list) + LENGTH ys < LENGTH zs /\
    LENGTH zs < dimword (:'a) DIV 2 /\
    iop <> Lt /\ iop <> Eq /\ iop <> Dec /\
    (((iop = Div) \/ (iop = Mod)) ==> ys <> []) /\
    mc_div_max xs ys zs + 2 * LENGTH zs + 2 <= l ==>
    ?zs1 l2.
      mc_iop_pre (l,mc_header (s,xs),mc_header (t,ys),int_op_rep iop,
                   xs,ys,zs) /\
      (mc_iop (l,mc_header (s,xs),mc_header (t,ys),int_op_rep iop,
                xs,ys,zs) =
       (l2,mc_header (mwi_op iop (s,xs) (t,ys)),xs,ys,
        SND (mwi_op iop (s,xs) (t,ys)) ++ zs1)) /\
      (LENGTH (SND (mwi_op iop (s,xs) (t,ys)) ++ zs1) = LENGTH zs) /\
      l <= l2 + mc_div_max xs ys zs + 2 * LENGTH zs + 2``,
  strip_tac \\
 `10 < dimword(:'a)`
  by (
    `2 ** 4 <= dimword(:'a)` suffices_by fs[]
    \\ rewrite_tac[dimword_def] \\ simp[] ) \\
  Cases_on `iop` \\ SIMP_TAC std_ss [int_op_rep_def] \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword (:'a) DIV 2 /\ LENGTH ys < dimword (:'a) DIV 2` by DECIDE_TAC
  \\ `LENGTH xs + LENGTH ys <= LENGTH zs` by DECIDE_TAC
  \\ SIMP_TAC std_ss [mc_iop_def,mc_iop_pre_def,WORD_LO]
  \\ SIMP_TAC (srw_ss()) [w2n_n2w,LET_DEF,mc_isub_flip_def]
  THEN1 (
    reverse IF_CASES_TAC \\ rfs[]
    \\ MP_TAC mc_iadd_thm \\ fs[]
    \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs [mc_div_max_def]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ fs[] \\ fs [mc_div_max_def])
  THEN1 (
    reverse IF_CASES_TAC \\ rfs[]
    \\ MP_TAC (mc_iadd_thm |> Q.INST [`t`|->`~t`])
    \\ fs[mc_header_XOR_1]
    \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs [mc_div_max_def]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def,mwi_sub_def]
    \\ fs[] \\ fs [mc_div_max_def])
  THEN1 (
    IF_CASES_TAC \\ rfs[]
    \\ MP_TAC mc_imul_thm \\ fs[]
    \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 fs [mc_div_max_def]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ fs[] \\ fs [mc_div_max_def])
  THEN1 (
    IF_CASES_TAC \\ rfs[]
    \\ MP_TAC (mc_idiv_thm |> Q.INST [`r3`|->`0w`]) \\ fs[]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [mwi_divmod_alt_def])
  THEN1 (
    IF_CASES_TAC \\ rfs[]
    \\ MP_TAC (mc_idiv_thm |> Q.INST [`r3`|->`1w`]) \\ fs[]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ fs[mwi_divmod_alt_def] ));

(* An example which uses recursion that is not tail-recursion:
   tail-recursive components are defined as usual; however,
   non-tail-recursive functions must be defined using tDefine and the
   precondition is to be defined separately but closely following the
   structure of the original function *)

val (mc_fac_init_def, _,
     mc_fac_init_pre_def, _) =
  tailrec_define "mc_fac_init" ``
    (\(l:num,r1).
      if r1 <+ 2w then
        (let r0 = 0w:'a word in
         let r2 = 0w:'a word in
         let r3 = 0w in
         let cond = T in
           (INR (l,r0,r1,r2,r3),cond))
      else
        (let r0 = 1w:'a word in
         let r2 = r1 - 1w in
         let r3 = r1 - 2w in
         let cond = T in
           (INR (l,r0,r1,r2,r3),cond)))
     :num # α word -> (num # α word + num # α word # α word # α word #
      α word) # bool``

val (mc_fac_final_def, _,
     mc_fac_final_pre_def, _) =
  tailrec_define "mc_fac_final" ``
    (\(l:num,r1,r2).
       let r1 = r1 + r2 in
       let cond = T in
         (INR (l,r1),cond))
     :num # α word # α word -> (num # α word # α word + num # α word) # bool``

val mc_fac_def = tDefine "mc_fac" `
  mc_fac (l:num,r1:'a word) =
    let l0 = l in
    let (l,r0,r1,r2,r3) = mc_fac_init (l:num,r1:'a word) in
    let l = MIN l l0 in
      if r0 = 0w then (l,r1) else
        let r1 = r2 in
        if l = 0 then (l,r1) else
        let ((r2,r3),(l,r1)) = ((r2,r3),mc_fac (l-1,r1)) in
        let l = MIN l l0 in
        let r2 = r1 in
        let r1 = r3 in
        if l = 0 then (l,r1) else
        let (r2,(l,r1)) = (r2,mc_fac (l-1,r1)) in
        let (l,r1) = mc_fac_final (l,r1,r2) in
          (l,r1)`
  (WF_REL_TAC `measure FST` \\ rw []);

val mc_fac_pre_def = tDefine "mc_fac_pre" `
  mc_fac_pre (l:num,r1:'a word) =
    let l0 = l in
    let cond = mc_fac_init_pre (l:num,r1:'a word) in
    let (l,r0,r1,r2,r3) = mc_fac_init (l:num,r1:'a word) in
    let l = MIN l l0 in
      if r0 = 0w then F else
        let r1 = r2 in
        if l = 0 then F else
        let cond = (mc_fac_pre (l-1,r1) /\ cond) in
        let ((r2,r3),(l,r1)) = ((r2,r3),mc_fac (l-1,r1)) in
        let l = MIN l l0 in
        let r2 = r1 in
        let r1 = r3 in
        if l = 0 then F else
        let cond = (mc_fac_pre (l-1,r1) /\ cond) in
        let cond = (mc_fac_final_pre (l,r1,r2) /\ cond) in
        let (l,r1) = mc_fac_final (l,r1,r2) in
          cond`
  (WF_REL_TAC `measure FST` \\ rw []);

val (mc_use_fac_def, _,
     mc_use_fac_pre_def, _) =
  tailrec_define "mc_use_fac" ``
    (\(l:num,r1).
       let cond = mc_fac_pre (l-1,r1) /\ l <> 0 in
       let (l,r1) = mc_fac (l-1,r1) in
       let r0 = r1 in
         (INR (l,r0),cond))
     :num # α word -> (num # α word + num # α word) # bool``

val _ = export_theory();
