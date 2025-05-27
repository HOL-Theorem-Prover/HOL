open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_parse";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory stringTheory helperLib;

open compilerLib;
open lisp_gcTheory lisp_typeTheory lisp_invTheory;


val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj", "NOT_LT_ZERO_EQ_ZERO"]


(* setting up the compiler *)
val _ = codegen_x86Lib.set_x86_regs
  [(3,"eax"),(4,"ecx"),(5,"edx"),(6,"ebx"),(7,"edi"),(8,"esi"),(9,"ebp")]

(* --- READ NUMBER --- *)

val (th1,arm_read_loop_def,arm_read_loop_pre_def) = compile_all ``
  arm_read_loop (r3:word32,r4:word32,r5:word32,df:word32 set,f:word32->word8) =
    (let r6 = r3 << 2 in
     let r3 = r3 + r6 in
     let r3 = r3 + r3 in
     let r3 = r3 + r4 in
     let r6 = w2w (f (r5 + 0x1w)) in
     let r5 = r5 + 0x1w in
     let r4 = r6 - 0x30w in
       if ~(r6 <+ 0x30w) then
         if ~(r4 <+ 0xAw) then
           (let r4 = r4 + 0x30w in (r3,r4,r5,r6,df,f))
         else
           arm_read_loop (r3,r4,r5,df,f)
       else
         (let r4 = r4 + 0x30w in (r3,r4,r5,r6,df,f)))``

val (th1,arm_readnum_def,arm_readnum_pre_def) = compile_all ``
  arm_readnum (r4:word32,r5:word32,df:word32 set,f:word32->word8) =
    let r3 = 0x0w:word32 in
    let r4 = r4 - 0x30w in
    let (r3,r4,r5,r6,df,f) = arm_read_loop (r3,r4,r5,df,f) in
      (r3,r4,r5,r6,df,f)``;

val number_char_def = Define `
  number_char c = 48 <= ORD c /\ ORD c < 58`;

val is_number_string_def = Define `
  is_number_string s = EVERY number_char (EXPLODE s)`;

val dec2str_def = Define `dec2str n = STRING (CHR (n + 48)) ""`;

val num2str_def = tDefine "num2str" `
  num2str n =
    if n DIV 10 = 0 then dec2str (n MOD 10) else
      STRCAT (num2str (n DIV 10)) (dec2str (n MOD 10))`
  (Q.EXISTS_TAC `measure I`
   \\ SIMP_TAC std_ss [prim_recTheory.WF_measure]
   \\ SIMP_TAC std_ss [prim_recTheory.measure_thm]
   \\ STRIP_TAC
   \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DA (DECIDE ``0 < 10:num``)))
   \\ ASM_SIMP_TAC std_ss [DIV_MULT]
   \\ DECIDE_TAC);

val str2dec_def = Define `
  str2dec c = ORD c - 48`;

val str2num_def = Define `
  (str2num "" = 0) /\
  (str2num (STRING c s) = (ORD c - 48) * 10 ** (LENGTH s) + str2num s)`;

val str2num_dec2str = prove(
  ``!n. n < 10 ==> (str2num (dec2str n) = n) /\ ~(dec2str n = "") /\
                   EVERY (\c. 48 <= ORD c /\ ORD c < 58) (EXPLODE (dec2str n))``,
  SRW_TAC [] [dec2str_def,str2num_def,LENGTH,ORD_CHR]
  \\ `n + 48 < 256` by DECIDE_TAC
  \\ IMP_RES_TAC ORD_CHR
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val EXPLODE_STRCAT = store_thm("EXPLODE_STRCAT",
  ``!s t. EXPLODE (STRCAT s t) = EXPLODE s ++ EXPLODE t``,
  Induct THEN ASM_SIMP_TAC std_ss [STRCAT_def,EXPLODE_def,APPEND])

val LENGTH_STRCAT = store_thm("LENGTH_STRCAT",
  ``!x y. LENGTH (STRCAT x y) = LENGTH x + LENGTH y``,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH,STRCAT_def,ADD_ASSOC,
     DECIDE ``SUC n = 1 + n``]);

val str2num_STRCAT = prove(
  ``!s c. str2num (STRCAT s (STRING c "")) = str2num s * 10 + str2num (STRING c "")``,
  Induct \\ ASM_SIMP_TAC std_ss [str2num_def,STRCAT_def,LENGTH_STRCAT,
    LENGTH,EXP_ADD,RIGHT_ADD_DISTRIB,AC MULT_ASSOC MULT_COMM, AC ADD_ASSOC ADD_COMM]);

val dec2str_lemma = prove(
  ``?c. dec2str r = STRING c ""``,
  SRW_TAC [] [dec2str_def,str2num_def,LENGTH]);

val str2num_num2str = prove(
  ``!n. (str2num (num2str n) = n) /\ ~((num2str n) = "") /\
        EVERY (\c. 48 <= ORD c /\ ORD c < 58) (EXPLODE (num2str n))``,
  completeInduct_on `n` \\ Cases_on `n < 10` THENL [
    IMP_RES_TAC LESS_DIV_EQ_ZERO \\ ONCE_REWRITE_TAC [num2str_def]
    \\ ASM_SIMP_TAC std_ss [str2num_dec2str],
    STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DA (DECIDE ``0 < 10:num``)))
    \\ ONCE_REWRITE_TAC [num2str_def]
    \\ ASM_SIMP_TAC std_ss [DIV_MULT]
    \\ Cases_on `q = 0` THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [MOD_TIMES,STRCAT_EQ_EMPTY,EXPLODE_STRCAT,EVERY_APPEND]
    \\ ASM_SIMP_TAC std_ss [str2num_dec2str,str2num_STRCAT]
    \\ `q < n` by DECIDE_TAC \\ RES_TAC
    \\ STRIP_ASSUME_TAC dec2str_lemma
    \\ ASM_SIMP_TAC std_ss [str2num_STRCAT]
    \\ METIS_TAC [str2num_dec2str]]);

val arm_read_loop_lemma = (RW [markerTheory.Abbrev_def] o prove)(
  ``!s a k.
      EVERY number_char (EXPLODE s) /\ ~(s = "") /\
      string_mem (STRCAT s (STRING c1 s1)) (a,f,df) /\
      Abbrev ~(number_char c1) ==>
      arm_read_loop_pre (n2w k,w2w (f a) - 48w,a,df,f) /\
      ?x. arm_read_loop (n2w k,w2w (f a) - 48w,a,df,f) =
          (n2w (k * 10 ** LENGTH s + str2num s),
           w2w (f (a + n2w (LENGTH s))),a + n2w (LENGTH s),x,df,f)``,
  Induct \\ FULL_SIMP_TAC bool_ss [NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF,STRCAT_def,string_mem_def]
  \\ NTAC 4 STRIP_TAC
  \\ `ORD h < 256 /\ ORD c1 < 256` by REWRITE_TAC [ORD_BOUND]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,w2w_def,ORD_BOUND]
  \\ ONCE_REWRITE_TAC [arm_read_loop_pre_def,arm_read_loop_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,WORD_SUB_ADD,number_char_def]
  \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_add_n2w,word_mul_n2w,
        DECIDE ``(k + 4 * k + (k + 4 * k) = 10 * k:num)``]
  \\ `~(ORD h < 48)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w]
  \\ Cases_on `s`
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [STRCAT_def,string_mem_def,w2w_def,w2n_n2w]
  THEN1
   (`ORD c1 < 4294967296 /\ ORD c1 - 48 < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w]
    \\ REWRITE_TAC [METIS_PROVE [] ``b \/ c = ~b ==> c:bool``]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [markerTheory.Abbrev_def,LENGTH,
         str2num_def,w2n_n2w, AC MULT_ASSOC MULT_COMM,word_arith_lemma2,GSYM NOT_LESS])
  \\ `ORD h' < 256` by REWRITE_TAC [ORD_BOUND]
  \\ `ORD h' < 4294967296 /\ ORD h' - 48 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w,GSYM NOT_LESS,EXPLODE_def,EVERY_DEF,number_char_def]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_arith_lemma2,w2n_n2w,NOT_CONS_NIL,GSYM AND_IMP_INTRO]
  \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `bb ==> cc` (K ALL_TAC))
  \\ Q.PAT_X_ASSUM `!k. ?b. bbb` (STRIP_ASSUME_TAC o Q.SPEC `10 * k + (ORD h - 48)`)
  \\ ASM_SIMP_TAC std_ss [LENGTH,word_add_n2w,GSYM WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [str2num_def,LENGTH,EXP_ADD,EXP]
  \\ SIMP_TAC std_ss [RIGHT_ADD_DISTRIB]
  \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC,ADD1]);

val arm_readnum_lemma = prove(
  ``!s a df f c1 s1.
      EVERY number_char (EXPLODE s) /\ ~(s = "") /\
      string_mem (STRCAT s (STRING c1 s1)) (a,f,df) /\
      ~(number_char c1) ==>
      arm_readnum_pre (w2w (f a),a,df,f) /\
      ?x y. arm_readnum (w2w (f a),a,df,f) =
            (n2w (str2num s),y,a + n2w (LENGTH s),x,df,f)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC arm_read_loop_lemma
  \\ Q.PAT_X_ASSUM `!k. bbb` (STRIP_ASSUME_TAC o Q.SPECL [`0`])
  \\ ASM_SIMP_TAC std_ss [arm_readnum_pre_def,arm_readnum_def,LET_DEF]);


(* --- READ NUMBER TOKEN --- *)

val (th1,arm_read_number_def,arm_read_number_pre_def) = compile_all ``
  arm_read_number (r4,r5,df,f) =
    let (r3,r4,r5,r6,df,f) = arm_readnum (r4,r5,df,f) in
    let r3 = r3 << 2 in
    let r3 = r3 + 0x2w in
      (r3,r4,r5,r6,df,f)``;

val string_mem_STRCAT = prove(
  ``!s t a df f. string_mem (STRCAT s t) (a,f,df) =
                 string_mem s (a,f,df) /\ string_mem t (a + n2w (LENGTH s),f,df)``,
  Induct \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH,WORD_ADD_0,string_mem_def,STRCAT_def]
  \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,CONJ_ASSOC,
       AC ADD_ASSOC ADD_COMM]);

val arm_read_number_lemma = prove(
  ``!s a df f c1 s1.
      EVERY number_char (EXPLODE s) /\
      string_mem (STRCAT s (STRING c1 s1)) (a,f,df) /\ ~(s = "") /\ ~(number_char c1) ==>
      arm_read_number_pre (w2w (f a),a,df,f) /\
      ?x y z.
        (arm_read_number (w2w (f a),a,df,f) = (ADDR32 (n2w (str2num s)) + 2w,z,x,y,df,f)) /\
        string_mem (STRING c1 s1) (x,f,df)``,
  NTAC 7 STRIP_TAC \\ IMP_RES_TAC arm_readnum_lemma
  \\ ONCE_REWRITE_TAC [arm_read_number_pre_def,arm_read_number_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,string_mem_STRCAT]
  \\ FULL_SIMP_TAC std_ss [string_mem_def,ADDR32_n2w,WORD_MUL_LSL,word_mul_n2w]);


(* --- READ STRING LENGTH --- *)

val space_char_def = Define `
  space_char c = ORD c <= 32`;

val identifier_char_def = Define `
  identifier_char c = ~(space_char c) /\ ~(MEM (STRING c "") ["(";")";"."])`;

val (th1,arm_strlen_def,arm_strlen_pre_def) = compile_all ``
  arm_strlen (r4:word32,r5:word32,df:word32 set,f:word32->word8) =
    if r4 <+ 0x21w then (r4,r5,df,f) else
    if r4 = 0x28w then (r4,r5,df,f) else
    if r4 = 0x29w then (r4,r5,df,f) else
    if r4 = 0x2Ew then (r4,r5,df,f) else
      let r5 = r5 + 0x1w in
      let r4 = w2w (f r5) in
        arm_strlen (r4,r5,df,f)``;

val (th1,arm_string_length_def,arm_string_length_pre_def) = compile_all ``
  arm_string_length (r4:word32,r5:word32,df:word32 set,f:word32->word8) =
    let r7 = r5:word32 in
    let (r4,r5,df,f) = arm_strlen (r4,r5,df,f) in
    let r8 = r5 - r7 in
      (r4,r5,r7,r8,df,f)``

val identifier_lemma = prove(
  ``identifier_char c  =
      let w = (w2w ((n2w (ORD c)):word8)):word32 in
        ~(w <+ 0x21w) /\ ~(w = 0x28w) /\ ~(w = 0x29w) /\ ~(w = 0x2Ew)``,
  SIMP_TAC std_ss [identifier_char_def,MEM,CONS_11,LET_DEF]
  \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND]
  \\ Cases_on `c`
  \\ IMP_RES_TAC ORD_CHR
  \\ ASM_SIMP_TAC std_ss [CHR_11,space_char_def]
  \\ `n < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_LO,w2n_n2w]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val arm_strlen_lemma = prove(
  ``!s a.
      EVERY identifier_char (EXPLODE s) /\ ~(identifier_char c1) /\
      string_mem (STRCAT s (STRING c1 s1)) (a,f,df) ==>
      arm_strlen_pre (w2w (f a),a,df,f) /\
      ?x. arm_strlen (w2w (f a),a,df,f) = (x,a + n2w (LENGTH s),df,f)``,
  Induct \\ SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF,STRCAT_def,string_mem_def]
  THENL [
    ONCE_REWRITE_TAC [arm_strlen_pre_def,arm_strlen_def]
    \\ SIMP_TAC bool_ss [WORD_EQ_SUB_ZERO,LENGTH,WORD_ADD_0]
    \\ STRIP_TAC \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [LET_DEF] identifier_lemma]
    \\ SRW_TAC [] [],
    STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ ONCE_REWRITE_TAC [arm_strlen_def,arm_strlen_pre_def]
    \\ SIMP_TAC bool_ss [WORD_EQ_SUB_ZERO,LENGTH,WORD_ADD_0,LET_DEF]
    \\ RES_TAC \\ Q.PAT_X_ASSUM `~identifier_char c1` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [LET_DEF] identifier_lemma]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC,ADD1]
    \\ Cases_on `s` \\ FULL_SIMP_TAC std_ss [STRCAT_def,string_mem_def]
    \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]]);

val arm_string_length_thm = prove(
  ``!s a.
      EVERY identifier_char (EXPLODE s) /\ ~(identifier_char c1) /\
      string_mem (STRCAT s (STRING c1 s1)) (a,f,df) ==>
      arm_string_length_pre (w2w (f a),a,df,f) /\
      ?x1 x2. arm_string_length (w2w (f a),a,df,f) = (x1,x2,a,n2w (LENGTH s),df,f)``,
  SIMP_TAC bool_ss [arm_string_length_pre_def,arm_string_length_def,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC arm_strlen_lemma
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [WORD_ADD_SUB]);


(* --- TEST STRING EQUALITY --- *)

val (th1,arm_streq_def,arm_streq_pre_def) = compile_all ``
  arm_streq (r4:word32,r5:word32,r6:word32,r7:word32,df:word32 set,dg:word32 set,f:word32->word8,g:word32->word8) =
    if r7 = 0x0w then
      (let r5 = r7 + r5 in (r4,r5,r6,r7,df,dg,f,g))
    else
      (let r4 = w2w (g r6) in
       let r6 = r6 + 0x1w in
         if r4 = w2w (f r5):word32 then
           (let r7 = r7 - 0x1w in
            let r5 = r5 + 0x1w in
              arm_streq (r4,r5,r6,r7,df,dg,f,g))
         else
           (let r5 = r7 + r5 in (r4,r5,r6,r7,df,dg,f,g)))``

val arm_streq_lemma = prove(
  ``!s t a b r4.
      LENGTH s < 2**32 /\
      string_mem s (a,f,df) /\ string_mem t (b,g,dg) /\ (LENGTH t = LENGTH s) ==>
      arm_streq_pre (r4,a,b,n2w (LENGTH s),df,dg,f,g) /\
      ?x4 x5 x6 x7. (arm_streq (r4,a,b,n2w (LENGTH s),df,dg,f,g) =
                     (x4,a + n2w (LENGTH s),x6,x7,df,dg,f,g)) /\
                    ((x7 = 0w) = (s = t))``,
  Induct
  THEN1 (ONCE_REWRITE_TAC [arm_streq_pre_def,arm_streq_def]
         \\ Cases \\ SIMP_TAC std_ss [LENGTH,WORD_ADD_0,LET_DEF,ADD1]
         \\ ONCE_REWRITE_TAC [arm_streq_def]
         \\ SIMP_TAC std_ss [LENGTH,WORD_ADD_0,LET_DEF])
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(1 + n = 0:num)``]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ NTAC 5 STRIP_TAC
  \\ ONCE_REWRITE_TAC [arm_streq_pre_def,arm_streq_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [string_mem_def,w2w_def,w2n_n2w,ORD_BOUND]
  \\ `ORD h' < 256 /\ ORD h < 256` by REWRITE_TAC [ORD_BOUND]
  \\ `ORD h' < 4294967296 /\ ORD h < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,ORD_11]
  THEN1 (`F` by DECIDE_TAC)
  \\ `~(SUC (LENGTH s) = 0)` by DECIDE_TAC
  \\ REVERSE (Cases_on `h' = h`) \\ ASM_SIMP_TAC std_ss [CONS_11] THENL [
    ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM],
    ONCE_REWRITE_TAC [ADD_COMM]
    \\ REWRITE_TAC [GSYM word_add_n2w,WORD_ADD_SUB]
    \\ `LENGTH s < 4294967296` by DECIDE_TAC
    \\ RES_TAC \\ Q.PAT_X_ASSUM `!t a b. bbb` (K ALL_TAC)
    \\ REPEAT (Q.PAT_X_ASSUM `!r4. bbb` (STRIP_ASSUME_TAC o Q.SPECL [`n2w (ORD h)`]))
    \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]]);


(* --- COPY STRING --- *)

val (th1,arm_strcopy_def,arm_strcopy_pre_def) = compile_all ``
  arm_strcopy (r4:word32,r5:word32,r8:word32,df:word32 set,dg:word32 set,f:word32->word8,g:word32->word8) =
    (let r6 = (w2w (f r5)):word32 in
     let r5 = r5 + 0x1w in
     let g = (r4 =+ w2w r6) g in
     let r4 = r4 + 0x1w in
     let r8 = r8 - 0x1w in
       if r8 = 0w then
         (r4,r5,r6,r8,df,dg,f,g)
       else
         arm_strcopy (r4,r5,r8,df,dg,f,g))``

val arm_strcopy_lemma = prove(
  ``!s a b g.
      w2n b + LENGTH s < 2**32 /\ string_mem s (a,f,df) /\
      string_mem_dom s b SUBSET dg /\ ~(s = "") ==>
      arm_strcopy_pre (b,a,n2w (LENGTH s),df,dg,f,g) /\
      ?x3 x4 x5 g'. (arm_strcopy (b,a,n2w (LENGTH s),df,dg,f,g) =
                     (x3,a + n2w (LENGTH s), x4, x5, df,dg,f,g')) /\
                    string_mem s (b,g',dg) /\ !i. i <+ b ==> (g i = g' i)``,
  Induct \\ SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ ONCE_REWRITE_TAC [arm_strcopy_pre_def,arm_strcopy_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ NTAC 5 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [string_mem_def,string_mem_dom_def,INSERT_SUBSET]
  \\ Cases_on `s` THENL [
    SIMP_TAC std_ss [LENGTH,string_mem_def,APPLY_UPDATE_THM]
    \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
    \\ `ORD h < 256` by REWRITE_TAC [ORD_BOUND]
    \\ `ORD h < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [GSYM WORD_NOT_LOWER_EQUAL]
    \\ SIMP_TAC std_ss [WORD_LOWER_OR_EQ,WORD_SUB_REFL,APPLY_UPDATE_THM],
    ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ `LENGTH (STRING h (STRING h' t)) < 4294967296` by
         (FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ `~(LENGTH (STRING h (STRING h' t)) = 1)` by
         (SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
    \\ `(w2n b + 1) < 4294967296` by
         (FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
    \\ `w2n (b + 1w) + LENGTH (STRING h' t) < 4294967296` by
         (ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_def,w2n_n2w]
          \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
    \\ `ORD h < 256` by REWRITE_TAC [ORD_BOUND]
    \\ `ORD h < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
    \\ ONCE_REWRITE_TAC [LENGTH]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
    \\ Q.PAT_X_ASSUM `!a. bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
          Q.SPECL [`a+1w`,`b+1w`,`(b =+ n2w (ORD h)) g`])
    \\ ASM_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ `b <+ b + 1w` by ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,word_add_def,w2n_n2w]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    \\ `~(n2w (STRLEN (STRING h' t)) = 0x0w:word32)` by
     (FULL_SIMP_TAC (std_ss++SIZES_ss) [LENGTH,ADD1,n2w_11]
      \\ `STRLEN t + 1 < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LENGTH,ADD1,n2w_11])
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_TRANS
    \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ REPEAT STRIP_TAC
    \\ RES_TAC
    \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC []]);


(* --- INSERT SYMBOL NAME --- *)

val (th1,arm_symbol_insert_def,arm_symbol_insert_pre_def) = compile_all ``
  arm_symbol_insert (r3,r5,r8,df:word32 set,dg:word32 set,dm:word32 set,f,g,m) =
    (let m = (r3 =+ r8) m in
     let r7 = r8 + 0x3w in
     let r7 = r7 >>> 2 in
     let r7 = r7 << 2 in
     let r7 = r7 + r3 in
     let r7 = r7 + 0x8w in
     let m = (r3 + 0x4w =+ r7) m in
     let r6 = 0x0w:word32 in
     let m = (r7 =+ r6) m in
     let r4 = r3 + 0x8w in
     let (r4,r5,r6,r8,df,dg,f,g) = arm_strcopy (r4,r5,r8,df,dg,f,g) in
       (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m))``

val word_shift_right_n2w = store_thm("word_shift_right_n2w",
  ``!n k. n < dimword (:'a) ==> (n2w n >>> k = n2w (n DIV 2 ** k) :'a word)``,
  SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w] \\ REPEAT STRIP_TAC
  \\ `n DIV 2 ** k <= n` by (MATCH_MP_TAC DIV_LESS_EQ \\ SIMP_TAC std_ss [ZERO_LT_EXP])
  \\ IMP_RES_TAC LESS_EQ_LESS_TRANS
  \\ ASM_SIMP_TAC std_ss []);

val symbol_table_dom_ALIGNED = prove(
  ``!xs a dm dg. symbol_table_dom xs (a,dm,dg) ==> ALIGNED a``,
  Induct \\ SIMP_TAC std_ss [symbol_table_dom_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.PAT_X_ASSUM `ALIGNED b` MP_TAC
  \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4] \\ SIMP_TAC std_ss [WORD_ADD_0]
  \\ ONCE_REWRITE_TAC [GSYM (MATCH_MP MOD_PLUS (DECIDE ``0<4:num``))]
  \\ REWRITE_TAC [EVAL ``8 MOD 4``]
  \\ SIMP_TAC std_ss [SIMP_RULE std_ss [] (Q.SPECL [`4`,`0`] MOD_MULT),WORD_ADD_0]);

val arm_symbol_insert_lemma = prove(
  ``string_mem s (k,f,df) /\ symbol_table [] {} (a,dm,m,dg,g) /\
    symbol_table_dom [s] (a,dm,dg) ==>
    arm_symbol_insert_pre (a,k,n2w (LENGTH s),df,dg,dm,f,g,m) /\
    ?r4i r5i r6i r7i r8i gi mi.
       (arm_symbol_insert (a,k,n2w (LENGTH s),df,dg,dm,f,g,m) =
        (a,r4i,k + n2w (LENGTH s),r6i,r7i,r8i,df,dg,dm,f,gi,mi)) /\
       symbol_table [s] {(a,s)} (a,dm,mi,dg,gi) /\
       !i. i <+ a ==> (gi i = g i) /\ (mi i = m i)``,
  STRIP_TAC \\ IMP_RES_TAC symbol_table_dom_ALIGNED
  \\ FULL_SIMP_TAC std_ss [arm_symbol_insert_pre_def,
       arm_symbol_insert_def,LET_DEF,symbol_table_dom_def]
  \\ `(w2n (a + 8w) = w2n a + 8) /\ (w2n (a + 4w) = w2n a + 4)` by
        (SIMP_TAC (std_ss++SIZES_ss) [word_add_def,w2n_n2w] \\ DECIDE_TAC)
  \\ `w2n (a + 0x8w) + LENGTH s < 2 ** 32` by
       (ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
      Q.SPECL [`s`,`k`,`a+8w`,`g`]) arm_strcopy_lemma
  \\ ASM_SIMP_TAC std_ss [symbol_table_def,LET_DEF,APPLY_UPDATE_THM]
  \\ `a + (n2w (LENGTH s) + 0x3w) >>> 2 << 2 + 8w =
      a + n2w (8 + (LENGTH s + 3) DIV 4 * 4)` by
      (`LENGTH s + 3 < dimword (:32)` by
          (FULL_SIMP_TAC (std_ss++SIZES_ss) [] \\ DECIDE_TAC)
       \\ IMP_RES_TAC word_shift_right_n2w
       \\ ASM_SIMP_TAC std_ss [word_add_n2w,WORD_MUL_LSL,word_mul_n2w,GSYM WORD_ADD_ASSOC]
       \\ SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM, AC MULT_COMM MULT_ASSOC])
  \\ `(n2w (LENGTH s) + 0x3w) >>> 2 << 2 + a + 8w =
      a + n2w (8 + (LENGTH s + 3) DIV 4 * 4)` by
        (FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [SING_DELETE,IN_INSERT]
  \\ ASM_SIMP_TAC std_ss [RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL),
       WORD_EQ_ADD_LCANCEL]
  \\ `(STRLEN s + 3) DIV 4 * 4 <= STRLEN s + 3` by
     (ASSUME_TAC (Q.SPEC `STRLEN s + 3` (SIMP_RULE std_ss [] (Q.SPEC `4` DIVISION)))
      \\ POP_ASSUM (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
      \\ DECIDE_TAC)
  \\ `8 + (LENGTH s + 3) DIV 4 * 4 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,DECIDE ``~(8 + k = 4:num)``]
  \\ FULL_SIMP_TAC std_ss [ALIGNED_INTRO,INSERT_SUBSET]
  \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4] \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ `(w2n (a + n2w (8 + (LENGTH s + 3) DIV 4 * 4)) =
       w2n a + (8 + (LENGTH s + 3) DIV 4 * 4))` by
        (ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_def,w2n_n2w] \\ DECIDE_TAC)
  \\ `a <+ a + 8w /\ a <+ a + 4w /\ a <+ a + n2w (8 + (LENGTH s + 3) DIV 4 * 4)` by
       (ASM_SIMP_TAC std_ss [WORD_LO] \\ DECIDE_TAC)
  \\ IMP_RES_TAC WORD_LOWER_TRANS
  \\ IMP_RES_TAC WORD_LOWER_NOT_EQ
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);




(* --- ADD SYMBOL NAME --- *)

val (th1,arm_symbol_add_def,arm_symbol_add_pre_def) = compile_all ``
  arm_symbol_add (r3,r5,r8,df,dg,dm,f,g,m) =
    (let r4 = m r3 in
       if r4 = 0x0w then
         (let (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m) =
                arm_symbol_insert (r3,r5,r8,df,dg,dm,f,g,m)
          in
            (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m))
       else
         if r4 = r8 then
           (let r7 = r8 in
            let r6 = r3 + 0x8w in
            let (r4,r5,r6,r7,df,dg,f,g) =
                  arm_streq (r4,r5,r6,r7,df,dg,f,g)
            in
              if r7 = 0x0w then
                (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m)
              else
                (let r5 = r5 - r8 in
                 let r3 = m (r3 + 0x4w) in
                   arm_symbol_add (r3,r5,r8,df,dg,dm,f,g,m)))
         else
           (let r3 = m (r3 + 0x4w) in
              arm_symbol_add (r3,r5,r8,df,dg,dm,f,g,m)))``;

val add_symbol_def = Define `
  (add_symbol y [] = [y]) /\
  (add_symbol y (x::xs) = if y = x then x :: xs else x :: add_symbol y xs)`;

val add_symbol_thm = prove(
  ``!xs y. add_symbol y xs = if MEM y xs then xs else xs ++ [y]``,
  Induct \\ SIMP_TAC std_ss [MEM,add_symbol_def,APPEND] \\ METIS_TAC []);

val symbol_table_dom_add_symbol = prove(
  ``!xs s a. symbol_table_dom (add_symbol s xs) (a,dm,dg) ==>
             w2n a + 8 + LENGTH s + 3 < 2**32``,
  Induct \\ REPEAT STRIP_TAC THENL [ALL_TAC, Cases_on `s = h`]
  \\ FULL_SIMP_TAC std_ss [add_symbol_def,symbol_table_dom_def]
  \\ `w2n a <= w2n (a + n2w (8 + (LENGTH h + 3) DIV 4 * 4))` suffices_by
  (STRIP_TAC THEN RES_TAC \\ DECIDE_TAC)
  \\ `(LENGTH h + 3) DIV 4 * 4 <= LENGTH h + 3` by
      (ASSUME_TAC (Q.SPEC `STRLEN h + 3` (SIMP_RULE std_ss [] (Q.SPEC `4` DIVISION)))
        \\ `(LENGTH h + 3) MOD 4 < 4` by SIMP_TAC std_ss [MOD_LESS] \\ DECIDE_TAC)
  \\ `8 + (LENGTH h + 3) DIV 4 * 4 < 4294967296 /\
      w2n a + (8 + (LENGTH h + 3) DIV 4 * 4) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_def,w2n_n2w]);

val arm_symbol_add_string_mem = prove(
  ``!s a g gi dg.
      w2n a + LENGTH s < 4294967296 /\ string_mem s (a,g,dg) /\
      (!i. i <+ a + n2w (LENGTH s) ==> (gi i = g i)) ==>
      string_mem s (a,gi,dg)``,
  Induct \\ SIMP_TAC std_ss [string_mem_def,LENGTH]
  \\ REPEAT STRIP_TAC THENL [
    `a <+ a + n2w (SUC (STRLEN s))` suffices_by METIS_TAC []
    \\ `SUC (LENGTH s) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,word_add_def,w2n_n2w] \\ DECIDE_TAC,
    Q.PAT_X_ASSUM `!x y. bb` MATCH_MP_TAC \\ Q.EXISTS_TAC `g`
    \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
    \\ `w2n a + 1 < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_add_def,w2n_n2w,GSYM ADD_ASSOC,
         DECIDE ``1 + (n:num) = SUC n``]]);

val LESS_EQ_DIV_MULT = prove(
  ``!n. n <= (n + 3) DIV 4 * 4``,
  STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `n + 3` (MATCH_MP (GSYM DIVISION) (DECIDE ``0 < 4:num``)))
  \\ `(n + 3) DIV 4 * 4 = (n + 3) - (n + 3) MOD 4`  by DECIDE_TAC
  \\ ASM_REWRITE_TAC [] \\ DECIDE_TAC);

val arm_symbol_add_lemma = prove(
  ``!xs x s a f g.
      string_mem s (k,f,df) /\ symbol_table xs x (a,dm,m,dg,g) /\
      symbol_table_dom (add_symbol s xs) (a,dm,dg) ==>
      arm_symbol_add_pre (a,k,n2w (LENGTH s),df,dg,dm,f,g,m) /\
      ?r3i r4i r6i r7i r8i gi mi.
         (arm_symbol_add (a,k,n2w (LENGTH s),df,dg,dm,f,g,m) =
          (r3i,r4i,k + n2w (LENGTH s),r6i,r7i,r8i,df,dg,dm,f,gi,mi)) /\
         symbol_table (add_symbol s xs) ((r3i,s) INSERT x) (a,dm,mi,dg,gi) /\
         !i. i <+ a ==> (gi i = g i) /\ (mi i = m i)``,
  Induct THEN1
   (ONCE_REWRITE_TAC [arm_symbol_add_pre_def,arm_symbol_add_def]
    \\ SIMP_TAC std_ss [LET_DEF,add_symbol_def,APPEND,MEM]
    \\ REPEAT STRIP_TAC
    \\ `x = {}` by FULL_SIMP_TAC std_ss [symbol_table_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC arm_symbol_insert_lemma
    \\ IMP_RES_TAC symbol_table_dom_ALIGNED
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [symbol_table_def,ALIGNED_INTRO])
  \\ ONCE_REWRITE_TAC [arm_symbol_add_pre_def,arm_symbol_add_def] \\ REWRITE_TAC [add_symbol_def]
  \\ NTAC 7 STRIP_TAC \\ Cases_on `s = h`
  \\ FULL_SIMP_TAC std_ss [symbol_table_def,symbol_table_dom_def,LET_DEF]
  \\ `LENGTH h < 4294967296` by DECIDE_TAC
  \\ `~(LENGTH h = 0)` by
       (Cases_on `h` \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
  \\ `ALIGNED a` by
     (IMP_RES_TAC symbol_table_dom_ALIGNED
      \\ Q.PAT_X_ASSUM `ALIGNED xxx` MP_TAC
      \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4] \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
      \\ ONCE_REWRITE_TAC [MATCH_MP(GSYM MOD_PLUS) (DECIDE ``0<4:num``)]
      \\ REWRITE_TAC [ADD,EVAL ``8 MOD 4``]
      \\ SIMP_TAC std_ss [MOD_EQ_0,WORD_ADD_0])
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  THEN1
      (STRIP_ASSUME_TAC (UNDISCH_ALL (SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
         (Q.SPECL [`h`,`h`,`k`,`a + 8w`,`n2w (STRLEN h)`] arm_streq_lemma)))
       \\ `((a,h) INSERT x) DELETE (a,h) = x DELETE (a,h)` by (SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE] \\ METIS_TAC [])
       \\ FULL_SIMP_TAC std_ss [ALIGNED_INTRO,INSERT_SUBSET,IN_INSERT])
  \\ REVERSE (Cases_on `STRLEN h = STRLEN s`)
  \\ IMP_RES_TAC symbol_table_dom_add_symbol
  \\ FULL_SIMP_TAC std_ss []
  \\ `STRLEN s < 4294967296` by DECIDE_TAC
  \\ `w2n (a + 8w) = w2n a + 8` by
      (SIMP_TAC (std_ss++SIZES_ss) [word_add_def,w2n_n2w] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,ALIGNED_INTRO,ALIGNED_CLAUSES]
  \\ `(STRLEN h + 3) DIV 4 * 4 <= STRLEN h + 3` by
     (ASSUME_TAC (Q.SPEC `STRLEN h + 3` (SIMP_RULE std_ss [] (Q.SPEC `4` DIVISION)))
      \\ `(STRLEN h + 3) MOD 4 < 4` by SIMP_TAC std_ss [MOD_LESS] \\ DECIDE_TAC)
  \\ `(STRLEN s + 3) DIV 4 * 4 <= STRLEN s + 3` by
     (ASSUME_TAC (Q.SPEC `STRLEN s + 3` (SIMP_RULE std_ss [] (Q.SPEC `4` DIVISION)))
      \\ `(STRLEN s + 3) MOD 4 < 4` by SIMP_TAC std_ss [MOD_LESS] \\ DECIDE_TAC)
  THEN1
     (Q.ABBREV_TAC `a2 = a + n2w (8 + (LENGTH h + 3) DIV 4 * 4)`
      \\ `w2n a + 4 < 4294967296 /\
          (w2n a + (8 + (STRLEN h + 3) DIV 4 * 4)) < 4294967296 /\
          8 + (STRLEN h + 3) DIV 4 * 4 < 4294967296` by
            (ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ `a <+ a2 /\ a + 4w <+ a2` by
        (Q.UNABBREV_TAC `a2` \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,word_add_def,w2n_n2w] \\ DECIDE_TAC)
      \\ Q.PAT_X_ASSUM `!s a f g. bb` (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
           Q.SPECL [`x DELETE (a,h)`,`s`,`a2`,`f`,`g`])
      \\ `(((r3i,s) INSERT x) DELETE (a,h)) = (r3i,s) INSERT (x DELETE (a,h))` by (ASM_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE] \\ METIS_TAC [PAIR_EQ,PAIR])
      \\ ASM_SIMP_TAC std_ss [WORD_LOWER_TRANS,IN_INSERT]
      \\ REVERSE STRIP_TAC THEN1 METIS_TAC [WORD_LOWER_TRANS]
      \\ MATCH_MP_TAC arm_symbol_add_string_mem \\ Q.EXISTS_TAC `g`
      \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w]
      \\ REPEAT STRIP_TAC
      \\ `a + n2w (8 + STRLEN h) <=+ a2` suffices_by METIS_TAC [WORD_LOWER_LOWER_EQ_TRANS]
      \\ Q.UNABBREV_TAC `a2`
      \\ `8 + STRLEN h < 4294967296 /\
          w2n a + (8 + STRLEN h) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LS,word_add_def,w2n_n2w,LESS_EQ_DIV_MULT])
  THEN1
     (STRIP_ASSUME_TAC (UNDISCH_ALL (REWRITE_RULE [GSYM AND_IMP_INTRO, EVAL ``(2:num)**32``]
        (Q.SPECL [`s`,`h`,`k`,`a + 8w`,`n2w (STRLEN s)`] arm_streq_lemma)))
      \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB]
      \\ Q.ABBREV_TAC `a2 = a + n2w (8 + (STRLEN s + 3) DIV 4 * 4)`
      \\ Q.PAT_X_ASSUM `!s a f g. bb` (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
           Q.SPECL [`x DELETE (a,h)`,`s`,`a2`,`f`,`g`])
      \\ ASM_SIMP_TAC std_ss []
      \\ `w2n a + 4 < 4294967296 /\
          (w2n a + (8 + (STRLEN s + 3) DIV 4 * 4)) < 4294967296 /\
          8 + (STRLEN s + 3) DIV 4 * 4 < 4294967296` by DECIDE_TAC
      \\ `a <+ a2 /\ a + 4w <+ a2` by
        (Q.UNABBREV_TAC `a2` \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,word_add_def,w2n_n2w] \\ DECIDE_TAC)
      \\ `(((r3i,s) INSERT x) DELETE (a,h)) = (r3i,s) INSERT (x DELETE (a,h))` by (ASM_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE] \\ METIS_TAC [PAIR_EQ,PAIR])
      \\ ASM_SIMP_TAC std_ss [WORD_LOWER_TRANS,IN_INSERT]
      \\ REVERSE STRIP_TAC THEN1 METIS_TAC [WORD_LOWER_TRANS]
      \\ MATCH_MP_TAC arm_symbol_add_string_mem \\ Q.EXISTS_TAC `g`
      \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w]
      \\ REPEAT STRIP_TAC
      \\ `a + n2w (8 + STRLEN s) <=+ a2` suffices_by METIS_TAC [WORD_LOWER_LOWER_EQ_TRANS]
      \\ Q.UNABBREV_TAC `a2`
      \\ `8 + STRLEN s < 4294967296 /\
          w2n a + (8 + STRLEN s) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_LS,word_add_def,w2n_n2w,LESS_EQ_DIV_MULT]));


(* --- UPDATE SYMBOL TABLE --- *)

val (th1,arm_symbol_def,arm_symbol_pre_def) = compile_all ``
  arm_symbol (r3,r4,r5,df,dg,dm,f,g,m) =
    (let r7 = r5 in
     let (r4,r5,df,f) = arm_strlen (r4,r5,df,f) in
     let r8 = r5 - r7 in
     let r5 = r5 - r8 in
     let (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m) =
           arm_symbol_add (r3,r5,r8,df,dg,dm,f,g,m)
     in
     let r3 = r3 + 0x3w in
       (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m))``;

val arm_symbol_lemma = prove(
  ``!xs s a f g.
      EVERY identifier_char (EXPLODE s) /\ ~identifier_char c1 /\
      string_mem (STRCAT s (STRING c1 s1)) (k,f,df) /\
      symbol_table xs x (a,dm,m,dg,g) /\
      symbol_table_dom (add_symbol s xs) (a,dm,dg) ==>
      arm_symbol_pre (a,w2w (f k),k,df,dg,dm,f,g,m) /\
      ?r3i r4i r5i r6i r7i r8i gi mi.
         (arm_symbol (a,w2w (f k),k,df,dg,dm,f,g,m) =
          (r3i,r4i,r5i,r6i,r7i,r8i,df,dg,dm,f,gi,mi)) /\
         symbol_table (add_symbol s xs) ((r3i - 3w,s) INSERT x) (a,dm,mi,dg,gi) /\
         string_mem (STRING c1 s1) (r5i,f,df)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss[arm_symbol_def,arm_symbol_pre_def,LET_DEF]
  \\ SIMP_TAC std_ss [GSYM WORD_NEG_MUL,GSYM (RW1 [WORD_ADD_COMM] word_sub_def)]
  \\ IMP_RES_TAC arm_strlen_lemma
  \\ ASM_SIMP_TAC std_ss []
  \\ REWRITE_TAC [WORD_SUB_SUB2]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [string_mem_STRCAT]
  \\ IMP_RES_TAC arm_symbol_add_lemma
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_ADD,WORD_ADD_SUB]);


(* --- LEX SYMBOL AND NUMBER --- *)

val (th1,arm_number_symbol_def,arm_number_symbol_pre_def) = compile_all ``
  arm_number_symbol (r9,r3,r4,r5,r7,r8,df,dg,dh:word32 set,dm,f,g,h:word32->word32,m) =
    if ~(r4 <+ 0x30w) then
      if ~(r4 <+ 0x3Aw) then
        (let (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m) =
               arm_symbol (r3,r4,r5,df,dg,dm,f,g,m)
         in
         let r4 = h (r9 + 4w) in
         let r3 = r3 - r4 in
         let r4 = (w2w (f r5)):word32 in
         let h = (r9 =+ r3) h in
         let r9 = r9 + 0x8w in
           (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m))
      else
        (let (r3,r4,r5,r6,df,f) = arm_read_number (r4,r5,df,f) in
         let r4 = w2w (f r5) in
         let h = (r9 =+ r3) h in
         let r9 = r9 + 0x8w in
           (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m))
    else
      (let (r3,r4,r5,r6,r7,r8,df,dg,dm,f,g,m) =
             arm_symbol (r3,r4,r5,df,dg,dm,f,g,m)
       in
       let r4 = h (r9 + 4w) in
       let r3 = r3 - r4 in
       let r4 = w2w (f r5) in
       let h = (r9 =+ r3) h in
       let r9 = r9 + 0x8w in
         (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m))``;


(* --- LEXER AUX --- *)

val (th1,arm_lexer_aux_def,arm_lexer_aux_pre_def) = compile_all ``
  arm_lexer_aux (r4:word32,r6:word32) =
    if r4 = 0x27w then let r6 = 0x10w in (r4,r6) else
    if r4 = 0x2Ew then let r6 = 0xCw in (r4,r6) else
    if r4 = 0x29w then let r6 = 0x8w in (r4,r6) else
    if r4 = 0x28w then let r6 = 0x4w in (r4,r6) else
    (r4,r6)``;


(* --- LEXER --- *)

val (th1,arm_lexer_def,arm_lexer_pre_def) = compile_all ``
  arm_lexer (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
    if r4 = 0x0w then
      (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m)
    else
      if ~(r4 <+ 0x21w) then
        (let r6 = 0x0w in
         let (r4,r6) = arm_lexer_aux (r4,r6) in
           if r6 = 0x0w then
             (let h = (r9 + 4w =+ r3) h in
              let (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
                    arm_number_symbol
                      (r9,r3,r4,r5,r7,r8,df,dg,dh,dm,f,g,h,m)
              in
              let r3 = h (r9 - 4w) in
                arm_lexer (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m))
           else
             (let h = (r9 =+ r6) h in
              let r9 = r9 + 0x8w in
              let r5 = r5 + 0x1w in
              let r4 = w2w (f r5) in
                arm_lexer
                  (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m)))
      else
        (let r5 = r5 + 0x1w in
         let r4 = w2w (f r5) in
           arm_lexer (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m))``;

val read_while_def = Define `
  (read_while P "" s = (s,"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (STRCAT s (STRING c ""))
            else (s,STRING c cs))`;

val read_while_thm = prove(
  ``!cs s cs' s'.
       (read_while P cs s = (s',cs')) ==> LENGTH cs' <= LENGTH cs + LENGTH s``,
  Induct \\ SIMP_TAC std_ss [read_while_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_STRCAT]
  \\ REPEAT (Q.PAT_X_ASSUM `STRING c cs = cs'` (ASSUME_TAC o GSYM))
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_STRCAT] \\ DECIDE_TAC);

val sexp_lex_def = tDefine "sexp_lex" `
  (sexp_lex "" = []) /\
  (sexp_lex (STRING c cs) =
    if space_char c then sexp_lex cs else
    if MEM c [#"(";#")";#".";#"'"] then (STRING c "") :: sexp_lex cs else
    if number_char c then
      (let (x,cs) = read_while number_char cs "" in (STRING c x) :: sexp_lex cs) else
      (let (x,cs) = read_while identifier_char cs "" in (STRING c x) :: sexp_lex cs))`
  (WF_REL_TAC `measure (LENGTH)` \\ REPEAT STRIP_TAC
   \\ IMP_RES_TAC (GSYM read_while_thm)
   \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)

val null_string_def = Define `null_string = STRING (CHR 0) ""`;

val identifier_string_def = Define `
  identifier_string s =
    EVERY identifier_char (EXPLODE s) /\ ~(number_char (HD (EXPLODE s))) /\
    ~(HD (EXPLODE s) = #"'")`;

val all_symbols_def = Define `
  (all_symbols [] xs = xs) /\
  (all_symbols (c::cs) xs =
     if identifier_string c
     then all_symbols cs (add_symbol c xs) else all_symbols cs xs)`;

val read_while_thm2_lemma = prove(
  ``!cs s P. ?t1 t2. (read_while P cs s = (t1,t2)) /\ (STRCAT s cs = STRCAT t1 t2) /\
                     (EVERY P (EXPLODE s) ==> EVERY P (EXPLODE t1)) /\
                     (~(t2 = "") ==> ~ P (HD (EXPLODE t2)))``,
  Induct \\ SIMP_TAC std_ss [read_while_def,EXPLODE_def,EVERY_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `P h` \\ ASM_SIMP_TAC std_ss [EXPLODE_def,HD]
  \\ Q.PAT_X_ASSUM `!s. bbb` (STRIP_ASSUME_TAC o Q.SPECL [`STRCAT s (STRING h "")`,`P`])
  \\ FULL_SIMP_TAC std_ss [EXPLODE_STRCAT,EVERY_APPEND,EXPLODE_def,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [GSYM STRCAT_ASSOC,STRCAT_def]);

val read_while_thm2 =
  GEN_ALL (RW [STRCAT_def,EXPLODE_def,EVERY_DEF] (Q.SPECL [`cs`,`""`] read_while_thm2_lemma));

val symbol_table_dom_IMPLIES = prove(
  ``!xs ys a dm dg.
      symbol_table_dom (all_symbols xs ys) (a,dm,dg) ==>
      symbol_table_dom ys (a,dm,dg)``,
  Induct \\ REWRITE_TAC [all_symbols_def] \\ NTAC 5 STRIP_TAC
  \\ Cases_on `identifier_string h` \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ REWRITE_TAC [add_symbol_thm]
  \\ Cases_on `MEM h ys` THEN1 METIS_TAC []
  \\ ASM_REWRITE_TAC []
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`a`,`a`)
  \\ Induct_on `ys` THENL [
    SIMP_TAC std_ss [symbol_table_dom_def,INSERT_SUBSET]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC symbol_table_dom_ALIGNED
    \\ FULL_SIMP_TAC std_ss [symbol_table_dom_def,INSERT_SUBSET,APPEND],
    REWRITE_TAC [APPEND]
    \\ ONCE_REWRITE_TAC [symbol_table_dom_def]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ ASM_SIMP_TAC std_ss []]);

open set_sepTheory;

val arm_token_def = Define `
  arm_token w str b x =
    if str = "(" then (w =  4w) else
    if str = ")" then (w =  8w) else
    if str = "." then (w = 12w) else
    if str = "'" then (w = 16w) else
    if EVERY number_char (EXPLODE str)
    then (w = ADDR32 (n2w (str2num str)) + 2w)
    else (b + w - 3w, str) IN x /\ ALIGNED (w - 3w)`;

val arm_tokens_def = Define `
  (arm_tokens a [] b x y = cond (a = y)) /\
  (arm_tokens a (str::xs) b x y =
     SEP_EXISTS w1:word32 w2:word32. one (a,w1) * one (a+4w,w2) *
                       cond (arm_token w1 str b x) *
                       arm_tokens (a + 8w:word32) xs b x y)`;

val token_slots_def = Define `
  (token_slots a 0 = emp) /\
  (token_slots a (SUC n) =
     SEP_EXISTS w1:word32 w2:word32. one (a,w1) * one (a+4w,w2) *
                                     token_slots (a + 8w:word32) n)`;

val symbol_table_IMP_ALIGNED = prove(
  ``!xs x r3 a y. (a,y) IN x /\ ALIGNED r3 /\
                  symbol_table xs x (r3,dm,mi,dg,gi) ==>
                  ALIGNED a``,
  Induct
  \\ REWRITE_TAC [symbol_table_def] THEN1 METIS_TAC [NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `(a,y) = (r3,h)` THEN1 METIS_TAC [PAIR_EQ]
  \\ `(a,y) IN (x DELETE (r3,h))` by ASM_SIMP_TAC std_ss [IN_DELETE]
  \\ `ALIGNED (r3 + n2w (8 + (STRLEN h + 3) DIV 4 * 4))` suffices_by METIS_TAC []
  \\ REWRITE_TAC [GSYM word_add_n2w]
  \\ MATCH_MP_TAC ALIGNED_ADD \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC ALIGNED_ADD \\ ASM_SIMP_TAC std_ss [ALIGNED_n2w]
  \\ SIMP_TAC std_ss [MOD_EQ_0]);

val string_mem_IMP_IN = prove(
  ``!t x f df. string_mem (STRCAT t null_string) (x,f,df) ==> x IN df``,
  Cases \\ FULL_SIMP_TAC std_ss [APPEND,null_string_def,string_mem_def]);

val arm_lexer_lemma = prove(
  ``!s r1 r3 k r6 r7 r8 p x xs df dg dh dm f g h m.
      string_mem (STRCAT s null_string) (k,f,df) /\
      (EVERY (\c. ~(ORD c = 0)) (EXPLODE s)) /\
      symbol_table xs x (r3,dm,m,dg,g) /\ ALIGNED r1 /\
      (p * token_slots r1 (LENGTH (sexp_lex s))) (fun2set (h,dh)) /\
      symbol_table_dom (all_symbols (sexp_lex s) xs) (r3,dm,dg) ==>
      ?r1i r4i r5i r6i r7i r8i gi hi mi xi.
        arm_lexer_pre (r1,r3,w2w (f k),k,r6,r7,r8,df,dg,dh,dm,f,g,h,m) /\
        (arm_lexer (r1,r3,w2w (f k),k,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
            (r1i,r3,r4i,r5i,r6i,r7i,r8i,df,dg,dh,dm,f,gi,hi,mi)) /\
        (p * arm_tokens r1 (sexp_lex s) r3 xi r1i) (fun2set (hi,dh)) /\
        (r1 + n2w (8 * LENGTH (sexp_lex s)) = r1i) /\
        symbol_table (all_symbols (sexp_lex s) xs) xi (r3,dm,mi,dg,gi) /\
        x SUBSET xi``,
  completeInduct_on `STRLEN s` \\ Cases THEN1
   (SIMP_TAC std_ss [STRCAT_def,null_string_def,string_mem_def]
    \\ ONCE_REWRITE_TAC [arm_lexer_def,arm_lexer_pre_def]
    \\ SIMP_TAC std_ss [sexp_lex_def,all_symbols_def,arm_tokens_def,LENGTH,WORD_ADD_0]
    \\ SIMP_TAC std_ss [EVAL ``(w2w (n2w (ORD #"\^@") :word8)):word32``]
    \\ SIMP_TAC std_ss [token_slots_def,SEP_CLAUSES]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x` \\ ASM_REWRITE_TAC [SUBSET_REFL])
  \\ SIMP_TAC std_ss [EVERY_DEF,EXPLODE_def,STRCAT_def,string_mem_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND]
  \\ ONCE_REWRITE_TAC [arm_lexer_def,arm_lexer_pre_def]
  \\ REPEAT STRIP_TAC
  \\ `ORD h < 256` by REWRITE_TAC [ORD_BOUND]
  \\ `ORD h < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ `k + 0x1w IN df` by (IMP_RES_TAC string_mem_IMP_IN)
  \\ Cases_on `space_char h` THEN1
   (FULL_SIMP_TAC std_ss [sexp_lex_def]
    \\ FULL_SIMP_TAC std_ss [space_char_def]
    \\ `ORD h < 33` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,WORD_LO,w2n_n2w]
    \\ Q.PAT_X_ASSUM `!xyz. myz` (ASSUME_TAC o Q.SPEC `STRLEN t`)
    \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``m < m + 1:num``]
    \\ Q.PAT_X_ASSUM `!xys. msd` (ASSUME_TAC o RW [] o Q.SPEC `t`)
    \\ RES_TAC \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`r8`,`r7`,`r6`])
    \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `xi`
    \\ ASM_SIMP_TAC std_ss [])
  \\ `~(n2w (ORD h) <+ 0x21w:word32)` by
   (FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w,space_char_def] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `MEM (ORD h) [40;41;39;46]` THEN1
   (`?x2 y2. (arm_lexer_aux (n2w (ORD h),0w) = (x2,y2)) /\ ~(y2 = 0w)` by FULL_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,MEM,arm_lexer_aux_def,n2w_11]
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ Q.PAT_X_ASSUM `!x. mq` (ASSUME_TAC o Q.SPEC `STRLEN t`)
    \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``m < m + 1:num``]
    \\ Q.PAT_X_ASSUM `!x. mq` (ASSUME_TAC o RW [] o Q.SPEC `t`)
    \\ `sexp_lex (STRING h t) = STRING h ""::sexp_lex t` by
         FULL_SIMP_TAC std_ss [sexp_lex_def,MEM,GSYM ORD_11,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``]
    \\ FULL_SIMP_TAC std_ss []
    \\ `~identifier_string (STRING h "")` by
      FULL_SIMP_TAC std_ss [all_symbols_def,EXPLODE_def,EVERY_DEF,
       identifier_char_def,MEM,CONS_11,GSYM ORD_11,identifier_string_def,HD,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``]
    \\ FULL_SIMP_TAC std_ss [all_symbols_def,arm_tokens_def,LENGTH,RW1[MULT_COMM]MULT]
    \\ FULL_SIMP_TAC std_ss [token_slots_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
    \\ `(p * one (r1,y2) * one (r1 + 0x4w,y') *
         token_slots (r1 + 0x8w) (LENGTH (sexp_lex t)))
        (fun2set ((r1 =+ y2) h',dh))` by SEP_WRITE_TAC
    \\ `ALIGNED (r1+8w)` by ALIGNED_TAC
    \\ Q.PAT_X_ASSUM `!r1 r2. bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.SPECL
        [`r1+8w`,`r3`,`k+1w`,`y2`,`r7`,`r8`,`p * one (r1,y2) * one (r1 + 0x4w,y')`,`x`,`xs`,`df`,`dg`,`dh`,`dm`,`f`,`g`,`(r1 =+ y2) h'`,`m`])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `xi` \\ ASM_SIMP_TAC std_ss [SUBSET_REFL]
    \\ `(h' r1 = y) /\ r1 IN dh` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
    \\ STRIP_TAC THEN1
     (REWRITE_TAC [GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
    \\ Q.ABBREV_TAC `i = r1 + n2w (8 * LENGTH (sexp_lex t) + 8)`
    \\ Q.EXISTS_TAC `y2` \\ Q.EXISTS_TAC `y'`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ STRIP_TAC THEN1
     (Q.PAT_X_ASSUM `arm_lexer_aux (n2w (ORD h),0x0w) = (x2,y2)` (ASSUME_TAC o GSYM)
      \\ Q.PAT_X_ASSUM `MEM (ORD h) [40; 41; 39; 46]`
          (STRIP_ASSUME_TAC o RW [MEM])
      \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [arm_lexer_aux_def,LET_DEF,n2w_11,arm_token_def,CONS_11]
      \\ ASM_REWRITE_TAC [GSYM ORD_11] \\ EVAL_TAC)
    \\ `r1 + 0x8w + n2w (8 * LENGTH (sexp_lex t)) = i` by
     (Q.UNABBREV_TAC `i`
      \\ SIMP_TAC std_ss [GSYM word_add_n2w,
          AC WORD_ADD_ASSOC WORD_ADD_COMM])
    \\ FULL_SIMP_TAC std_ss [])
  \\ `arm_lexer_aux (n2w (ORD h),0w) = (n2w (ORD h),0w)` by FULL_SIMP_TAC (std_ss++SIZES_ss) [arm_lexer_aux_def,MEM,n2w_11,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,arm_number_symbol_def,arm_number_symbol_pre_def]
  \\ Cases_on `number_char h` THEN1
   (FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w,number_char_def,
      DECIDE ``48 <= n = ~(n < 48:num)``]
    \\ STRIP_ASSUME_TAC (Q.SPECL [`t`,`number_char`] read_while_thm2)
    \\ `sexp_lex (STRING h t) = STRING h t1 :: sexp_lex t2` by
     (ONCE_REWRITE_TAC [sexp_lex_def]
      \\ ASM_SIMP_TAC std_ss [space_char_def,MEM,GSYM ORD_11,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``]
      \\ FULL_SIMP_TAC std_ss [number_char_def,MEM,DECIDE ``48 <= m = ~(m < 48:num)``,LET_DEF])
    \\ FULL_SIMP_TAC std_ss [GSYM STRCAT_ASSOC]
    \\ `EVERY number_char (EXPLODE (STRING h t1))` by
          (ASM_SIMP_TAC std_ss [number_char_def,EXPLODE_def,EVERY_DEF] \\ DECIDE_TAC)
    \\ `?c2 t3. (STRCAT t2 null_string = STRING c2 t3) /\ ~(number_char c2)` by
       (Cases_on `t2` \\ SIMP_TAC std_ss [STRCAT_def,null_string_def,CONS_11]
        THEN1 EVAL_TAC \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,EXPLODE_def,HD])
    \\ FULL_SIMP_TAC std_ss []
    \\ `string_mem (STRCAT (STRING h t1) (STRING c2 t3)) (k,f,df)` by
          ASM_SIMP_TAC std_ss [STRCAT_def,string_mem_def]
    \\ STRIP_ASSUME_TAC ((UNDISCH_ALL o SIMP_RULE std_ss [GSYM NOT_CONS_NIL,GSYM AND_IMP_INTRO])
      (Q.SPECL [`STRING h t1`,`k`,`df`,`f`,`c2`,`t3`] arm_read_number_lemma))
    \\ `w2w (f k) = n2w (ORD h):word32` by
      ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `STRCAT t2 null_string = STRING c2 t3` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH t2 < LENGTH (STRING h (STRCAT t1 t2))` by
       (SIMP_TAC std_ss [LENGTH,LENGTH_STRCAT] \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `!m. bb ==> ccc` (ASSUME_TAC o
         RW [] o Q.SPEC `t2` o UNDISCH o Q.SPEC `STRLEN t2`)
    \\ FULL_SIMP_TAC std_ss [LENGTH,token_slots_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
    \\ Q.ABBREV_TAC [ANTIQUOTE ``n = ADDR32 (n2w (str2num (STRING h t1))) + 2w``]
    \\ FULL_SIMP_TAC std_ss [EXPLODE_STRCAT,EVERY_APPEND,LENGTH,RW1[MULT_COMM]MULT]
    \\ `~identifier_string (STRING h t1)` by
     (FULL_SIMP_TAC std_ss [identifier_string_def,EXPLODE_def,HD,number_char_def]
      \\ ASM_SIMP_TAC std_ss [DECIDE ``48 <= m = ~(m < 48:num)``])
    \\ FULL_SIMP_TAC std_ss [all_symbols_def]
    \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,word_arith_lemma4]
    \\ SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11]
    \\ `(p * one (r1,n) * one (r1 + 0x4w,r3) *
         token_slots (r1 + 0x8w) (LENGTH (sexp_lex t2)))
         (fun2set ((r1 =+ n) ((r1 + 0x4w =+ r3) h'),dh))` by SEP_WRITE_TAC
    \\ `ALIGNED (r1+8w)` by ALIGNED_TAC
    \\ Q.PAT_X_ASSUM `!r1 r2. bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.SPECL
         [`r1+8w`,`r3`,`x'`,`y`,`r7`,`r8`,`p * one (r1,n) * one (r1 + 0x4w,r3)`,`x`,`xs`,`df`,`dg`,`dh`,`dm`,`f`,`g`,`(r1 =+ n) ((r1 + 4w =+ r3) h')`,`m`])
    \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `xi` \\ ASM_SIMP_TAC std_ss [SUBSET_REFL]
    \\ `(h' r1 = y') /\ r1 IN dh` by SEP_READ_TAC
    \\ `(h' (r1 + 4w) = y'') /\ r1 + 4w IN dh` by SEP_READ_TAC
    \\ IMP_RES_TAC string_mem_IMP_IN
    \\ `ALIGNED (r1 + 0x4w)` by ALIGNED_TAC
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
    \\ STRIP_TAC THEN1
     (REWRITE_TAC [GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
    \\ Q.ABBREV_TAC `i = r1 + n2w (8 * LENGTH (sexp_lex t) + 8)`
    \\ REWRITE_TAC [arm_tokens_def]
    \\ SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `n` \\ Q.EXISTS_TAC `r3`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ STRIP_TAC THEN1
     (POP_ASSUM (K ALL_TAC)
      \\ Q.UNABBREV_TAC `n`
      \\ ASM_REWRITE_TAC [arm_token_def,CONS_11,GSYM ORD_11]
      \\ REWRITE_TAC [EVAL ``ORD #"'"``]
      \\ REWRITE_TAC [EVAL ``ORD #"."``]
      \\ REWRITE_TAC [EVAL ``ORD #"("``]
      \\ REWRITE_TAC [EVAL ``ORD #")"``]
      \\ FULL_SIMP_TAC std_ss [MEM])
    \\ FULL_SIMP_TAC (std_ss++star_ss) [
        AC ADD_COMM ADD_ASSOC,
        GSYM WORD_ADD_ASSOC,word_add_n2w])
  \\ `~(n2w (ORD h) <+ 0x30w:word32) ==> ~(n2w (ORD h) <+ 0x3Aw:word32)` by
    (FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w,number_char_def] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_ASSUME_TAC (Q.SPECL [`t`,`identifier_char`] read_while_thm2)
  \\ `sexp_lex (STRING h t) = STRING h t1 :: sexp_lex t2` by
     (ONCE_REWRITE_TAC [sexp_lex_def]
      \\ ASM_SIMP_TAC std_ss [space_char_def,MEM,GSYM ORD_11,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``]
      \\ FULL_SIMP_TAC std_ss [number_char_def,MEM,DECIDE ``48 <= m = ~(m < 48:num)``,LET_DEF])
  \\ FULL_SIMP_TAC std_ss [GSYM STRCAT_ASSOC]
  \\ `EVERY identifier_char (EXPLODE (STRING h t1))` by
        (FULL_SIMP_TAC std_ss [identifier_char_def,EXPLODE_def,EVERY_DEF,MEM,CONS_11,GSYM ORD_11,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``])
  \\ `?c2 t3. (STRCAT t2 null_string = STRING c2 t3) /\ ~(identifier_char c2)` by
       (Cases_on `t2` \\ SIMP_TAC std_ss [STRCAT_def,null_string_def,CONS_11]
        THEN1 EVAL_TAC \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,EXPLODE_def,HD])
  \\ FULL_SIMP_TAC std_ss []
  \\ `string_mem (STRCAT (STRING h t1) (STRING c2 t3)) (k,f,df)` by
        ASM_SIMP_TAC std_ss [STRCAT_def,string_mem_def]
  \\ `identifier_string (STRING h t1)` by
    FULL_SIMP_TAC std_ss [identifier_string_def,EXPLODE_def,HD,GSYM ORD_11, EVAL ``ORD #"'"``,MEM]
  \\ FULL_SIMP_TAC std_ss [all_symbols_def]
  \\ IMP_RES_TAC symbol_table_dom_IMPLIES
  \\ STRIP_ASSUME_TAC (UNDISCH_ALL (SIMP_RULE std_ss [GSYM NOT_CONS_NIL,GSYM AND_IMP_INTRO]
       (Q.INST [`c1`|->`c2`,`s1`|->`t3`]
       (Q.SPECL [`xs`,`STRING h t1`,`r3`,`f`,`g`] arm_symbol_lemma))))
  \\ ASM_SIMP_TAC std_ss []
  \\ `w2w (f k) = n2w (ORD h):word32` by
    ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!xx. bb ==> bbb` (ASSUME_TAC o Q.SPEC `STRLEN t2`)
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_STRCAT,DECIDE ``n < SUC (m + n:num)``]
  \\ Q.PAT_X_ASSUM `!xx. bb` (ASSUME_TAC o RW [] o Q.SPEC `t2`)
  \\ `string_mem (STRCAT t2 null_string) (r5i,f,df)` by ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EXPLODE_STRCAT,EVERY_APPEND,LENGTH,RW1[MULT_COMM]MULT]
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,word_arith_lemma4]
  \\ SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11]
  \\ FULL_SIMP_TAC std_ss [LENGTH,token_slots_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
  \\ `(p * one (r1,r3i - r3) * one (r1 + 0x4w,r3) *
       token_slots (r1 + 0x8w) (LENGTH (sexp_lex t2)))
         (fun2set ((r1 =+ r3i - r3) ((r1 + 0x4w =+ r3) h'),dh))` by SEP_WRITE_TAC
  \\ `ALIGNED (r1+8w)` by ALIGNED_TAC
  \\ Q.PAT_X_ASSUM `!r1 r2. bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.SPECL
       [`r1+8w`,`r3`,`r5i`,`r6i`,`r7i`,`r8i`,`p * one (r1,r3i - r3) * one (r1 + 4w,r3)`,`(r3i - 3w, STRING h t1)  INSERT x`,`add_symbol (STRING h t1) xs`,`df`,`dg`,`dh`,`dm`,`f`,`gi`,`(r1 =+ r3i - r3) ((r1 + 4w =+ r3) h')`,`mi`])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `xi` \\ ASM_SIMP_TAC std_ss [SUBSET_REFL]
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET]
  \\ `ALIGNED (r1+4w)` by ALIGNED_TAC
  \\ IMP_RES_TAC string_mem_IMP_IN
  \\ `(hi (r1 + 4w) = r3) /\ r1 + 0x4w IN dh` by SEP_READ_TAC
  \\ `(hi r1 = r3i-r3) /\ r1 IN dh` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
  \\ STRIP_TAC THEN1
     (REWRITE_TAC [GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  \\ REWRITE_TAC [arm_tokens_def]
  \\ SIMP_TAC std_ss [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ Q.EXISTS_TAC `r3i - r3`
  \\ Q.EXISTS_TAC `r3`
  \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [
        AC ADD_COMM ADD_ASSOC,
        GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ ASM_SIMP_TAC std_ss [arm_token_def,WORD_SUB_ADD2]
  \\ ASM_REWRITE_TAC [arm_token_def,CONS_11,GSYM ORD_11]
  \\ REWRITE_TAC [EVAL ``ORD #"'"``]
  \\ REWRITE_TAC [EVAL ``ORD #"."``]
  \\ REWRITE_TAC [EVAL ``ORD #"("``]
  \\ REWRITE_TAC [EVAL ``ORD #")"``]
  \\ FULL_SIMP_TAC std_ss [MEM]
  \\ ASM_SIMP_TAC std_ss [EVERY_DEF,EXPLODE_def]
  \\ `(r3i - 0x3w,STRING h t1) IN ((r3i - 0x3w,STRING h t1) INSERT x)`
        by SIMP_TAC std_ss [IN_INSERT]
  \\ IMP_RES_TAC symbol_table_dom_ALIGNED
  \\ IMP_RES_TAC symbol_table_IMP_ALIGNED
  \\ REPEAT (Q.PAT_X_ASSUM `ALIGNED xxx` MP_TAC)
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ ONCE_REWRITE_TAC [word_sub_def]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ONCE_REWRITE_TAC [word_sub_def]
  \\ REWRITE_TAC [WORD_ADD_ASSOC]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ALIGNED_ADD
  \\ ASM_SIMP_TAC std_ss [ALIGNED_NEG]);


(* --- PARSER --- *)

val LIST_STRCAT_def = Define `
  (LIST_STRCAT [] = "") /\
  (LIST_STRCAT (x::xs) = STRCAT x (LIST_STRCAT xs))`;

val sexp2string_aux_def = tDefine "sexp2string_aux" `
  (sexp2string_aux (Val n, b) = num2str n) /\
  (sexp2string_aux (Sym s, b) = s) /\
  (sexp2string_aux (Dot x y, b) =
     if isQuote (Dot x y) /\ b then LIST_STRCAT ["'"; sexp2string_aux (CAR y,T)] else
       let (a,e) = if b then ("(",")") else ("","") in
         if y = Sym "nil" then LIST_STRCAT [a; sexp2string_aux (x,T); e] else
         if isDot y
         then LIST_STRCAT [a; sexp2string_aux (x,T); " "; sexp2string_aux (y,F); e]
         else LIST_STRCAT [a; sexp2string_aux (x,T); " . "; sexp2string_aux (y,F); e])`
 (WF_REL_TAC `measure (LSIZE o FST)` \\ REWRITE_TAC [LSIZE_def,ADD1]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,LSIZE_def]
  \\ DECIDE_TAC);

val sexp2string_def = Define `sexp2string x = sexp2string_aux (x, T)`;

val sexp2tokens_def = tDefine "sexp2tokens" `
  (sexp2tokens (Val n) b = [num2str n]) /\
  (sexp2tokens (Sym s) b = [s]) /\
  (sexp2tokens (Dot x y) b =
     if isQuote (Dot x y) /\ b then
       ["'"] ++ sexp2tokens (CAR y) T
     else if b then
       if y = Sym "nil" then ["("] ++ sexp2tokens x T ++ [")"] else
       if isDot y
         then ["("] ++ sexp2tokens x T ++ sexp2tokens y F ++ [")"]
         else ["("] ++ sexp2tokens x T ++ ["."] ++ sexp2tokens y F ++ [")"]
     else
       if y = Sym "nil" then sexp2tokens x T else
       if isDot y
         then sexp2tokens x T ++ sexp2tokens y F
         else sexp2tokens x T ++ ["."] ++ sexp2tokens y F)`
 (WF_REL_TAC `measure (LSIZE o FST)` \\ REWRITE_TAC [LSIZE_def,ADD1] \\ STRIP_TAC
  THEN1 (SIMP_TAC std_ss [isQuote_def,isDot_thm] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def,ADD1] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val sexp_parse_def = Define `
  (sexp_parse [] exp stack = exp) /\
  (sexp_parse (t::ts) exp stack =
    if t = ")" then sexp_parse ts (Sym "nil") (exp::stack) else
    if t = "." then sexp_parse ts (CAR exp) stack else
    if t = "(" then (if stack = [] then sexp_parse ts exp stack
                                   else sexp_parse ts (Dot exp (HD stack)) (TL stack)) else
    if t = "'" then (if isDot exp then sexp_parse ts (Dot (Dot (Sym "quote") (Dot (CAR exp) (Sym "nil"))) (CDR exp)) stack
                                  else sexp_parse ts exp stack) else
    if is_number_string t then sexp_parse ts (Dot (Val (str2num t)) exp) stack else
                               sexp_parse ts (Dot (Sym t) exp) stack)`;

val sexp_inject_def = Define `
  (sexp_inject (Val m) x = Dot (Val m) x) /\
  (sexp_inject (Sym s) x = Dot (Sym s) x) /\
  (sexp_inject (Dot t1 t2) x =
     if x = Sym "nil" then Dot t1 t2 else
     if t2 = Sym "nil" then Dot t1 x else Dot t1 (sexp_inject t2 x))`;

val parse_tac =
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [sexp2tokens_def,listTheory.REVERSE_SNOC_DEF,
                      rich_listTheory.SNOC_APPEND,APPEND,REVERSE_APPEND,
                      GSYM APPEND_ASSOC]
  \\ ASM_SIMP_TAC std_ss [sexp_parse_def] \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
  \\ SIMP_TAC std_ss [NOT_CONS_NIL,HD,TL,CAR_def]

val sexp_ok_def = Define `
  (sexp_ok (Val m) = m < 2**30) /\
  (sexp_ok (Sym s) = identifier_string s /\ ~(s = "")) /\
  (sexp_ok (Dot t1 t2) = sexp_ok t1 /\ sexp_ok t2)`;

val sexp_ok_Sym = prove(
  ``sexp_ok (Sym s) ==> ~(s = "(") /\ ~(s = ".") /\ ~(s = ")") /\
                        ~(s = "'") /\ ~(is_number_string s)``,
  FULL_SIMP_TAC std_ss [sexp_ok_def,identifier_string_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF,identifier_char_def,MEM,HD] \\ Cases_on `s`
  \\ FULL_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF,identifier_char_def,MEM,HD,is_number_string_def]);

val sexp_ok_Val = prove(
  ``sexp_ok (Val n) ==> is_number_string (num2str n)``,
  `number_char = \c. 48 <= ORD c /\ ORD c < 58` by SIMP_TAC std_ss [FUN_EQ_THM,number_char_def]
  \\ ASM_REWRITE_TAC [is_number_string_def,number_char_def,str2num_num2str]);

val is_number_string_IMP = prove(
  ``!s. is_number_string s ==> ~(s = ")") /\ ~(s = ".") /\ ~(s = "(") /\ ~(s = "'")``,
  Cases \\ SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11,is_number_string_def,EVERY_DEF,
     EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``,
     EXPLODE_def,number_char_def,GSYM ORD_11]
  \\ REPEAT STRIP_TAC \\ DISJ1_TAC \\ DECIDE_TAC);

val sexp_parse_lemma = prove(
  ``!exp b ys x stack.
      sexp_ok exp /\ (~b ==> (x = Sym "nil")) ==>
      (sexp_parse (REVERSE (sexp2tokens exp b) ++ ys) x stack =
       sexp_parse ys (if b then Dot exp x else sexp_inject exp x) stack)``,
  completeInduct_on `LSIZE exp` \\ REVERSE Cases
  THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC sexp_ok_Sym
    \\ SIMP_TAC std_ss [sexp2tokens_def,listTheory.REVERSE_SNOC_DEF,
                        rich_listTheory.SNOC_APPEND,APPEND]
    \\ Cases_on `b` \\ ASM_SIMP_TAC std_ss [sexp_parse_def] \\ SIMP_TAC std_ss [sexp_inject_def])
  THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC sexp_ok_Val \\ IMP_RES_TAC is_number_string_IMP
    \\ SIMP_TAC std_ss [sexp2tokens_def,listTheory.REVERSE_SNOC_DEF,
                        rich_listTheory.SNOC_APPEND,APPEND]
    \\ Cases_on `b` \\ ASM_SIMP_TAC std_ss [sexp_parse_def,str2num_num2str,sexp_inject_def])
  \\ Q.ABBREV_TAC `exp = S'` \\ Q.ABBREV_TAC `exp' = S0`
  \\ REPEAT (Q.PAT_X_ASSUM `Abbrev bbb` (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC
  \\ REWRITE_TAC [sexp2tokens_def]
  \\ Cases_on `isQuote (Dot exp exp') /\ b` \\ ASM_SIMP_TAC std_ss [] THEN1
   (REWRITE_TAC [REVERSE_APPEND,listTheory.REVERSE_SNOC_DEF,
                 rich_listTheory.SNOC_APPEND,APPEND,GSYM APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,sexp_ok_def]
    \\ REPEAT STRIP_TAC
    \\ `LSIZE y < LSIZE (Dot (Sym "quote") (Dot y (Sym "nil")))` by
           (FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!m.bbb` (ASSUME_TAC o UNDISCH o Q.SPEC `LSIZE y`)
    \\ Q.PAT_X_ASSUM `!exp.bbb` (ASSUME_TAC o UNDISCH o RW [] o Q.SPECL [`T`,`"'"::ys`,`x`,`stack`] o RW [] o Q.SPEC `y`)
    \\ ASM_REWRITE_TAC []
    \\ ONCE_REWRITE_TAC [sexp_parse_def]
    \\ REWRITE_TAC [EVAL ``"'" = ")"``,EVAL ``"'" = "("``,EVAL ``"'" = "."``,isDot_def]
    \\ SIMP_TAC std_ss [CAR_def,CDR_def])
  \\ Q.PAT_X_ASSUM `~bb` (K ALL_TAC)
  \\ REWRITE_TAC [sexp_ok_def]
  \\ REPEAT STRIP_TAC
  \\ `LSIZE exp < v /\ LSIZE exp' < v` by (FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
  \\ Q.PAT_X_ASSUM `!m.bbb` (fn th => ASSUME_TAC (Q.SPEC `exp` (UNDISCH (Q.SPEC `LSIZE exp` th))) THEN
                                    ASSUME_TAC (Q.SPEC `exp'` (UNDISCH (Q.SPEC `LSIZE exp'` th))))
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `sexp_ok _` (fn th => FULL_SIMP_TAC std_ss [th]))
  \\ Cases_on `b` THENL [
    Cases_on `exp' = Sym "nil"` \\ ASM_SIMP_TAC std_ss []
    THEN1 (`~isDot exp'` by ASM_SIMP_TAC std_ss [isDot_def]
      \\ REPEAT (Q.PAT_X_ASSUM `!x:bool. bbb` (ASSUME_TAC o RW[] o Q.SPEC `T`))  \\ parse_tac)
    \\ REVERSE (Cases_on `isDot exp'` \\ ASM_SIMP_TAC std_ss [])
     THEN1 (`sexp2tokens exp' F = sexp2tokens exp' T` by
           (Cases_on `exp'` \\ FULL_SIMP_TAC std_ss [isDot_def,sexp2tokens_def])
        \\ ASM_REWRITE_TAC []
        \\ REPEAT (Q.PAT_X_ASSUM `!x:bool. bbb` (ASSUME_TAC o RW[] o Q.SPEC `T`)) \\ parse_tac)
    \\ `~F ==> (Sym "nil" = Sym "nil")` by REWRITE_TAC []
    \\ RES_TAC \\ ASM_REWRITE_TAC []
    \\ REPEAT (Q.PAT_X_ASSUM `!x:bool. bbb` (ASSUME_TAC o RW[] o Q.SPEC `T`))
    \\ Cases_on `isQuote exp'` \\ parse_tac \\ parse_tac
    \\ Cases_on `exp'` \\ FULL_SIMP_TAC std_ss [isDot_def,sexp_inject_def,CAR_def],
    Cases_on `exp' = Sym "nil"` \\ ASM_SIMP_TAC std_ss []
    THEN1 (SIMP_TAC std_ss [sexp_inject_def] \\ METIS_TAC [])
    \\ REVERSE (Cases_on `isDot exp'`) \\ ASM_SIMP_TAC std_ss [isDot_def,CDR_def]
    THEN1 (REPEAT (Q.PAT_X_ASSUM `!x:bool. bbb` (ASSUME_TAC o RW[] o Q.SPEC `T`))
      \\ `sexp2tokens exp' F = sexp2tokens exp' T` by
           (Cases_on `exp'` \\ FULL_SIMP_TAC std_ss [isDot_def,sexp2tokens_def])
      \\ parse_tac \\ Cases_on `exp'`
      \\ FULL_SIMP_TAC std_ss [isDot_def,sexp_inject_def,CAR_def])
    \\ REPEAT STRIP_TAC
    \\ `~F ==> (x = Sym "nil")` by FULL_SIMP_TAC std_ss [isDot_def]
    \\ ASM_SIMP_TAC std_ss [] \\ RES_TAC
    \\ REPEAT (Q.PAT_X_ASSUM `!x:bool. bbb` (ASSUME_TAC o RW[] o Q.SPEC `T`))
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `x = Sym "nil"` (fn th => FULL_SIMP_TAC std_ss [th])
    \\ parse_tac \\ ASM_SIMP_TAC std_ss [sexp_inject_def]
    \\ Q.PAT_X_ASSUM `isDot exp'` ASSUME_TAC \\ NTAC 2 (FULL_SIMP_TAC std_ss [isDot_thm])
    \\ ASM_SIMP_TAC bool_ss [sexp_inject_def,CAR_def]]);

val string2sexp_def = Define `
  string2sexp s = CAR (sexp_parse (REVERSE (sexp_lex s)) (Sym "nil") [])`;

val EVERY_read_while = prove(
  ``!s t. EVERY P (EXPLODE s) ==> (read_while P s t = (STRCAT t s,""))``,
  Induct
  \\ ASM_SIMP_TAC std_ss [read_while_def,STRCAT_def,STRCAT_EQNS,EVERY_DEF,EXPLODE_def]
  \\ REWRITE_TAC [GSYM STRCAT_ASSOC] \\ REWRITE_TAC [STRCAT_def]);

val string_nil_or_not_def = Define `
  string_nil_or_not P s = ~(s = "") ==> ~P (HD (EXPLODE s))`;

val read_while_step = prove(
  ``!s t q. EVERY P (EXPLODE s) /\ string_nil_or_not P q ==>
            (read_while P (STRCAT s q) t = (STRCAT t s,q))``,
  Induct THENL [
    Cases_on `q` \\ SIMP_TAC std_ss [STRCAT_EQNS,read_while_def,
      string_nil_or_not_def,NOT_CONS_NIL,EXPLODE_def,HD],
    ASM_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF,STRCAT_EQNS,read_while_def]
    \\ REWRITE_TAC [GSYM STRCAT_ASSOC,STRCAT_EQNS]]);

val sexp2tokens_lemma = prove(
  ``!exp b t. sexp_ok exp /\ string_nil_or_not (\c. ~MEM c [#".";#"(";#")"] /\ ~space_char c) t ==>
              (sexp_lex (STRCAT (sexp2string_aux (exp,b)) t) = sexp2tokens exp b ++ sexp_lex t)``,
  completeInduct_on `LSIZE exp` \\ REVERSE Cases
  THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,sexp2tokens_def,sexp_lex_def]
    \\ Cases_on `s` \\ FULL_SIMP_TAC std_ss [sexp_lex_def,CONS_11,sexp_ok_def,STRCAT_EQNS]
    \\ FULL_SIMP_TAC std_ss [identifier_string_def,EVERY_DEF,EXPLODE_def,
         identifier_char_def,MEM,CONS_11,HD]
    \\ `string_nil_or_not identifier_char t` by
      (Cases_on `t` \\ FULL_SIMP_TAC std_ss [string_nil_or_not_def,NOT_CONS_NIL,
          EXPLODE_def,HD,identifier_char_def,MEM,CONS_11])
    \\ IMP_RES_TAC read_while_step
    \\ ASM_SIMP_TAC std_ss [LET_DEF,STRCAT_EQNS,APPEND])
  THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,sexp2tokens_def,sexp_lex_def]
    \\ IMP_RES_TAC sexp_ok_Val
    \\ Cases_on `num2str n` \\ FULL_SIMP_TAC std_ss [str2num_num2str,is_number_string_def]
    \\ FULL_SIMP_TAC std_ss [sexp_lex_def,EVERY_DEF,EXPLODE_def,STRCAT_EQNS]
    \\ `~space_char h /\ ~MEM h [#"("; #")"; #"."; #"'"]` by
     (FULL_SIMP_TAC std_ss [space_char_def,MEM,GSYM ORD_11,number_char_def,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``]
      \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ `string_nil_or_not number_char t` by
      (Cases_on `t` \\ FULL_SIMP_TAC std_ss [string_nil_or_not_def,NOT_CONS_NIL,
          EXPLODE_def,HD,identifier_char_def,MEM,CONS_11]
       \\ FULL_SIMP_TAC std_ss [space_char_def,number_char_def,
           EVAL ``ORD #"("``,EVAL ``ORD #")"``,EVAL ``ORD #"."``,EVAL ``ORD #"'"``]
       \\ DECIDE_TAC)
    \\ IMP_RES_TAC read_while_step
    \\ ASM_SIMP_TAC std_ss [LET_DEF,STRCAT_EQNS,APPEND])
  \\ REWRITE_TAC [ADD1,LSIZE_def,sexp_ok_def] \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `exp = S'` \\ Q.ABBREV_TAC `exp' = S0`
  \\ REPEAT (Q.PAT_X_ASSUM `Abbrev bbb` (K ALL_TAC))
  \\ SIMP_TAC std_ss [sexp2string_aux_def,sexp2tokens_def]
  \\ Cases_on `isQuote (Dot exp exp') /\ b` \\ ASM_REWRITE_TAC [] THEN1
   (SIMP_TAC std_ss [LIST_STRCAT_def,STRCAT_EQNS,APPEND,sexp_lex_def,MEM]
    \\ `~space_char #"'"` by EVAL_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [isQuote_def,isDot_def,CAR_def,CDR_def]
    \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,LSIZE_def,ADD1]
    \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,LSIZE_def,ADD1]
    \\ `LSIZE a < LSIZE a + LSIZE b' + 1 + 1` by DECIDE_TAC
    \\ RES_TAC \\ METIS_TAC [sexp_ok_def])
  \\ Q.PAT_X_ASSUM `~bbb` (K ALL_TAC)
  \\ `LSIZE exp < v /\ LSIZE exp' < v` by DECIDE_TAC
  \\ `!t. string_nil_or_not (\c. ~MEM c [#"."; #"("; #")"] /\ ~space_char c) t ==>
        (sexp_lex (STRCAT (sexp2string_aux (exp,T)) t) = sexp2tokens exp T ++ sexp_lex t)`
      by METIS_TAC []
  \\ `!t. string_nil_or_not (\c. ~MEM c [#"."; #"("; #")"] /\ ~space_char c) t ==>
        (sexp_lex (STRCAT (sexp2string_aux (exp',F)) t) = sexp2tokens exp' F ++ sexp_lex t)`
      by METIS_TAC []
  \\ Q.PAT_X_ASSUM `!m. m < v ==> fgh` (K ALL_TAC)
  \\ `~(space_char #".") /\ ~(space_char #"(") /\ ~(space_char #")") /\ space_char #" "` by EVAL_TAC
  \\ Q.ABBREV_TAC `g = (\c. ~MEM c [#"."; #"("; #")"] /\ ~space_char c)`
  \\ Cases_on `b` \\ ASM_SIMP_TAC std_ss [LIST_STRCAT_def,STRCAT_EQNS,LET_DEF] THENL [
    Cases_on `exp' = Sym "nil"` \\ ASM_SIMP_TAC std_ss [] THENL [
      ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def,MEM,APPEND,CONS_11]
      \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
      \\ `string_nil_or_not g (STRCAT ")" t)` by
        (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,EXPLODE_def,HD,MEM])
      \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def,MEM,GSYM APPEND_ASSOC,APPEND],
      Cases_on `isDot exp'` \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS] THENL [
        ASM_SIMP_TAC std_ss [sexp_lex_def,MEM,APPEND,CONS_11]
        \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
        \\ `string_nil_or_not g (STRCAT (STRING #" " (STRCAT (sexp2string_aux (exp',F)) ")")) t)` by
          (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,
             EXPLODE_def,HD,MEM,EVAL ``space_char #" "``])
        \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def]
        \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
        \\ `string_nil_or_not g (STRCAT ")" t)` by
          (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,EXPLODE_def,HD,MEM])
        \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def,MEM,GSYM APPEND_ASSOC,APPEND],
        ASM_SIMP_TAC std_ss [sexp_lex_def,MEM,APPEND,CONS_11]
        \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
        \\ `string_nil_or_not g (STRCAT (STRING #" "
             (STRING #"." (STRING #" " (STRCAT (sexp2string_aux (exp',F)) ")")))) t)` by
          (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,
             EXPLODE_def,HD,MEM,EVAL ``space_char #" "``])
        \\ RES_TAC \\ ASM_SIMP_TAC std_ss [sexp_lex_def]
        \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def,MEM]
        \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
        \\ `string_nil_or_not g (STRCAT ")" t)` by
          (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,EXPLODE_def,HD,MEM])
        \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def,MEM,GSYM APPEND_ASSOC,APPEND]]],
    Cases_on `exp' = Sym "nil"` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `isDot exp'` \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS] THENL [
      ASM_SIMP_TAC std_ss [sexp_lex_def,MEM,APPEND,CONS_11]
      \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
      \\ `string_nil_or_not g (STRCAT (STRING #" " (sexp2string_aux (exp',F))) t)` by
        (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,
           EXPLODE_def,HD,MEM,EVAL ``space_char #" "``])
      \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def]
      \\ REWRITE_TAC [GSYM STRCAT_ASSOC,APPEND_ASSOC],
      ASM_SIMP_TAC std_ss [sexp_lex_def,MEM,APPEND,CONS_11]
      \\ REWRITE_TAC [GSYM STRCAT_ASSOC]
      \\ `string_nil_or_not g (STRCAT (STRING #" "
           (STRING #"." (STRING #" " ((sexp2string_aux (exp',F)))))) t)` by
        (Q.UNABBREV_TAC `g` \\ SIMP_TAC std_ss [STRCAT_EQNS,string_nil_or_not_def,
           EXPLODE_def,HD,MEM,EVAL ``space_char #" "``])
      \\ RES_TAC \\ ASM_SIMP_TAC std_ss [sexp_lex_def]
      \\ ASM_SIMP_TAC std_ss [STRCAT_EQNS,sexp_lex_def,MEM]
      \\ REWRITE_TAC [GSYM STRCAT_ASSOC,GSYM APPEND_ASSOC,APPEND]]]);

val sexp_lex_sexp2str =
  (RW [string_nil_or_not_def,sexp_lex_def,APPEND_NIL,STRCAT_EQNS] o
   Q.SPECL [`exp`,`T`,`""`]) sexp2tokens_lemma;

val string2sexp_sexp2string = store_thm("string2sexp_sexp2string",
  ``!x. sexp_ok x ==> (string2sexp (sexp2string x) = x)``,
  REWRITE_TAC [string2sexp_def,sexp2string_def]
  \\ SIMP_TAC std_ss [sexp_lex_sexp2str,
       RW [APPEND_NIL] (Q.SPECL [`x`,`T`,`[]`] sexp_parse_lemma)]
  \\ SIMP_TAC std_ss [sexp_parse_def,CAR_def]);


(* PARSER IMPLEMENTATION *)

val (th,arm_parse1_def,arm_parse1_pre_def) = compile_all ``
  arm_parse1 (r4:word32,r7:word32,r8:word32,dh:word32 set,h:word32->word32) =
    let h = (r4 =+ r7) h in
    let h = (r4 + 0x4w =+ r8) h in
    let r7 = 0x3w in
    let r8 = r4 in
      (r4:word32,r7:word32,r8:word32,dh,h)``

val (th,arm_parse2_def,arm_parse2_pre_def) = compile_all ``
  arm_parse2 (r4:word32,r6:word32,r7:word32,r8,dh:word32 set,h:word32->word32) =
    if r8 && 0x3w = 0x0w then
      (let r6 = h r8 in
       let h = (r4 =+ r7) h in
       let r7 = r8 in
       let h = (r4 + 4w =+ r6) h in
       let r8 = h (r8 + 0x4w) in
       let r6 = 3w in
       let h = (r7 =+ r6) h in
       let h = (r7 + 0x4w =+ r6) h in
       let r7 = r4 in
         (r4,r6,r7,r8,dh,h))
    else
      (let r6 = 3w in
       let h = (r4 =+ r6) h in
       let h = (r4 + 0x4w =+ r6) h in
         (r4,r6,r7,r8,dh,h))``

val (th,arm_parse3_def,arm_parse3_pre_def) = compile_all ``
  arm_parse3 (r4:word32,r7:word32,dh:word32 set,h:word32->word32) =
    (if r7 && 3w = 0x0w then
       (let r6 = r7 in
        let r7 = h r7 in
        let r3 = 3w in
        let h = (r6 =+ r3) h in
        let r6 = 0x3w in
        let h = (r4 =+ r6) h in
        let h = (r4 + 0x4w =+ r6) h in
          (r4,r6,r7,dh,h))
     else
       (let r6 = 0x3w in
        let h = (r4 =+ r6) h in
        let h = (r4 + 0x4w =+ r6) h in
          (r4,r6,r7,dh,h)))``

val (th,arm_parse4_def,arm_parse4_pre_def) = compile_all ``
  arm_parse4 (r4:word32,r5:word32,r7:word32,dh:word32 set,h:word32->word32) =
    if r7 && 3w = 0x0w then
      (let r6 = h r7 in
       let h = (r5 + 0x8w =+ r6) h in
       let r5 = r5 + 0x8w in
       let r6 = 0x3w in
       let h = (r5 + 0x4w =+ r6) h in
       let r6 = 0x1Bw in
       let h = (r4 + 0x4w =+ r5) h in
       let h = (r4 =+ r6) h in
       let h = (r7 =+ r4) h in
         (r4,r5,r6,r7,dh,h))
    else
      (let r6 = 0x3w:word32 in
       let h = (r5 + 0x8w =+ r6) h in
       let r5 = r5 + 0x8w in
       let h = (r5 + 0x4w =+ r6) h in
       let h = (r4 =+ r6) h in
       let h = (r4 + 0x4w =+ r6) h in
         (r4,r5,r6,r7,dh,h))``;

val (th,arm_parse_next_def,arm_parse_next_pre_def) = compile_all ``
  arm_parse_next (r4,r5,r6,r7,r8,dh,h) =
    if r6 && 3w = 0x0w then
      if r6 = 0x8w then
        (let (r4,r7,r8,dh,h) = arm_parse1 (r4,r7,r8,dh,h)
         in (r4,r5,r6,r7,r8,dh,h))
      else
        if r6 = 0x4w then
          (let (r4,r6,r7,r8,dh,h) = arm_parse2 (r4,r6,r7,r8,dh,h)
           in (r4,r5,r6,r7,r8,dh,h))
        else
          if r6 = 0xCw then
            (let (r4,r6,r7,dh,h) = arm_parse3 (r4,r7,dh,h)
             in (r4,r5,r6,r7,r8,dh,h))
          else
            (let (r4,r5,r6,r7,dh,h) = arm_parse4 (r4,r5,r7,dh,h)
             in (r4,r5,r6,r7,r8,dh,h))
    else
      (let h = (r4 + 0x4w =+ r7) h in
       let r7 = r4 in
         (r4,r5,r6,r7,r8,dh,h))``

val (th,arm_parse_loop_def,arm_parse_loop_pre_def) = compile_all ``
  arm_parse_loop1 (r4,r5,r6,r7,r8,dh:word32 set,h:word32->word32) =
    if r6 = 40w then
      if r7 && 3w = 0w then
        let r6 = 3w in
        let r8 = r7 in
        let r7 = h r7 in
        let h = (r8 =+ r6) h in
          (r4,r5,r6,r7,r8,dh,h)
      else
        (r4,r5,r6,r7,r8,dh,h)
    else
      let (r4,r5,r6,r7,r8,dh,h) = arm_parse_next (r4,r5,r6,r7,r8,dh,h) in
      let r6 = h (r4 - 0x8w) in
      let r4 = r4 - 0x8w in
        arm_parse_loop1 (r4,r5,r6,r7,r8,dh,h)``;

val sexp_list_def = Define `
  (sexp_list [] = Sym "nil") /\
  (sexp_list (x::xs) = Dot x (sexp_list xs))`;

val add_set_def = Define `add_set x s (i,j) = (x + i,j) IN s`;

val SPLIT_thm = prove(
  ``!x y z. SPLIT x (y,z) = (y = x DIFF z) /\ z SUBSET x``,
  FULL_SIMP_TAC std_ss [set_sepTheory.SPLIT_def,EXTENSION,IN_DELETE,
    IN_DIFF,IN_UNION,DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,SUBSET_DEF]
  \\ METIS_TAC []);

val SPLIT_DISJOINT_DISJOINT = prove(
  ``SPLIT (x DELETE t1 DELETE t2) (y,z) /\ DISJOINT i x ==> DISJOINT i y``,
  FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER,IN_UNION,SPLIT_thm,IN_DELETE,SUBSET_DEF,IN_DELETE,IN_DIFF] \\ METIS_TAC []);

val SET_TAC =
  FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER,
    IN_UNION,IN_INSERT,IN_DELETE,IN_DIFF,SUBSET_DEF,set_sepTheory.SPLIT_def] \\ METIS_TAC []

val arm_tokens2_def = Define `
  (arm_tokens2 a [] b x y = cond (a = y)) /\
  (arm_tokens2 a (str::xs) b x y =
     SEP_EXISTS w1:word32 w2:word32. one (a,w1) * one (a+4w,w2) *
                       cond (arm_token w1 str b x) *
                       arm_tokens2 (a - 8w:word32) xs b x y)`;

val arm_tokens2_SNOC = prove(
  ``!xs a b x w. arm_tokens2 a (xs ++ [h]) b x w =
                 arm_tokens2 a xs b x (w + 8w) * arm_tokens2 (w + 8w) [h] b x w``,
  Induct THENL [
    REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [arm_tokens2_def,APPEND]
    \\ REWRITE_TAC [WORD_EQ_SUB_RADD]
    \\ Cases_on `a = w + 8w` \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES],
    ASM_REWRITE_TAC [APPEND,arm_tokens2_def,WORD_ADD_SUB]
    \\ SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++star_ss) []]);

val arm_tokens_EQ_arm_tokens2 = prove(
  ``!xs a b x y. arm_tokens a xs b x y = arm_tokens2 (y - 8w) (REVERSE xs) b x (a - 8w)``,
  Induct
  \\ REWRITE_TAC [arm_tokens2_def,arm_tokens_def,REVERSE_DEF]
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [WORD_LCANCEL_SUB]
  THEN1 (Cases_on `a = y` \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_REWRITE_TAC [arm_tokens2_SNOC,WORD_SUB_ADD,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [SEP_CLAUSES,arm_tokens2_def]
  \\ SIMP_TAC (std_ss++star_ss) []);

val arm_tokens4_def = Define `
  arm_tokens4 a xs b x y =
    arm_tokens2 a xs b x y * one (y,40w) * SEP_EXISTS w. one (y+4w,w)`;

val arm_tokens4_thm = prove(
  ``arm_tokens4 a (str::xs) b x y =
    arm_tokens2 a [str] b x (a - 8w) * arm_tokens4 (a - 8w) xs b x y``,
  REWRITE_TAC [arm_tokens4_def,arm_tokens2_def]
  \\ REWRITE_TAC [STAR_ASSOC]
  \\ SIMP_TAC std_ss [SEP_CLAUSES]);

val arm_tokens3_def = Define `
  (arm_tokens3 a [] q = cond (a = q)) /\
  (arm_tokens3 a (str::xs) q =
     if str = "'" then SEP_EXISTS w3:word32 w4.
                       one (a,w3) * one (a+4w,w4) * arm_tokens3 (a + 8w) xs q
     else arm_tokens3 a xs q)`;

val lisp_exp_def = Define `
  (lisp_exp (Sym s) a (b,d) = cond (ALIGNED (a - 3w) /\ (b + a - 3w:word32,s) IN d)) /\
  (lisp_exp (Val n) a (b,d) = cond (a = ADDR32 (n2w n) + 2w)) /\
  (lisp_exp (Dot x y) a (b,d) = cond (ALIGNED a /\ (w2n (b - a) MOD 8 = 0)) *
    SEP_EXISTS a1 a2. one (a,a1) * one (a+4w,a2) * lisp_exp x a1 (b,d) * lisp_exp y a2 (b,d))`;

val SEP_EXPS_def = Define `
  (SEP_EXPS [] (b,d) = emp) /\
  (SEP_EXPS ((a,x)::xs) (b,d) = lisp_exp x a (b,d) * SEP_EXPS xs (b,d))`;

val SEP_FILL_def = Define `SEP_FILL (b,d) = SEP_EXISTS xs. SEP_EXPS xs (b,d)`;

val lisp_exp_FILL = prove(
  ``!exp exp2 a a2 b d a.
      (lisp_exp exp a (b,d) * lisp_exp exp2 a2 (b,d) * SEP_FILL (b,d)) s ==>
      (lisp_exp exp a (b,d) * SEP_FILL (b,d)) s``,
  SIMP_TAC std_ss [SEP_FILL_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `(a2,exp2)::y`
  \\ ASM_REWRITE_TAC [SEP_EXPS_def,STAR_ASSOC]);

val LENGTH_LEMMA1 = prove(
  ``(0x8w + r4 - n2w (8 * LENGTH (x::xs)) = r4 - n2w (8 * LENGTH xs)) /\
    (r4 + 0x8w - n2w (8 * LENGTH (x::xs)) = r4 - n2w (8 * LENGTH xs))``,
  REWRITE_TAC [LENGTH,MULT_CLAUSES,GSYM word_add_n2w]
  \\ REWRITE_TAC [WORD_SUB_PLUS,WORD_ADD_SUB]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [WORD_SUB_PLUS,WORD_ADD_SUB]);

val WORD_EQ_SUB_CANCEL = prove(
  ``!x:'a word y. (x - y = x) = (y = 0w)``,
  METIS_TAC [WORD_RCANCEL_SUB,WORD_SUB_RZERO])

val LENGTH_LEMMA2 = prove(
  ``LENGTH (x::xs) <= 536870912 ==>
    ((n2w (8 * LENGTH xs) = 0w:word32) = (xs = [])) /\
    LENGTH xs <= 536870912``,
  SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LENGTH]
  \\ REPEAT STRIP_TAC
  \\ `8 * LENGTH xs < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_NIL] \\ DECIDE_TAC);

val ALIGNED8_def = Define `
  ALIGNED8 x = (w2n x MOD 8 = 0)`;

val ALIGNED8_LEMMA = prove(
  ``!x:word32. ALIGNED8 (x + 0x8w) = ALIGNED8 x``,
  REWRITE_TAC [ALIGNED8_def]
  \\ Cases \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,w2n_n2w]
  \\ REWRITE_TAC [GSYM (EVAL ``8 * 536870912``)]
  \\ SIMP_TAC bool_ss [MOD_MULT_MOD,DECIDE ``0<8:num /\ 0<536870912:num``]
  \\ SIMP_TAC std_ss [ADD_MODULUS]);

val ALIGNED8_STEP = prove(
  ``!a:word32 b.
      (ALIGNED8 (b - (a - 0x8w)) = ALIGNED8 (b - a)) /\
      (ALIGNED8 (b - (a + 0x8w)) = ALIGNED8 (b - a))``,
  NTAC 2 STRIP_TAC
  \\ SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_SUB_SUB,WORD_ADD_SUB_SYM]
  \\ SIMP_TAC std_ss [ALIGNED8_LEMMA]
  \\ SIMP_TAC std_ss [GSYM (RW [WORD_SUB_ADD] (Q.SPEC `x - 8w` ALIGNED8_LEMMA))]);

val arm_parse_lemma = prove(
  ``!xs r4 r5 r7 r8 df f d1 d2 d3 exp stack p.
      ALIGNED8 (b - r4) /\ ALIGNED8 (b - r5) /\ ALIGNED b /\
      (ALIGNED r8 ==> ALIGNED8 (b - r8)) /\
      (ALIGNED r7 ==> ALIGNED8 (b - r7)) /\
      (arm_tokens4 r4 xs b d y * arm_tokens3 (r5 + 8w) xs q * lisp_exp exp r7 (b,d) *
       lisp_exp (sexp_list stack) r8 (b,d) * SEP_FILL (b,d) * p) (fun2set (f,df)) /\
      (b + 0x18w,"quote") IN d /\ (b,"nil") IN d /\
      ALIGNED r4 /\ ALIGNED r5 ==>
      ?r4i r5i r6i r7i r8i fi.
        arm_parse_loop1_pre (r4,r5,f r4,r7,r8,df,f) /\
        (arm_parse_loop1(r4,r5,f r4,r7,r8,df,f) = (y,q - 8w,r6i,r7i,r8i,df,fi)) /\
        (arm_tokens4 y [] b d y * lisp_exp (CAR (sexp_parse xs exp stack)) r7i (b,d) * SEP_FILL (b,d) * p) (fun2set (fi,df)) /\
        r4 IN df``,
  Induct THEN1
   (REWRITE_TAC [sexp_parse_def,arm_tokens4_def,arm_tokens2_def]
    \\ ONCE_REWRITE_TAC [arm_parse_loop_pre_def,arm_parse_loop_def]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REPEAT STRIP_TAC
    \\ `(f y = 0x28w) /\ y IN df` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,SEP_FILL_def]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ REWRITE_TAC [ALIGNED_INTRO]
    \\ `ALIGNED r7 = isDot exp` by
     (Cases_on `exp`
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [lisp_exp_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,isDot_def]
      \\ METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32,WORD_SUB_ADD])
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ REVERSE (Cases_on `isDot exp`)
    THEN1
     (`CAR exp = exp` by (Cases_on `exp` \\ FULL_SIMP_TAC std_ss [CAR_def,isDot_def])
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES]
      \\ ASM_SIMP_TAC std_ss [WORD_EQ_SUB_LADD]
      \\ Q.EXISTS_TAC `(r8,sexp_list stack)::y'`
      \\ Q.EXISTS_TAC `y''`
      \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES])
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_exp_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_exp_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [CAR_def,STAR_ASSOC,SEP_EXISTS]
    \\ `(f r7 = y''') /\ r7 IN df` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES]
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_SUB_LADD]
    \\ Q.EXISTS_TAC `(r7,Dot (Sym "nil") b')::(r8,sexp_list stack)::y'`
    \\ Q.EXISTS_TAC `y''`
    \\ SIMP_TAC std_ss [SEP_EXPS_def,lisp_exp_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `3w`
    \\ Q.EXISTS_TAC `y''''`
    \\ ASM_SIMP_TAC std_ss [WORD_SUB_REFL,ALIGNED_n2w,WORD_ADD_SUB,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [arm_tokens3_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_EXPS_def,arm_tokens3_def,SEP_CLAUSES]
    \\ SEP_WRITE_TAC)
  \\ SIMP_TAC std_ss [arm_tokens4_thm,arm_tokens2_def,SEP_CLAUSES]
  \\ REWRITE_TAC [STAR_ASSOC]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ REPEAT STRIP_TAC
  \\ `ALIGNED (r4 - 8w) /\ ALIGNED (r5 + 8w)` by ALIGNED_TAC
  \\ `(f r4 = y') /\ r4 IN df` by SEP_READ_TAC
  \\ Cases_on `h = "'"` THEN1
   (FULL_SIMP_TAC std_ss [arm_tokens3_def,sexp_parse_def,SEP_CLAUSES]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `arm_token y' ccc b x` MP_TAC
    \\ FULL_SIMP_TAC std_ss [arm_token_def]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [arm_parse_loop_def,arm_parse_loop_pre_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,arm_parse_next_def,arm_parse_next_pre_def]
    \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w]
    \\ SIMP_TAC std_ss [LET_DEF,arm_parse4_pre_def,arm_parse4_def,ALIGNED_INTRO]
    \\ `ALIGNED r7 = isDot exp` by
     (Cases_on `exp`
      \\ FULL_SIMP_TAC std_ss [lisp_exp_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_EXISTS,cond_STAR,isDot_def]
      \\ METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32,WORD_SUB_ADD])
    \\ SIMP_TAC std_ss [word_arith_lemma1]
    \\ REVERSE (Cases_on `isDot exp` \\ ASM_SIMP_TAC std_ss [])
    THEN1
     (Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ 0x3w)
        ((r4 =+ 0x3w) ((r5 + 0xCw =+ 0x3w) ((r5 + 0x8w =+ 0x3w) f)))`
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
      \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 ((r5 + 8w) + 0x8w) xs q *
           lisp_exp exp r7 (b,d) * lisp_exp (sexp_list stack) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by
      (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5 + 8w`,`r7`,`r8`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP] \\ STRIP_TAC
        \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
        \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
      \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
      \\ Q.UNABBREV_TAC `f2`
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_FILL_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `(r4,Dot (Sym "nil") (Sym "nil"))::(r5+8w,Dot (Sym "nil") (Sym "nil"))::y'''''`
      \\ SIMP_TAC std_ss [SEP_EXPS_def,lisp_exp_def]
      \\ SIMP_TAC std_ss [SEP_CLAUSES]
      \\ SIMP_TAC std_ss [SEP_EXISTS]
      \\ REPEAT (Q.EXISTS_TAC `3w`)
      \\ ASM_SIMP_TAC std_ss [WORD_SUB_REFL,ALIGNED_n2w,WORD_ADD_SUB,SEP_CLAUSES]
      \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
      \\ ASM_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP]
      \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,SEP_CLAUSES,STAR_ASSOC,word_arith_lemma1]
      \\ SEP_WRITE_TAC)
    THEN
     (Q.ABBREV_TAC `f2 = (r7 =+ r4) ((r4 =+ 0x1Bw) ((r4 + 0x4w =+ r5 + 0x8w)
              ((r5 + 0xCw =+ 0x3w) ((r5 + 0x8w =+ f r7) f))))`
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
      \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 ((r5 + 8w) + 0x8w) xs q *
           lisp_exp (Dot (Dot (Sym "quote") (Dot (CAR exp) (Sym "nil"))) (CDR exp))
                     r7 (b,d) * lisp_exp (sexp_list stack) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5 + 8w`,`r7`,`r8`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP] \\ STRIP_TAC
        \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
        \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ ALIGNED_TAC \\ ASM_SIMP_TAC std_ss []
        \\ Q.PAT_X_ASSUM `isDot xxxxx` MP_TAC \\ STRIP_TAC
        \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_exp_def]
        \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
        \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
        \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
        \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
        \\ ASM_SIMP_TAC std_ss [] \\ SEP_READ_TAC)
      \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
      \\ Q.UNABBREV_TAC `f2`
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_FILL_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `y'''''`
      \\ SIMP_TAC std_ss [lisp_exp_def]
      \\ SIMP_TAC std_ss [SEP_CLAUSES]
      \\ SIMP_TAC std_ss [SEP_EXISTS]
      \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_exp_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_exp_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.ABBREV_TAC `y2 = y''`
      \\ Q.ABBREV_TAC `y3 = y'''`
      \\ Q.ABBREV_TAC `y4 = y''''`
      \\ Q.ABBREV_TAC `y5 = y'''''`
      \\ Q.ABBREV_TAC `y6 = y''''''`
      \\ Q.ABBREV_TAC `y7 = y'''''''`
      \\ NTAC 6 (POP_ASSUM (K ALL_TAC))
      \\ Q.EXISTS_TAC `r4`
      \\ Q.EXISTS_TAC `y7`
      \\ Q.EXISTS_TAC `0x1Bw`
      \\ Q.EXISTS_TAC `r5 + 8w`
      \\ Q.EXISTS_TAC `y6`
      \\ Q.EXISTS_TAC `3w`
      \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma2,ALIGNED_n2w]
      \\ ASM_SIMP_TAC std_ss [word_arith_lemma4,word_arith_lemma3,WORD_ADD_0]
      \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
      \\ Q.PAT_X_ASSUM `bbb (fun2set (f,df))` MP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
      \\ STRIP_TAC
      \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,SEP_CLAUSES,STAR_ASSOC,CAR_def,CDR_def]
      \\ `f r7 = y6` by SEP_READ_TAC
      \\ ASM_SIMP_TAC std_ss []
      \\ SEP_WRITE_TAC))
  \\ Cases_on `h = ")"` THEN1
   (FULL_SIMP_TAC std_ss [arm_tokens3_def,sexp_parse_def,SEP_CLAUSES]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `arm_token y' ccc b x` MP_TAC
    \\ FULL_SIMP_TAC std_ss [arm_token_def]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [arm_parse_loop_def,arm_parse_loop_pre_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,arm_parse_next_def,arm_parse_next_pre_def]
    \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w]
    \\ SIMP_TAC std_ss [LET_DEF,arm_parse1_def,arm_parse1_pre_def,ALIGNED_INTRO]
    \\ Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ r8) ((r4 =+ r7) f)`
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
    \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp (Sym "nil") 3w (b,d) *
           lisp_exp (sexp_list (exp::stack)) r4 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`3w`,`r4`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
        \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
        \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
    \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
    \\ Q.UNABBREV_TAC `f2`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_CLAUSES]
    \\ ASM_SIMP_TAC std_ss [sexp_list_def,lisp_exp_def,SEP_CLAUSES,WORD_SUB_REFL,
          ALIGNED_n2w,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `r7`
    \\ Q.EXISTS_TAC `r8`
    \\ SEP_WRITE_TAC)
  \\ Cases_on `h = "("` THEN1
   (FULL_SIMP_TAC std_ss [arm_tokens3_def,sexp_parse_def,SEP_CLAUSES]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `arm_token y' ccc b x` MP_TAC
    \\ FULL_SIMP_TAC std_ss [arm_token_def]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [arm_parse_loop_def,arm_parse_loop_pre_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,arm_parse_next_def,arm_parse_next_pre_def]
    \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w]
    \\ SIMP_TAC std_ss [LET_DEF,arm_parse2_def,arm_parse2_pre_def,ALIGNED_INTRO]
    \\ `ALIGNED r8 = (stack <> [])` by
     (Cases_on `stack`
      \\ FULL_SIMP_TAC std_ss [lisp_exp_def,SEP_CLAUSES,sexp_list_def]
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_EXISTS,cond_STAR,isDot_def,NOT_CONS_NIL]
      \\ METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32,WORD_SUB_ADD])
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,NOT_IF]
    \\ REVERSE (Cases_on `stack` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL])
    THEN1
     (Q.ABBREV_TAC `f2 = (r8 + 0x4w =+ 0x3w)
        ((r8 =+ 0x3w) ((r4 + 0x4w =+ f r8) ((r4 =+ r7) f)))`
      \\ FULL_SIMP_TAC std_ss [sexp_list_def,lisp_exp_def,NOT_CONS_NIL,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.PAT_X_ASSUM `ALIGNED8 (b - r8)` ASSUME_TAC
      \\ `(r4 + 0x4w =+ f r8) ((r4 =+ r7) f) (r8 + 0x4w) = y''''` by
       (`r4 + 0x4w <> r8 + 0x4w` by SEP_NEQ_TAC
        \\ `r8 + 0x4w <> r4` by SEP_NEQ_TAC
        \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]
        \\ SEP_READ_TAC)
      \\ ASM_SIMP_TAC std_ss [HD,TL]
      \\ POP_ASSUM (K ALL_TAC)
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
      \\ `(ALIGNED y'''' ==> ALIGNED8 (b - y''''))` by
       (STRIP_TAC \\ REVERSE (Cases_on `t`)
        \\ FULL_SIMP_TAC std_ss [lisp_exp_def,SEP_CLAUSES,sexp_list_def]
        \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [GSYM ALIGNED8_def,
              cond_STAR,SEP_EXISTS]
        \\ IMP_RES_TAC NOT_ALIGNED \\ METIS_TAC [WORD_SUB_ADD])
      \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp (Dot exp h') r4 (b,d) * lisp_exp (sexp_list t) y'''' (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`r4`,`y''''`])
          \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
          \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
          \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
          \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
      \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
      \\ Q.UNABBREV_TAC `f2`
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_CLAUSES,SEP_FILL_def]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `(r8,Dot (Sym "nil") (Sym "nil"))::y'''''`
      \\ SIMP_TAC std_ss [SEP_EXPS_def,lisp_exp_def]
      \\ SIMP_TAC std_ss [SEP_CLAUSES]
      \\ SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `r7`
      \\ Q.EXISTS_TAC `y'''`
      \\ Q.EXISTS_TAC `3w`
      \\ Q.EXISTS_TAC `3w`
      \\ ASM_SIMP_TAC std_ss [WORD_SUB_REFL,ALIGNED_n2w,WORD_ADD_SUB,SEP_CLAUSES]
      \\ `f r8 = y'''` by SEP_READ_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
      \\ ASM_SIMP_TAC std_ss [STAR_ASSOC]
      \\ SEP_WRITE_TAC)
    THEN
     (Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ 0x3w) ((r4 =+ 0x3w) f)`
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
      \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp exp r7 (b,d) * lisp_exp (sexp_list []) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`r7`,`r8`])
         \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
         \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
         \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
         \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
      \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
      \\ Q.UNABBREV_TAC `f2`
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_CLAUSES,SEP_FILL_def]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `(r4,Dot (Sym "nil") (Sym "nil"))::y'''`
      \\ SIMP_TAC std_ss [SEP_EXPS_def,lisp_exp_def]
      \\ SIMP_TAC std_ss [SEP_CLAUSES]
      \\ SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `3w`
      \\ Q.EXISTS_TAC `3w`
      \\ ASM_SIMP_TAC std_ss [WORD_SUB_REFL,ALIGNED_n2w,WORD_ADD_SUB,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
      \\ SEP_WRITE_TAC))
  \\ Cases_on `h = "."` THEN1
   (FULL_SIMP_TAC std_ss [arm_tokens3_def,sexp_parse_def,SEP_CLAUSES]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `arm_token y' ccc b x` MP_TAC
    \\ FULL_SIMP_TAC std_ss [arm_token_def]
    \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    \\ SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [arm_parse_loop_def,arm_parse_loop_pre_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,arm_parse_next_def,arm_parse_next_pre_def]
    \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w]
    \\ SIMP_TAC std_ss [LET_DEF,arm_parse3_def,arm_parse3_pre_def,ALIGNED_INTRO]
    \\ `ALIGNED r7 = isDot exp` by
     (Cases_on `exp`
      \\ FULL_SIMP_TAC std_ss [lisp_exp_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_EXISTS,cond_STAR,isDot_def]
      \\ METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32,WORD_SUB_ADD])
    \\ SIMP_TAC std_ss [word_arith_lemma1]
    \\ REVERSE (Cases_on `isDot exp` \\ ASM_SIMP_TAC std_ss [])
    THEN1
     (Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ 0x3w) ((r4 =+ 0x3w) f)`
      \\ `CAR exp = exp` by
        (Cases_on `exp` \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def])
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
      \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp exp r7 (b,d) * lisp_exp (sexp_list stack) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`r7`,`r8`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
        \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
        \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
      \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
      \\ Q.UNABBREV_TAC `f2`
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_FILL_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `(r4,Dot (Sym "nil") (Sym "nil"))::y'''`
      \\ SIMP_TAC std_ss [SEP_EXPS_def,lisp_exp_def]
      \\ SIMP_TAC std_ss [SEP_CLAUSES]
      \\ SIMP_TAC std_ss [SEP_EXISTS]
      \\ REPEAT (Q.EXISTS_TAC `3w`)
      \\ ASM_SIMP_TAC std_ss [WORD_SUB_REFL,ALIGNED_n2w,WORD_ADD_SUB,SEP_CLAUSES]
      \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
      \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,SEP_CLAUSES,STAR_ASSOC,word_arith_lemma1]
      \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
      \\ SEP_WRITE_TAC)
    THEN
     (FULL_SIMP_TAC std_ss [isDot_thm,CAR_def]
      \\ Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ 0x3w) ((r4 =+ 0x3w) ((r7 =+ 3w) f))`
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1,STAR_ASSOC]
      \\ FULL_SIMP_TAC std_ss [lisp_exp_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
      \\ `f r7 = y'''` by SEP_READ_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `(ALIGNED y''' ==> ALIGNED8 (b - y'''))` by
       (STRIP_TAC \\ REVERSE (Cases_on `a`)
        \\ FULL_SIMP_TAC std_ss [lisp_exp_def,SEP_CLAUSES,sexp_list_def]
        \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [GSYM ALIGNED8_def,
              cond_STAR,SEP_EXISTS]
        THEN1 (IMP_RES_TAC NOT_ALIGNED \\ METIS_TAC [WORD_SUB_ADD])
        \\ POP_ASSUM MP_TAC
        \\ ASM_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w])
      \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp a y''' (b,d) * lisp_exp (sexp_list stack) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`y'''`,`r8`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
        \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
        \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
      \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
      \\ Q.UNABBREV_TAC `f2`
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_CLAUSES,SEP_FILL_def]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `(r4,Dot (Sym "nil") (Sym "nil"))::(r7,Dot (Sym "nil") b')::y'''''`
      \\ SIMP_TAC std_ss [SEP_EXPS_def,lisp_exp_def]
      \\ SIMP_TAC std_ss [SEP_CLAUSES]
      \\ SIMP_TAC std_ss [SEP_EXISTS]
      \\ Q.EXISTS_TAC `3w`
      \\ Q.EXISTS_TAC `3w`
      \\ Q.EXISTS_TAC `3w`
      \\ Q.EXISTS_TAC `y''''`
      \\ ASM_SIMP_TAC std_ss [WORD_SUB_REFL,ALIGNED_n2w,WORD_ADD_SUB,SEP_CLAUSES]
      \\ ASM_SIMP_TAC std_ss [STAR_ASSOC]
      \\ Q.PAT_X_ASSUM `ALIGNED8 (b - r7)` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
      \\ SEP_WRITE_TAC))
  \\ Cases_on `is_number_string h` THEN1
   (FULL_SIMP_TAC std_ss [arm_tokens3_def,sexp_parse_def,SEP_CLAUSES]
    \\ Q.PAT_X_ASSUM `arm_token y' ccc b x` MP_TAC
    \\ FULL_SIMP_TAC std_ss [arm_token_def,GSYM is_number_string_def]
    \\ ONCE_REWRITE_TAC [arm_parse_loop_def,arm_parse_loop_pre_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,arm_parse_next_def,arm_parse_next_pre_def]
    \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w]
    \\ `~ALIGNED (ADDR32 (n2w (str2num h)) + 0x2w)` by
         METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ `ADDR32 (n2w (str2num h)) + 0x2w <> 0x28w` by
         METIS_TAC [EVAL ``ALIGNED 0x28w``]
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ r7) f`
    \\ STRIP_TAC
    \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp (Dot (Val (str2num h)) exp) r4 (b,d) *
           lisp_exp (sexp_list stack) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`r4`,`r8`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
          \\ RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. zz` (K ALL_TAC))
          \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
          \\ ASM_SIMP_TAC std_ss [] \\ ALIGNED_TAC \\ SEP_READ_TAC)
    \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
    \\ Q.UNABBREV_TAC `f2`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_CLAUSES,lisp_exp_def]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `y'`
    \\ Q.EXISTS_TAC `r7`
    \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
    \\ SEP_WRITE_TAC)
  THEN
   (FULL_SIMP_TAC std_ss [arm_tokens3_def,sexp_parse_def,SEP_CLAUSES]
    \\ Q.PAT_X_ASSUM `arm_token y' ccc b x` MP_TAC
    \\ FULL_SIMP_TAC std_ss [arm_token_def,GSYM is_number_string_def]
    \\ ONCE_REWRITE_TAC [arm_parse_loop_pre_def,arm_parse_loop_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,arm_parse_next_def,arm_parse_next_pre_def]
    \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w]
    \\ STRIP_TAC
    \\ `~ALIGNED y'` by METIS_TAC [WORD_SUB_ADD,NOT_ALIGNED]
    \\ `y' <> 0x28w` by METIS_TAC [EVAL ``ALIGNED 0x28w``]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ Q.ABBREV_TAC `f2 = (r4 + 0x4w =+ r7) f`
    \\ `(arm_tokens4 (r4 - 8w) xs b d y * arm_tokens3 (r5 + 0x8w) xs q *
           lisp_exp (Dot (Sym h) exp) r4 (b,d) *
           lisp_exp (sexp_list stack) r8 (b,d) *
           SEP_FILL (b,d) * p) (fun2set (f2,df))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `!xx yy zz. bbb` (MP_TAC o Q.SPECL [`r4 - 8w`,`r5`,`r4`,`r8`])
        \\ ASM_SIMP_TAC std_ss [ALIGNED8_STEP,ALIGNED_n2w] \\ STRIP_TAC
        \\ RES_TAC
        \\ REPEAT (Q.PAT_X_ASSUM `!df. bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ ASM_SIMP_TAC std_ss []
        \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
        \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
        \\ SEP_READ_TAC)
    \\ Q.PAT_X_ASSUM `!r4 r5. bb` (K ALL_TAC)
    \\ Q.UNABBREV_TAC `f2`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,SEP_CLAUSES,lisp_exp_def]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `y'`
    \\ Q.EXISTS_TAC `r7`
    \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [GSYM ALIGNED8_def,ALIGNED8_STEP,SEP_CLAUSES]
    \\ SEP_WRITE_TAC));

val arm_parse_string2sexp_lemma = let
  val th = Q.SPECL [`REVERSE (sexp_lex s)`,`r4`,`r5`,`3w`,`3w`,`df`,`f`,`d1`,`d2`,`d3`,`Sym "nil"`,`[]`]  arm_parse_lemma
  val th = RW [lisp_exp_def,GSYM AND_IMP_INTRO,WORD_SUB_REFL,WORD_ADD_SUB,sexp_list_def] th
  val th = SIMP_RULE (std_ss++sep_cond_ss) [cond_STAR,ALIGNED_n2w] th
  val th = RW1 [CONJ_COMM] th
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,GSYM string2sexp_def] th
  in th end

val SUB_n2w_LO = prove(
  ``!w:'a word k. 0 < k /\ k <= w2n w ==> w - n2w k <+ w``,
  Cases \\ ASM_SIMP_TAC std_ss [w2n_n2w,word_arith_lemma2]
  \\ REPEAT STRIP_TAC
  \\ `~(n < k) /\ n - k < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [WORD_LO,w2n_n2w] \\ DECIDE_TAC);

val (th,arm_parse8_def,arm_parse8_pre_def) = compilerLib.compile_all ``
  arm_parse8 (r9,r3,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
    let r4 = w2w (f r5) in
    let (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
          arm_lexer (r9,r3,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) in
    let r4 = r9 - 8w in
    let r6 = h r4 in
    let r5 = r4 in
    let r7 = 3w:word32 in
    let r8 = 3w:word32 in
    let (r4,r5,r6,r7,r8,dh,h) = arm_parse_loop1 (r4,r5,r6,r7,r8,dh,h) in
      (r9,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m)``;

val all_symbols_exists = prove(
  ``!ys xs. ?zs. all_symbols ys xs = xs ++ zs``,
  Induct THEN1 (REWRITE_TAC [all_symbols_def] \\ METIS_TAC [APPEND_NIL])
  \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [all_symbols_def]
  \\ Cases_on `identifier_string h` \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `add_symbol h xs`)
  \\ ASM_REWRITE_TAC []
  \\ POP_ASSUM (K ALL_TAC)
  \\ Induct_on `xs`
  \\ SIMP_TAC std_ss [add_symbol_def,APPEND]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `h = h'` \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ METIS_TAC []);

val sexp_lex_space_def = Define `
  sexp_lex_space s = LENGTH (sexp_lex s ++ FILTER (\x. x = "'") (sexp_lex s))`;

val token_slots_FILTER = prove(
  ``!xs a n.
      token_slots a (LENGTH (FILTER (\x. x = "'") xs) + n) =
      arm_tokens3 (a + n2w (8 * n)) xs
                  (a + n2w (8 * (LENGTH (FILTER (\x. x = "'") xs) + n))) *
      token_slots a n``,
  Induct_on `n` THEN1
   (SIMP_TAC std_ss [ADD_CLAUSES,WORD_ADD_0,token_slots_def,SEP_CLAUSES]
    \\ Induct \\ SIMP_TAC std_ss [arm_tokens3_def,LENGTH,FILTER,token_slots_def,
        WORD_ADD_0,SEP_CLAUSES]
    \\ REPEAT STRIP_TAC \\ Cases_on `h = "'"` \\ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [token_slots_def,LENGTH,ADD]
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,MULT_CLAUSES])
  \\ ASM_SIMP_TAC std_ss [ADD_CLAUSES,token_slots_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,MULT_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC,FUN_EQ_THM]
  \\ SIMP_TAC (std_ss++star_ss) []);

val token_slots_sexp_lex_space = prove(
  ``token_slots r9 (sexp_lex_space s) =
    arm_tokens3 (r9 + n2w (8 * LENGTH (sexp_lex s))) (REVERSE (sexp_lex s))
                (r9 + n2w (8 * sexp_lex_space s)) *
    token_slots r9 (LENGTH (sexp_lex s))``,
  REWRITE_TAC [sexp_lex_space_def,LENGTH_APPEND]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ REWRITE_TAC [RW [rich_listTheory.FILTER_REVERSE,rich_listTheory.LENGTH_REVERSE]
                  (Q.SPEC `REVERSE xs` token_slots_FILTER)]);

val ALIGNED8_IMP = prove(
  ``!a. ALIGNED8 a ==> ALIGNED a``,
  REWRITE_TAC [ALIGNED_THM,ALIGNED8_def]
  \\ Cases \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ STRIP_TAC
  \\ Q.EXISTS_TAC `n2w (n DIV 8 * 2)`
  \\ SIMP_TAC std_ss [word_mul_n2w,GSYM MULT_ASSOC]
  \\ METIS_TAC [DIVISION,EVAL ``0<8``,ADD_0]);

val ALIGNED8_ADD = prove(
  ``!a:word32 n. ALIGNED8 (a + n2w (8 * n)) = ALIGNED8 a``,
  Cases \\ REWRITE_TAC [ALIGNED8_def,word_add_n2w]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ REWRITE_TAC [GSYM (EVAL ``8 * 536870912``)]
  \\ SIMP_TAC bool_ss [MOD_MULT_MOD,DECIDE ``0<8:num /\ 0<536870912:num``]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [MOD_TIMES,DECIDE ``0<8:num``]);

val ALIGNED8_SUB =
  (GSYM o RW [WORD_SUB_ADD] o Q.SPECL [`a - n2w (8 * n)`,`n`]) ALIGNED8_ADD;

val arm_parse6_lemma = (GEN_ALL o SIMP_RULE std_ss [WORD_ADD_SUB,ALIGNED8_STEP] o Q.SPEC `r9+8w` o prove)(
  ``!r9 r8 r7 r6 r5 r3 y x s p m h g f dm dh dg df d b.
      string_mem (STRCAT s null_string) (r5,f,df) /\
      EVERY (\c. ORD c <> 0) (EXPLODE s) /\
      ALIGNED r9 /\ ALIGNED8 (r3 - r9) /\
      symbol_table builtin_symbols x (r3,dm,m,dg,g) /\
      (p * arm_tokens4 (r9 - 8w) [] b d y *
       token_slots r9 (sexp_lex_space s)) (fun2set (h,dh)) /\
      symbol_table_dom (all_symbols (sexp_lex s) builtin_symbols) (r3,dm,dg) ==>
      ?r9i r4i r5i r6i r7i r8i gi hi mi xi.
        arm_parse8_pre (r9,r3,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) /\
        (arm_parse8 (r9,r3,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
           (r4i,r9 - 8w,r5i,r6i,r7i,r8i,df,dg,dh,dm,f,gi,hi,mi)) /\
        (arm_tokens4 (r9 - 8w) [] r3 xi (r9 - 8w) *
         lisp_exp (string2sexp s) r7i (r3,xi) *
         SEP_FILL (r3,xi) * p) (fun2set (hi,dh)) /\
        (r5i = (r9 - 8w) + n2w (8 * sexp_lex_space s)) /\
        symbol_table (all_symbols (sexp_lex s) builtin_symbols) xi
         (r3,dm,mi,dg,gi)``,
  REWRITE_TAC [token_slots_sexp_lex_space,STAR_ASSOC]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (REWRITE_RULE [arm_tokens_EQ_arm_tokens2] arm_lexer_lemma)
  \\ SIMP_TAC std_ss [LET_DEF,arm_parse8_def,arm_parse8_pre_def]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`r8`,`r7`,`r6`])
  \\ ASM_SIMP_TAC std_ss []
  \\ `ALIGNED r1i /\ ALIGNED r3 /\ ALIGNED8 (r3 - r1i)` by
   (Q.PAT_X_ASSUM `r9 + bbb = r1i` (MP_TAC o GSYM)
    \\ SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ REPEAT STRIP_TAC THENL [
      MATCH_MP_TAC ALIGNED_ADD
      \\ ASM_SIMP_TAC bool_ss [ALIGNED_n2w,GSYM (EVAL ``4*2``)]
      \\ REWRITE_TAC [GSYM MULT_ASSOC]
      \\ SIMP_TAC std_ss [RW1 [MULT_COMM] MOD_EQ_0],
      IMP_RES_TAC ALIGNED8_IMP
      \\ POP_ASSUM MP_TAC
      \\ SIMP_TAC std_ss [word_sub_def]
      \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
      \\ ASM_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_NEG],
      ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,ALIGNED8_SUB]])
  \\ `ALIGNED (r1i - 8w)` by ALIGNED_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `(arm_tokens4 (r1i - 0x8w) (REVERSE (sexp_lex s)) r3 xi (r9 - 8w) *
       arm_tokens3 r1i (REVERSE (sexp_lex s)) (r9 + n2w (8 * sexp_lex_space s)) * SEP_FILL (r3,xi) * p)
         (fun2set (hi,dh))` by
   (FULL_SIMP_TAC std_ss [SEP_FILL_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `[]`
    \\ SIMP_TAC std_ss [SEP_EXPS_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [arm_tokens4_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [arm_tokens2_def,SEP_EXISTS]
    \\ Q.EXISTS_TAC `y''`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.PAT_X_ASSUM `r9 - 8w = y` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ `(r3, "nil") IN xi /\ (r3 + 0x18w, "quote") IN xi` by
   (STRIP_ASSUME_TAC (Q.SPECL [`sexp_lex s`,`builtin_symbols`] all_symbols_exists)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `symbol_table (builtin_symbols ++ zs) xi (r3,dm,mi,dg,gi)` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ REWRITE_TAC [builtin_symbols_def,APPEND]
    \\ NTAC 3 (ONCE_REWRITE_TAC [symbol_table_def])
    \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH,IN_DELETE,word_arith_lemma1])
  \\ `ALIGNED8 (r3 - (r1i - 8w))` by ASM_SIMP_TAC std_ss [ALIGNED8_STEP]
  \\ (IMP_RES_TAC o RW [WORD_SUB_ADD,GSYM AND_IMP_INTRO] o Q.SPEC `p`)
    (MATCH_INST (MATCH_INST arm_parse_string2sexp_lemma ``arm_parse_loop1
       (r1i - 0x8w,r1i - 0x8w,hi (r1i - 0x8w),0x3w,0x3w,dh,hi)``)
       ``SEP_FILL (r3,xi)``)
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `xi`
  \\ IMP_RES_TAC string_mem_IMP_IN
  \\ ASM_SIMP_TAC std_ss []
  \\ ALIGNED_TAC
  \\ SIMP_TAC std_ss [word_sub_def,AC WORD_ADD_ASSOC WORD_ADD_COMM]);




(* SETTING UP THE INITIAL SYMBOL TABLE *)

fun append_lists [] = []
  | append_lists (x::xs) = x @ append_lists xs

fun N_CONV 0 c = ALL_CONV
  | N_CONV n c = N_CONV (n-1) c THENC c

val symbol_table_th =
  (ONCE_REWRITE_CONV [builtin_symbols_def] THENC
   N_CONV 20 (ONCE_REWRITE_CONV [symbol_table_def]) THENC
   SIMP_CONV std_ss [LET_DEF,string_mem_def,LENGTH] THENC
   EVAL_ANY_MATCH_CONV [``n2w (ORD c):word8``] THENC
   SIMP_CONV std_ss [word_arith_lemma1,NOT_CONS_NIL,IN_DELETE] THENC
   SIMP_CONV (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11] THENC
   REWRITE_CONV [GSYM CONJ_ASSOC])
      ``symbol_table builtin_symbols x (r3,dm,m,dg,g)``

val symbol_table_dom_th =
  (ONCE_REWRITE_CONV [builtin_symbols_def] THENC
   N_CONV 20 (ONCE_REWRITE_CONV [symbol_table_dom_def]) THENC
   SIMP_CONV std_ss [LET_DEF,string_mem_def,LENGTH] THENC
   EVAL_ANY_MATCH_CONV [``n2w (ORD c):word8``] THENC
   SIMP_CONV std_ss [word_arith_lemma1,NOT_CONS_NIL,IN_DELETE] THENC
   SIMP_CONV (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11] THENC
   REWRITE_CONV [GSYM CONJ_ASSOC] THENC
   REWRITE_CONV [string_mem_dom_def] THENC
   SIMP_CONV std_ss [word_arith_lemma1,INSERT_SUBSET,EMPTY_SUBSET] THENC
   REWRITE_CONV [GSYM CONJ_ASSOC] THENC
   SIMP_CONV std_ss [GSYM ADD_ASSOC])
      ``symbol_table_dom builtin_symbols (r3,dm,dg)``

val symbol_table_tm = let
  fun all_distinct [] = []
    | all_distinct (x::xs) = x :: all_distinct (filter (fn y => not (x = y)) xs)
  val tms = find_terms (can (match_term ``(g:word32->word8) (r3 + n2w m) = n2w n``)) (concl symbol_table_th)
  val mooch = Arbnum.toInt o numSyntax.dest_numeral o cdr o cdr
  val ys = sort (fn x => fn y => x <= y) (all_distinct (map mooch tms))
  val zs = map (fn x => (x, filter (fn tm => mooch tm = x) tms)) ys
  val tt = (car o car) ``(x:word32 =+ y:word8)``
  val ww = mk_comb(``w2w:word32->word8``,mk_var("r6",``:word32``))
  fun cuscus (x,ws) = let
    val v = mk_comb(``n2w:num->word32``,numSyntax.mk_numeral(Arbnum.fromInt x))
    val v = (mk_var("r6",``:word32``),v)
    fun hipochus tm = let
      val (x,y) = dest_eq tm
      in (car x, mk_comb(mk_comb(mk_comb(tt,cdr x),ww),car x)) end
    in v :: map hipochus ws end
  val ts = append_lists (map cuscus zs)
  val tms = find_terms (can (match_term ``(m:word32->word32) (r3) = w``)) (concl symbol_table_th)
  val tt = (car o car) ``(x:word32 =+ y:word32)``
  val ww = mk_var("r6",``:word32``)
  fun cuscus tm = let
    val (x,y) = dest_eq tm
    in [(ww, y),
        (car x, mk_comb(mk_comb(mk_comb(tt,cdr x),ww),car x))] end
  val ts2 = append_lists (map cuscus tms)
  val ll = pairSyntax.list_mk_pair[mk_var("r3",``:word32``),
                                   mk_var("r6",``:word32``),
                                   mk_var("dg",``:word32 set``),
                                   mk_var("g",``:word32->word8``)]
  fun take_drop n [] = ([],[])
    | take_drop n (x::xs) = if n = 0 then ([],x::xs) else let
        val (ys,zs) = take_drop (n-1) xs
        in (x::ys,zs) end
  fun split [] = []
    | split (x::xs) = let
        val (ys,zs) = take_drop 8 (x::xs)
        in ys :: split zs end
  val tts = split ts
  val i = ref 0
  val ss = hd tts
  val ty = type_of (mk_abs(mk_var("fgh",type_of ll),ll))
  fun mk_func ss = let
    val tm3 = foldr (fn ((x,y),tm) => pairSyntax.mk_anylet([(x,y)],tm)) ll ss
    val _ = (i := !i + 1)
    val def = mk_eq(mk_comb(mk_var("arm_setup" ^ int_to_string (!i),ty),ll),tm3)
    in def end
  val defs = map mk_func tts
  val gh = map (fn tm => (ll, cdr (car tm))) defs
  val ls = (defs @ [mk_func gh])
  val ll2 = pairSyntax.list_mk_pair[mk_var("r3",``:word32``),
                                 mk_var("r6",``:word32``),
                                 mk_var("dm",``:word32 set``),
                                 mk_var("m",``:word32->word32``)]
  val tts = split ts2
  val ss = hd tts
  val ty = type_of (mk_abs(mk_var("fgh",type_of ll2),ll2))
  fun mk_func2 ss = let
    val tm3 = foldr (fn ((x,y),tm) => pairSyntax.mk_anylet([(x,y)],tm)) ll2 ss
    val _ = (i := !i + 1)
    val def = mk_eq(mk_comb(mk_var("arm_setup" ^ int_to_string (!i),ty),ll2),tm3)
    in def end
  val defs = map mk_func2 tts
  val gh = map (fn tm => (ll2, cdr (car tm))) defs
  val ls2 = (defs @ [mk_func2 gh])
  val ll3 = pairSyntax.list_mk_pair[mk_var("r3",``:word32``),
                                   mk_var("r6",``:word32``),
                                   mk_var("dm",``:word32 set``),
                                   mk_var("dg",``:word32 set``),
                                   mk_var("m",``:word32->word32``),
                                   mk_var("g",``:word32->word8``)]
  val ty = type_of (mk_abs(mk_var("fgh",type_of ll3),ll3))
  fun mk_func3 ss = let
    val tm3 = foldr (fn ((x,y),tm) => pairSyntax.mk_anylet([(x,y)],tm)) ll3 ss
    val _ = (i := !i + 1)
    val def = mk_eq(mk_comb(mk_var("arm_setup",ty),ll3),tm3)
    in def end
  val def = mk_func3 [(ll,(fst o dest_eq o last) ls), (ll2,(fst o dest_eq o last) ls2)]
  val tm = list_mk_conj (ls @ ls2 @ [def])
  in tm end;

val (_,arm_setup_def,arm_setup_pre_def) = compilerLib.compile_all symbol_table_tm;

val arm_setup_lemma = prove(
  ``!r3 dg dm g m.
      symbol_table_dom builtin_symbols (r3,dm,dg) ==>
      arm_setup_pre (r3,r6,dm,dg,m,g) /\
      ?gi mi r6i.
        (arm_setup (r3,r6,dm,dg,m,g) = (r3,r6i,dm,dg,mi,gi)) /\
        symbol_table builtin_symbols (builtin_symbols_set r3) (r3,dm,mi,dg,gi)``,
  SIMP_TAC std_ss [arm_setup_def,LET_DEF]
  THEN CONV_TAC (EVAL_ANY_MATCH_CONV [``w2w (n2w n)``])
  THEN REWRITE_TAC [symbol_table_th]
  THEN SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11,APPLY_UPDATE_THM]
  THEN SIMP_TAC std_ss [builtin_symbols_set_def,EXTENSION,IN_INSERT,IN_DELETE,NOT_IN_EMPTY]
  THEN REWRITE_TAC [CONJ_ASSOC]
  THEN REVERSE (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC)
  THEN1 METIS_TAC [] THEN REWRITE_TAC [GSYM CONJ_ASSOC]
  THEN POP_ASSUM MP_TAC
  THEN SIMP_TAC std_ss [symbol_table_dom_th,INSERT_SUBSET,EMPTY_SUBSET]
  THEN SIMP_TAC std_ss [arm_setup_def,arm_setup_pre_def,LET_DEF]
  THEN SIMP_TAC std_ss [ALIGNED_INTRO,GSYM CONJ_ASSOC]
  THEN ONCE_REWRITE_TAC [ALIGNED_MOD_4]
  THEN SIMP_TAC std_ss [] THEN SIMP_TAC std_ss [WORD_ADD_0])


(* SETTING UP lisp_inv *)

val (arm_string2sexp_thms,arm_string2sexp_def,arm_string2sexp_pre_def) = compile_all ``
  arm_string2sexp' (r3,r4,r5,df,dg,dh,dm,f,g,h,m) =
    let r9 = r5 in
    let r8 = r4 << 3 in
    let r7 = r8 + r8 in
    let h = (r9 - 0x20w =+ r8) h in
    let r5 = r3 in
    let r3 = r9 + r7 in
    let r9 = r9 + 8w in
    let r3 = r3 + 24w in
    let r6 = 40w in
    let (r3,r6,dm,dg,m,g) = arm_setup (r3,r6,dm,dg,m,g) in
    let r6 = 40w in
    let h = (r9 - 8w =+ r6) h in
    let (r9,r4,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) =
      arm_parse8 (r9,r3,r5,r6,r7,r8,df,dg,dh,dm,f,g,h,m) in
    let r9 = r4 in
    let r8 = 1w in
    let r6 = h (r9 - 0x20w) in
    let h = (r9 - 0x1Cw =+ r8) h in
    let r8 = r9 + r6 in
    let r8 = r8 + 8w in
    let h = (r9 + 4w =+ r8) h in
    let r5 = r5 + 8w in
    let r3 = r7 in
    let h = (r9 =+ r5) h in
    let r4 = 3w:word32 in
    let r5 = 3w:word32 in
    let r6 = 3w:word32 in
    let r7 = 3w:word32 in
    let r8 = 3w:word32 in
      (r3,r4,r5,r6,r7,r8,r9,df,dg,dh,dm,f,g,h,m)``;

val symbol_table_dom_APPEND = prove(
  ``!xs ys a dm dg.
      symbol_table_dom (xs++ys) (a,dm,dg) ==>
      symbol_table_dom xs (a,dm,dg)``,
  REVERSE Induct
  THEN1 (SIMP_TAC std_ss [symbol_table_dom_def,APPEND] \\ METIS_TAC [])
  \\ REWRITE_TAC [symbol_table_dom_def,APPEND]
  \\ Cases THEN1 REWRITE_TAC [symbol_table_dom_def,APPEND]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [symbol_table_dom_ALIGNED]
  \\ FULL_SIMP_TAC std_ss [symbol_table_dom_def,INSERT_SUBSET]) ;

val sexp2string_NOT_NULL = prove(
  ``!s. sexp_ok s ==> EVERY (\c. ORD c <> 0) (EXPLODE (sexp2string s))``,
  REWRITE_TAC [sexp2string_def] \\ Q.SPEC_TAC (`T`,`b`)
  \\ completeInduct_on `LSIZE s`
  \\ REVERSE (STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `s` SExp_expand))
  \\ ASM_SIMP_TAC std_ss []
  THEN1
   (FULL_SIMP_TAC std_ss [sexp_ok_def,sexp2string_aux_def,identifier_string_def]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [identifier_char_def,space_char_def]
    \\ DECIDE_TAC)
  THEN1
   (SIMP_TAC std_ss [sexp_ok_def,sexp2string_aux_def,identifier_string_def]
    \\ REPEAT STRIP_TAC \\ MP_TAC (Q.SPEC `n` str2num_num2str)
    \\ SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [sexp_ok_def,sexp2string_aux_def]
  \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `a1 = exp1`
  \\ Q.ABBREV_TAC `a2 = exp2`
  \\ `ORD #"(" <> 0 /\ ORD #")" <> 0 /\ ORD #"." <> 0 /\ ORD #" " <> 0 /\ ORD #"'" <> 0` by EVAL_TAC
  \\ Cases_on `isQuote (Dot a1 a2) /\ b` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,LSIZE_def,sexp_ok_def]
    \\ REWRITE_TAC [LIST_STRCAT_def,EXPLODE_STRCAT,EVERY_APPEND]
    \\ ASM_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF]
    \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,LSIZE_def,sexp_ok_def]
    \\ `LSIZE y < SUC (SUC (LSIZE y))` by DECIDE_TAC \\ METIS_TAC [])
  \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [LSIZE_def]
  \\ `LSIZE a1 < v` by DECIDE_TAC
  \\ `LSIZE a2 < v` by DECIDE_TAC
  \\ Cases_on `b` THEN
   (SIMP_TAC std_ss [LET_DEF]
    \\ REWRITE_TAC [LIST_STRCAT_def,EXPLODE_STRCAT,EVERY_APPEND]
    \\ ASM_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF]
    \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,LSIZE_def,sexp_ok_def]
    \\ Cases_on `a2 = Sym "nil"` \\ ASM_SIMP_TAC std_ss [] THEN1
     (REWRITE_TAC [LIST_STRCAT_def,EXPLODE_STRCAT,EVERY_APPEND]
      \\ ASM_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF]
      \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,LSIZE_def,sexp_ok_def])
    \\ Cases_on `isDot a2`
    \\ ASM_SIMP_TAC std_ss []
    \\ REWRITE_TAC [LIST_STRCAT_def,EXPLODE_STRCAT,EVERY_APPEND]
    \\ ASM_SIMP_TAC std_ss [EXPLODE_def,EVERY_DEF] \\ METIS_TAC []));

val token_slots_IMP = prove(
  ``!n a h dh.
      token_slots a n (fun2set (h,dh)) ==>
      (dh = ch_active_set (a,0,n) UNION ch_active_set (a + 4w,0,n))``,
  Induct THEN1
   (SIMP_TAC std_ss [token_slots_def,fun2set_def,
      ch_active_set_def,emp_def, DECIDE ``i <= j /\ j < i + 0:num = F``]
    \\ SIMP_TAC std_ss [GSPECIFICATION,EXTENSION,NOT_IN_EMPTY,IN_UNION])
  \\ ASM_SIMP_TAC std_ss [token_slots_def,SEP_EXISTS,one_STAR,GSYM STAR_ASSOC]
  \\ SIMP_TAC std_ss [IN_fun2set,IN_DELETE]
  \\ `!a. ch_active_set (a:word32,0,SUC n) =
          a INSERT ch_active_set (a + 8w:word32,0,n)` by
   (SIMP_TAC std_ss [GSPECIFICATION,EXTENSION,IN_INSERT,
      ch_active_set_def,GSYM WORD_ADD_ASSOC,
      word_add_n2w,word_mul_n2w,GSYM MULT_CLAUSES]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
      Cases_on `j = 0` \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]
      \\ DISJ2_TAC \\ Q.EXISTS_TAC `j - 1`
      \\ `SUC (j - 1) = j` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC,
      Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0],
      Q.EXISTS_TAC `SUC j` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ REVERSE (Cases_on `a IN dh /\ a + 4w IN dh`)
  THEN1 (FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_EQ_ADD_CANCEL]
  \\ FULL_SIMP_TAC std_ss [fun2set_DELETE] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DELETE,IN_UNION,word_arith_lemma1,IN_INSERT]
  \\ METIS_TAC []);

val token_slots_ADD = prove(
  ``!n m a.
      token_slots a (n + m) =
      token_slots a n * token_slots (a + n2w (8 * n)) m``,
  Induct \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,token_slots_def,WORD_ADD_0,
    ADD,MULT_CLAUSES,word_add_n2w,GSYM WORD_ADD_ASSOC,STAR_ASSOC]);

val ch_active_set_ADD = prove(
  ``!a m n. ch_active_set (a,0,n + m) =
            ch_active_set (a,0,n) UNION ch_active_set (a + n2w (8 * n),0,m)``,
  SIMP_TAC std_ss [ch_active_set_def,EXTENSION,GSPECIFICATION,IN_UNION]
  \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_mul_n2w,word_add_n2w]
  \\ SIMP_TAC std_ss [GSYM LEFT_ADD_DISTRIB]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] THENL [
   Cases_on `j < n` THEN1 METIS_TAC []
   \\ `j - n < m /\ (n + (j - n) = j)` by DECIDE_TAC \\ METIS_TAC [],
   `j < n + m` by DECIDE_TAC \\ METIS_TAC [],
   `n + j < n + m` by DECIDE_TAC \\ METIS_TAC []]);

val ch_active_set_4 = prove(
  ``!a n. ch_active_set (a,0,n) UNION ch_active_set (a + 0x4w,0,n) =
          { a + n2w (4 * i) | i < 2 * n }``,
  SIMP_TAC std_ss [ch_active_set_def,EXTENSION,GSPECIFICATION,IN_UNION]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w,word_mul_n2w]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `2 * j` \\ SIMP_TAC std_ss [MULT_ASSOC] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `2 * j + 1`
         \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB]
         \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC] \\ DECIDE_TAC)
  \\ STRIP_ASSUME_TAC (RW1 [MULT_COMM] (MATCH_MP (Q.SPEC `i` DA) (DECIDE ``0 < 2:num``)))
  \\ ASM_SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB]
  \\ `(r = 0) \/ (r = 1)` by DECIDE_TAC THENL [
    DISJ1_TAC \\ Q.EXISTS_TAC `q`
    \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC,
    DISJ2_TAC \\ Q.EXISTS_TAC `q`
    \\ ASM_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM] \\ DECIDE_TAC]);

val ALL_DISTINCT_all_symbols = prove(
  ``!xs ys. ALL_DISTINCT (all_symbols xs ys) = ALL_DISTINCT ys``,
  Induct \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [all_symbols_def]
  \\ Cases_on `identifier_string h`
  \\ ASM_SIMP_TAC std_ss [all_symbols_def]
  \\ Q.SPEC_TAC (`h`,`h`) \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `ys`
  \\ SIMP_TAC std_ss [add_symbol_def,ALL_DISTINCT,MEM]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `h = h'` \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT]
  \\ `h <> h' ==> (MEM h (add_symbol h' ys) = MEM h ys)` suffices_by METIS_TAC []
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `ys`
  \\ SIMP_TAC std_ss [MEM,add_symbol_def] \\ METIS_TAC [MEM]);

val set_lemma = prove(
  ``(v UNION u = s) /\ DISJOINT v u ==> (u = s DIFF v) /\ (v SUBSET s)``,
  SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_DIFF,SUBSET_DEF,
    DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER] \\ METIS_TAC []);

val fun2set_DIFF_IMP = store_thm("fun2set_DIFF_IMP",
  ``!p x. (!y. p (fun2set (f,y)) ==> (x = y)) /\ (p * q) (fun2set (f,df)) ==>
          q (fun2set (f,df DIFF x))``,
  SIMP_TAC std_ss [STAR_def,GSYM fun2set_DIFF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [SPLIT_def]
  \\ IMP_RES_TAC set_lemma
  \\ IMP_RES_TAC SUBSET_fun2set
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss []);

val ch_active_set2_def = Define `
  ch_active_set2 (a,i,n) =
    ch_active_set (a,i,n) UNION ch_active_set (a + 0x4w,i,n)`;

val ALIGNED8_EXISTS = prove(
  ``!w:word32. ALIGNED8 w ==> ?k. w = n2w (8 * k)``,
  Cases \\ ASM_SIMP_TAC std_ss [ALIGNED8_def,w2n_n2w]
  \\ METIS_TAC [DIVISION,EVAL ``0<8``,ADD_0,MULT_COMM])

val ALIGNED8_ADD_EQ = prove(
  ``!w:word32 v. ALIGNED8 w ==> (ALIGNED8 (w + v) = ALIGNED8 v) /\
                                (ALIGNED8 (w - v) = ALIGNED8 (-v))``,
  SIMP_TAC std_ss [word_sub_def]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC ALIGNED8_EXISTS
  \\ ASM_SIMP_TAC std_ss [ALIGNED8_ADD]);

val IMP_lisp_x = prove(
  ``!s a p.
      sexp_ok s /\ ALIGNED8 (sa - r5) /\
      (lisp_exp s a (sa,xi) * p) (fun2set (h,ch_active_set2 (r5 + 8w,0,ll))) ==>
      lisp_x s (a,ch_active_set (r5,1,1 + ll),h) (set_add (0x0w - sa) xi)``,
  REVERSE Induct THENL [
    SIMP_TAC std_ss [lisp_exp_def,cond_STAR,lisp_x_def,ALIGNED_INTRO]
    \\ SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_SUB_SUB,WORD_SUB_RZERO]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,word_sub_def],
    SIMP_TAC std_ss [lisp_exp_def,cond_STAR,lisp_x_def,ALIGNED_INTRO,sexp_ok_def]
    \\ SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w,AC MULT_COMM MULT_ASSOC],
    SIMP_TAC std_ss [lisp_exp_def,cond_STAR,lisp_x_def,ALIGNED_INTRO,sexp_ok_def]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS] \\ REPEAT STRIP_TAC THENL [
      `a IN ch_active_set2 (r5 + 0x8w,0,ll)` by SEP_READ_TAC
      \\ FULL_SIMP_TAC std_ss [ch_active_set2_def,ch_active_set_def,
           GSPECIFICATION,IN_UNION] THENL [
        Q.EXISTS_TAC `1 + j`
        \\ SIMP_TAC std_ss [word_mul_n2w,LEFT_ADD_DISTRIB]
        \\ ASM_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC],
        FULL_SIMP_TAC (std_ss++sep_cond_ss) [GSYM ALIGNED8_def,cond_STAR]
        \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,word_mul_n2w]
        \\ FULL_SIMP_TAC bool_ss [DECIDE ``8 + (4 + 8 * j) = 4 + 8 * (1 + j:num)``]
        \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS]
        \\ FULL_SIMP_TAC std_ss [ALIGNED8_SUB]
        \\ FULL_SIMP_TAC std_ss [word_sub_def]
        \\ `ALIGNED8 (-4w:word32)` by METIS_TAC [ALIGNED8_ADD_EQ]
        \\ POP_ASSUM MP_TAC \\ EVAL_TAC],
      FULL_SIMP_TAC (std_ss++sep_cond_ss) [GSYM ALIGNED8_def,cond_STAR],
      FULL_SIMP_TAC (std_ss++sep_cond_ss) [GSYM ALIGNED8_def,cond_STAR]
      \\ Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC)
      \\ Q.PAT_X_ASSUM `!xx.bbb` MATCH_MP_TAC
      \\ Q.EXISTS_TAC `one (a,y) * one (a + 0x4w,y') * p * lisp_exp s' y' (sa,xi)`
      \\ `h a = y` by SEP_READ_TAC
      \\ FULL_SIMP_TAC (std_ss++star_ss) [],
      FULL_SIMP_TAC (std_ss++sep_cond_ss) [GSYM ALIGNED8_def,cond_STAR]
      \\ Q.PAT_X_ASSUM `!xx.bbb` MATCH_MP_TAC
      \\ Q.EXISTS_TAC `one (a,y) * one (a + 0x4w,y') * p * lisp_exp s y (sa,xi)`
      \\ `h (a + 4w) = y'` by SEP_READ_TAC
      \\ FULL_SIMP_TAC (std_ss++star_ss) []]]);

val lisp_exp_ok_data = prove(
  ``!x w a s p f df.
      (lisp_exp x w (a,s) * p) (fun2set (f,df)) ==>
      ok_data w { y | y IN df /\ ALIGNED8 (a - y) }``,
  REVERSE Induct THENL [
    SIMP_TAC std_ss [lisp_exp_def,cond_STAR,ok_data_def]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC NOT_ALIGNED
    \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD,word_arith_lemma3,WORD_ADD_0],
    SIMP_TAC std_ss [lisp_exp_def,cond_STAR,ok_data_def]
    \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w]
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,word_arith_lemma4]
    \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w],
    SIMP_TAC (std_ss++sep_cond_ss) [lisp_exp_def,cond_STAR,ok_data_def]
    \\ SIMP_TAC std_ss [SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_EXISTS]
    \\ SIMP_TAC std_ss [GSYM STAR_ASSOC,one_STAR,IN_fun2set]
    \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [GSPECIFICATION,ALIGNED8_def]]);

val SUBSET_ok_data = prove(
  ``!a s t. ok_data a t /\ t SUBSET s ==> ok_data a s``,
  METIS_TAC [ok_data_def,SUBSET_DEF]);

val SEP_EXPS_ok_data = prove(
  ``!xs sa xi hh s x g.
      SEP_EXPS xs (a,xi) (fun2set (hh,g)) /\ x IN g /\ g SUBSET s ==>
      ok_data (hh x) { y | y IN s /\ ALIGNED8 (a - y) }``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs + 2 * SUM_LSIZE (MAP SND xs)`
  \\ Cases \\ SIMP_TAC std_ss [SEP_EXPS_def,emp_def,fun2set_EMPTY,SUBSET_EMPTY]
  THEN1 METIS_TAC [NOT_IN_EMPTY]
  \\ Cases_on `h`
  \\ SIMP_TAC std_ss [SEP_EXPS_def,LENGTH,MAP,SUM_LSIZE_def,MULT_CLAUSES]
  \\ REVERSE (STRIP_ASSUME_TAC (Q.SPEC `r` SExp_expand))
  \\ ASM_SIMP_TAC (std_ss++sep_cond_ss) [lisp_exp_def,cond_STAR,LSIZE_def]
  THEN1 (FULL_SIMP_TAC std_ss [ADD] \\ METIS_TAC [DECIDE ``m < SUC m:num``])
  THEN1 (FULL_SIMP_TAC std_ss [ADD] \\ METIS_TAC [DECIDE ``m < SUC m:num``])
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
  \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC,one_STAR,IN_fun2set,fun2set_DELETE]
  \\ NTAC 7 STRIP_TAC
  \\ `(g DELETE q DELETE (q + 0x4w)) SUBSET g` by METIS_TAC [SUBSET_DEF,IN_DELETE]
  \\ Cases_on `x = q` THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC lisp_exp_ok_data
    \\ MATCH_MP_TAC SUBSET_ok_data
    \\ Q.EXISTS_TAC `{y | y IN g DELETE q DELETE (q + 0x4w) /\ ALIGNED8 (a - y)}`
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,GSPECIFICATION,IN_DELETE])
  \\ Cases_on `x = q + 4w` THEN1
   (Q.PAT_X_ASSUM `bbb (fun2set (hh,g DELETE q DELETE (q + 0x4w)))` MP_TAC
    \\ ONCE_REWRITE_TAC [STAR_COMM]
    \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC lisp_exp_ok_data
    \\ MATCH_MP_TAC SUBSET_ok_data
    \\ Q.EXISTS_TAC `{y | y IN g DELETE q DELETE (q + 0x4w) /\ ALIGNED8 (a - y)}`
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,GSPECIFICATION,IN_DELETE])
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC,GSYM SEP_EXPS_def,IN_DELETE]
  \\ SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ Q.ABBREV_TAC `a1 = exp1` \\ Q.ABBREV_TAC `a2 = exp2`
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC
  \\ `x IN (g DELETE q DELETE (q + 0x4w))` by ASM_SIMP_TAC std_ss [IN_DELETE]
  \\ IMP_RES_TAC SUBSET_TRANS
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `ys = (hh q,a1)::(hh (q + 0x4w),a2)::t`
  \\ Q.ABBREV_TAC `i = SUC (LENGTH t) +
        2 * (SUC (LSIZE a1 + LSIZE a2) + SUM_LSIZE (MAP SND t))`
  \\ `LENGTH ys + 2 * SUM_LSIZE (MAP SND ys) < i` by
   (Q.UNABBREV_TAC `ys` \\ Q.UNABBREV_TAC `i`
    \\ FULL_SIMP_TAC std_ss [LENGTH,MAP,SUM_LSIZE_def,MULT_CLAUSES,ADD1]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!m. m < i ==> bbb` (ASSUME_TAC o UNDISCH o Q.SPEC `LENGTH (ys:(word32 # SExp) list) + 2 * SUM_LSIZE (MAP SND ys)`)
  \\ POP_ASSUM (ASSUME_TAC o RW [] o Q.SPEC `ys`)
  \\ `x IN (g DELETE q DELETE (q + 0x4w))` by METIS_TAC [IN_DELETE]
  \\ FULL_SIMP_TAC std_ss [GSYM SEP_EXPS_def]
  \\ METIS_TAC [SUBSET_TRANS]);

val arm_string2sexp_lemma = store_thm("arm_string2sexp_lemma",
  ``32 <= w2n r5 /\ w2n r5 + 16 * l + 20 < 2 ** 32 /\ l <> 0 /\
    sexp_lex_space (sexp2string s) <= l /\ sexp_ok s /\
    string_mem (STRCAT (sexp2string s) null_string) (r3,f,df) /\ ALIGNED r5 /\
    (token_slots (r5 - 32w) (l + l + 7)) (fun2set (h,dh)) /\
    symbol_table_dom (all_symbols (sexp2tokens s T) builtin_symbols)
                     (r5 + n2w (l * 16) + 0x18w,dm,dg) ==>
    ?r3i gi hi mi.
      arm_string2sexp'_pre (r3,n2w l,r5,df,dg,dh,dm,f,g,h,m) /\
      (arm_string2sexp' (r3,n2w l,r5,df,dg,dh,dm,f,g,h,m) =
        (r3i,3w,3w,3w,3w,3w,r5,df,dg,dh,dm,f,gi,hi,mi)) /\
      ?sym. lisp_inv (s,Sym "nil",Sym "nil",Sym "nil",Sym "nil",Sym "nil",l)
              (r3i,3w,3w,3w,3w,3w,r5,dh,hi,sym,dm,mi,dg,gi)``,
  REWRITE_TAC [GSYM AND_IMP_INTRO]
  \\ SIMP_TAC std_ss [GSYM sexp_lex_sexp2str]
  \\ REWRITE_TAC [AND_IMP_INTRO,GSYM CONJ_ASSOC,GSYM sexp2string_def]
  \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [arm_string2sexp_def,arm_string2sexp_pre_def,LET_DEF]
  \\ SIMP_TAC std_ss [word_LSL_n2w,word_add_n2w,GSYM LEFT_ADD_DISTRIB]
  \\ `symbol_table_dom builtin_symbols (r5 + n2w (l * 16) + 0x18w,dm,dg)` by
   (MATCH_MP_TAC symbol_table_dom_APPEND \\ METIS_TAC [all_symbols_exists])
  \\ (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
       Q.SPECL [`40w`,`r5 + n2w (l * 16) + 0x18w`] o GEN_ALL) arm_setup_lemma
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB,ALIGNED_INTRO]
  \\ `n2w (l * 16) + r5 + 0x18w = r5 + n2w (l * 16) + 0x18w` by
       SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB,ALIGNED_INTRO]
  \\ POP_ASSUM (K ALL_TAC)
  \\ Q.ABBREV_TAC `h2 = (r5 =+ 0x28w) ((r5 - 0x20w =+ n2w (l * 8)) h)`
  \\ `ALIGNED (r5 + 8w)` by ALIGNED_TAC
  \\ IMP_RES_TAC sexp2string_NOT_NULL
  \\ `(token_slots (r5 - 0x18w) 3 * one (r5 - 0x20w,n2w (l * 8)) *
       token_slots (r5 + 0x8w + n2w (8 * sexp_lex_space (sexp2string s)))
         (l + l + 2 - sexp_lex_space (sexp2string s)) *
       (SEP_EXISTS w. one (r5 - 0x1Cw,w)) * arm_tokens4 r5 [] b d r5 *
       token_slots (r5 + 0x8w) (sexp_lex_space (sexp2string s)))
        (fun2set (h2,dh))` by
   (Q.PAT_X_ASSUM `32 <= w2n r5` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `w2n r5 + 16 * l + 20 < 4294967296` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `l <> 0` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS]
    \\ Q.ABBREV_TAC `k = sexp_lex_space (sexp2string s)`
    \\ Q.UNABBREV_TAC `h2`
    \\ `k + p + (k + p) + 2 - k = k + p + p + 2` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ ASM_SIMP_TAC std_ss [arm_tokens2_def,arm_tokens4_def,SEP_CLAUSES,STAR_ASSOC]
    \\ `l + l + 7 = 1 + 3 + 1 + k + k + p + p + 2` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss []
    \\ FULL_SIMP_TAC std_ss [token_slots_ADD]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3]
    \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,ADD_ASSOC]
    \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``SUC 0``)]
    \\ FULL_SIMP_TAC bool_ss [token_slots_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `y'`
    \\ Q.EXISTS_TAC `y'''`
    \\ SEP_WRITE_TAC)
  \\ `ALIGNED8 (r5 + n2w (l * 16) + 0x18w - r5)` by
   (SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_ADD_SUB2]
    \\ SIMP_TAC bool_ss [word_add_n2w,DECIDE ``l * 16 + 24 = 0 + 8 * (2 * l + 3:num)``]
    \\ SIMP_TAC bool_ss [GSYM word_add_n2w,ALIGNED8_ADD] \\ EVAL_TAC)
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o SPEC_ALL o
   Q.SPECL [`r5`,`builtin_symbols_set (r5 + n2w (l * 16) + 0x18w)`,
            `sexp2string s`,`token_slots (r5 - 24w) 3 * one (r5 - 32w,n2w (l * 8)) *
             token_slots (r5 + 0x8w + n2w (8 * sexp_lex_space (sexp2string s)))
               (l + l + 2 - sexp_lex_space (sexp2string s)) *
               SEP_EXISTS w. one (r5 - 28w,w)`] o
   MATCH_INST arm_parse6_lemma)
     ``arm_parse8
        (r5 + 0x8w,r5 + n2w (l * 16) + 0x18w,r3,0x28w,n2w (l * 16),n2w (l * 8),
         df,dg,dh,dm,f,gi,h2,mi)``
  \\ ASM_SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
   (ALIGNED_TAC
    \\ FULL_SIMP_TAC bool_ss [DECIDE ``3:num = SUC (SUC (SUC 0))``,token_slots_def,arm_tokens4_def,arm_tokens2_def]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC] \\ SEP_READ_TAC)
  \\ Q.EXISTS_TAC `set_add (0w - (r5 + n2w (l * 16) + 0x18w)) xi`
  \\ `hi (r5 - 0x20w) = n2w (l * 8)` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `h3 = (r5 =+ r5 + n2w (8 * sexp_lex_space (sexp2string s)) + 0x8w)
       ((r5 + 0x4w =+ r5 + n2w (l * 8) + 0x8w) ((r5 - 0x1Cw =+ 0x1w) hi))`
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Q.EXISTS_TAC `1 + sexp_lex_space (sexp2string s)`
  \\ Q.EXISTS_TAC `F`
  \\ ASM_SIMP_TAC std_ss [LET_DEF,lisp_x_def,word_arith_lemma2,
       ALIGNED_INTRO,ALIGNED_n2w]
  \\ Q.ABBREV_TAC `ll = sexp_lex_space (sexp2string s)`
  \\ SIMP_TAC std_ss [lisp_symbol_table_def]
  \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `h3`
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ SIMP_TAC std_ss [APPLY_UPDATE_THM]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM])
  \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `h3`
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,WORD_EQ_ADD_CANCEL]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,
                        AC MULT_COMM MULT_ASSOC])
  \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `h3`
    \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,WORD_EQ_SUB_LADD,word_arith_lemma1]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_EQ_ADD_CANCEL,WORD_SUB_ADD])
  \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `h3`
    \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,WORD_EQ_SUB_LADD,word_arith_lemma3,word_arith_lemma1]
    \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_EQ_ADD_CANCEL]
    \\ ONCE_REWRITE_TAC [MULT_COMM] \\ SEP_READ_TAC)
  \\ STRIP_TAC THEN1
   (IMP_RES_TAC token_slots_IMP \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ REWRITE_TAC [ch_active_set_4,ref_set_def]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
    \\ SIMP_TAC std_ss [EXTENSION,IN_UNION,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [] THENL [
      Cases_on `i <= 8` THENL [
        DISJ2_TAC \\ Q.EXISTS_TAC `8 - i`
        \\ SIMP_TAC std_ss [LEFT_SUB_DISTRIB,MULT_ASSOC]
        \\ Cases_on `i = 8`
        \\ ASM_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0,WORD_SUB_RZERO]
        \\ `4 * i < 32` by DECIDE_TAC
        \\ ASM_SIMP_TAC std_ss [],
        DISJ1_TAC \\ Q.EXISTS_TAC `i - 8`
        \\ `~(4 * i < 32)` by DECIDE_TAC
        \\ ASM_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0,WORD_SUB_RZERO]
        \\ SIMP_TAC std_ss [LEFT_SUB_DISTRIB,MULT_ASSOC] \\ DECIDE_TAC],
      Q.EXISTS_TAC `8 + i`
      \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC,GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD] \\ DECIDE_TAC,
      Q.EXISTS_TAC `8 - i`
      \\ REVERSE CONJ_TAC THEN1 DECIDE_TAC
      \\ SIMP_TAC std_ss [LEFT_SUB_DISTRIB,MULT_ASSOC]
      \\ Cases_on `i = 0`
      \\ ASM_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0,WORD_SUB_RZERO]
      \\ ‘0 < i’ by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
      \\ `32 - (32 - 4 * i) = 4*i` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [] ])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [word_mul_n2w,Q.SPEC `16` MULT_COMM]
    \\ Q.ABBREV_TAC `a = r5 + n2w (l * 16) + 0x18w`
    \\ `?zs. all_symbols (sexp_lex (sexp2string s)) builtin_symbols =
             builtin_symbols ++ zs` by
               METIS_TAC [all_symbols_exists]
    \\ Q.EXISTS_TAC `zs`
    \\ FULL_SIMP_TAC std_ss []
    \\ `set_add a (set_add (0x0w - a) xi) = xi` by
        (REPEAT (POP_ASSUM (K ALL_TAC))
         \\ SIMP_TAC std_ss [set_add_def,FUN_EQ_THM,FORALL_PROD,IN_DEF]
         \\ SIMP_TAC std_ss [WORD_SUB_SUB,WORD_SUB_ADD,WORD_SUB_RZERO])
    \\ ASM_SIMP_TAC std_ss []
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    \\ REWRITE_TAC [ALL_DISTINCT_all_symbols] \\ EVAL_TAC)
  \\ Q.ABBREV_TAC `sa = (r5 + n2w (l * 16) + 0x18w)`
  \\ `(0x0w,"nil") IN set_add (0x0w - sa) xi` by
   (Q.PAT_X_ASSUM `symbol_table
       (all_symbols (sexp_lex (sexp2string s)) builtin_symbols) xi
       (sa,dm,mi',dg,gi')` MP_TAC
    \\ Q.UNABBREV_TAC `sa` \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ `?zs. all_symbols (sexp_lex (sexp2string s)) builtin_symbols =
          builtin_symbols ++ zs` by METIS_TAC [all_symbols_exists]
    \\ Q.ABBREV_TAC `sa = (r5 + n2w (l * 16) + 0x18w)`
    \\ ASM_SIMP_TAC std_ss [builtin_symbols_def,APPEND]
    \\ ONCE_REWRITE_TAC [symbol_table_def]
    \\ SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_SUB_SUB,
         WORD_ADD_0,WORD_SUB_RZERO])
  \\ ASM_SIMP_TAC std_ss []
  \\ `(token_slots (r5 - 0x20w) 5 *
       token_slots (r5 + 0x8w + n2w (8 * ll)) (l + l + 2 - ll) *
       lisp_exp (string2sexp (sexp2string s)) r7i (sa,xi) *
        SEP_FILL (sa,xi)) (fun2set (h3,dh))` by
    (Q.PAT_X_ASSUM `ppp (fun2set (hi,dh))` MP_TAC \\ Q.UNABBREV_TAC `h3`
     \\ REPEAT (POP_ASSUM (K ALL_TAC))
     \\ SIMP_TAC std_ss [arm_tokens4_def,arm_tokens2_def,SEP_CLAUSES]
     \\ REWRITE_TAC [DECIDE ``5 = SUC 0 + 3 + SUC 0:num``]
     \\ REWRITE_TAC [token_slots_ADD,token_slots_def]
     \\ SIMP_TAC std_ss [WORD_SUB_ADD,SEP_CLAUSES]
     \\ SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3,SEP_EXISTS]
     \\ REPEAT STRIP_TAC
     \\ Q.EXISTS_TAC `r5 + n2w (8 * ll) + 0x8w`
     \\ Q.EXISTS_TAC `r5 + n2w (l * 8) + 0x8w`
     \\ Q.EXISTS_TAC `n2w (l * 8)`
     \\ Q.EXISTS_TAC `1w`
     \\ SEP_WRITE_TAC)
  \\ `(lisp_exp (string2sexp (sexp2string s)) r7i (sa,xi) *
       SEP_FILL (sa,xi)) (fun2set (h3,dh
        DIFF ch_active_set2 (r5 - 0x20w,0,5)
        DIFF ch_active_set2 (r5 + 0x8w + n2w (8 * ll),0,l + l + 2 - ll)))` by
   (MATCH_MP_TAC fun2set_DIFF_IMP
    \\ Q.EXISTS_TAC `token_slots (r5 + 0x8w + n2w (8 * ll)) (l + l + 2 - ll)`
    \\ STRIP_TAC THEN1
     (REPEAT STRIP_TAC
      \\ IMP_RES_TAC token_slots_IMP
      \\ FULL_SIMP_TAC std_ss [ch_active_set2_def])
    \\ MATCH_MP_TAC fun2set_DIFF_IMP
    \\ Q.EXISTS_TAC `token_slots (r5 - 0x20w) 5`
    \\ ASM_SIMP_TAC std_ss [STAR_ASSOC]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC token_slots_IMP
    \\ FULL_SIMP_TAC std_ss [ch_active_set2_def])
  \\ `dh DIFF ch_active_set2 (r5 - 0x20w,0,5) DIFF
              ch_active_set2 (r5 + 0x8w + n2w (8 * ll),0,l + l + 2 - ll) =
      ch_active_set2 (r5 + 0x8w,0,ll)` by
   (IMP_RES_TAC token_slots_IMP
    \\ ASM_SIMP_TAC std_ss []
    \\ NTAC 24 (POP_ASSUM (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss [ch_active_set2_def]
    \\ SIMP_TAC std_ss [ch_active_set_4]
    \\ `{r5 - 0x20w + n2w (4 * i) | i < 2 * (l + l + 7)} DIFF
        {r5 - 0x20w + n2w (4 * i) | i < 10} =
        {r5 + 0x8w + n2w (4 * i) | i < 2 * (l + l + 2)}` by
     (SIMP_TAC std_ss [EXTENSION,IN_DIFF,GSPECIFICATION]
      \\ REVERSE (REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC)
      \\ ASM_SIMP_TAC std_ss [] THENL [
        SIMP_TAC std_ss [GSYM WORD_ADD_SUB_SYM,WORD_EQ_SUB_LADD]
        \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
        \\ SIMP_TAC std_ss [word_add_n2w,ADD_ASSOC]
        \\ `8 + 4 * i + 32 < 4294967296` by DECIDE_TAC
        \\ Cases_on `i' < 10` \\ ASM_SIMP_TAC std_ss []
        \\ `4 * i' < 4294967296` by DECIDE_TAC
        \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC,
        SIMP_TAC std_ss [GSYM WORD_ADD_SUB_SYM,WORD_EQ_SUB_LADD]
        \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
        \\ SIMP_TAC std_ss [word_add_n2w,ADD_ASSOC]
        \\ Q.EXISTS_TAC `2 + i + 8`
        \\ ASM_SIMP_TAC std_ss [LEFT_ADD_DISTRIB] \\ DECIDE_TAC,
        REPEAT (Q.PAT_X_ASSUM `!x.bbb` MP_TAC)
        \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL]
        \\ SIMP_TAC std_ss [GSYM WORD_ADD_SUB_SYM,WORD_EQ_SUB_RADD]
        \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
        \\ REWRITE_TAC [METIS_PROVE [] ``b \/ ~c = c ==> b``]
        \\ REPEAT STRIP_TAC
        \\ Cases_on `i < 10` THEN1 (RES_TAC \\ FULL_SIMP_TAC std_ss [])
        \\ Q.EXISTS_TAC `i - 10`
        \\ ASM_SIMP_TAC std_ss [LEFT_SUB_DISTRIB]
        \\ `8 + (4 * i - 40) + 32 = 4 * i` by DECIDE_TAC
        \\ ASM_SIMP_TAC std_ss [word_add_n2w,ADD_ASSOC] \\ DECIDE_TAC])
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [EXTENSION,IN_DIFF,GSPECIFICATION]
    \\ REVERSE (REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC)
    \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, WORD_EQ_ADD_CANCEL]
    THENL [
      SIMP_TAC std_ss [word_add_n2w]
      \\ REWRITE_TAC [METIS_PROVE [] ``b \/ ~c = c ==> b``]
      \\ STRIP_TAC
      \\ `8 * ll + 4 * i' < 4294967296 /\ 4 * i < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC,
      Q.EXISTS_TAC `i` \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC,
      Q.EXISTS_TAC `i` \\ ASM_SIMP_TAC std_ss []
      \\ POP_ASSUM MP_TAC
      \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, WORD_EQ_ADD_CANCEL]
      \\ REWRITE_TAC [METIS_PROVE [] ``b \/ ~c = c ==> b``]
      \\ SIMP_TAC std_ss [word_add_n2w] \\ STRIP_TAC
      \\ CCONTR_TAC
      \\ `i - 2 * ll < 2 * (l + l + 2 - ll)` by DECIDE_TAC
      \\ RES_TAC
      \\ `8 * ll + 4 * (i - 2 * ll) = 4 * i` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss []])
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC)
  \\ `SEP_FILL (sa,xi) (fun2set (h3,ch_active_set2 (r5 + 0x8w,0,ll)))` by
   (POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss [SEP_FILL_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS] \\ STRIP_TAC
    \\ METIS_TAC [SEP_EXPS_def])
  \\ IMP_RES_TAC string2sexp_sexp2string
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 METIS_TAC [IMP_lisp_x]
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM MP_TAC
  \\ Q.PAT_X_ASSUM `ALIGNED8 (sa - r5)` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ STRIP_TAC
  \\ `ch_active_set (r5,1,1 + ll) =
       { y | y IN ch_active_set2 (r5 + 0x8w,0,ll) /\ ALIGNED8 (sa - y) }` by
   (SIMP_TAC std_ss [ch_active_set2_def]
    \\ SIMP_TAC std_ss [IN_UNION,METIS_PROVE []
         ``(b1 \/ b2) /\ b = b /\ b1 \/ b /\ b2``]
    \\ `!y. ALIGNED8 (sa - y) /\ y IN ch_active_set (r5 + 0x8w + 0x4w,0,ll) = F` by
     (STRIP_TAC \\ Cases_on `y IN ch_active_set (r5 + 0x8w + 0x4w,0,ll)`
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [ch_active_set_def,GSPECIFICATION]
      \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,word_mul_n2w]
      \\ REWRITE_TAC [DECIDE ``8 + (4 + 8 * j) = 4 + 8 * (j + 1:num)``]
      \\ SIMP_TAC std_ss [WORD_SUB_PLUS,GSYM word_add_n2w,ALIGNED8_SUB]
      \\ FULL_SIMP_TAC std_ss [ALIGNED8_ADD_EQ,word_sub_def] \\ EVAL_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,ch_active_set_def]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss []
    THEN1 ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,word_mul_n2w,ALIGNED8_SUB]
    THENL [
      Q.EXISTS_TAC `j - 1`
      \\ `8 + 8 * (j - 1) = 8 * j` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_mul_n2w,word_add_n2w]
      \\ DECIDE_TAC,
      Q.EXISTS_TAC `SUC j`
      \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_mul_n2w,word_add_n2w,
                              MULT_CLAUSES] \\ DECIDE_TAC])
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC SEP_EXPS_ok_data
  \\ FULL_SIMP_TAC std_ss [SEP_FILL_def,SEP_EXISTS]
  THENL [
    Q.EXISTS_TAC `y` \\ Q.EXISTS_TAC `xi`
    \\ Q.EXISTS_TAC `ch_active_set2 (r5 + 0x8w,0,ll)`
    \\ ASM_SIMP_TAC std_ss [SUBSET_REFL]
    \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [GSPECIFICATION],
    Q.EXISTS_TAC `y` \\ Q.EXISTS_TAC `xi`
    \\ Q.EXISTS_TAC `ch_active_set2 (r5 + 0x8w,0,ll)`
    \\ ASM_SIMP_TAC std_ss [SUBSET_REFL]
    \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [GSPECIFICATION,ch_active_set2_def,
          ch_active_set_def,IN_UNION]
    \\ REPEAT STRIP_TAC \\ DISJ2_TAC
    \\ Q.EXISTS_TAC `j - 1`
    \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
    \\ `8 + (4 + 8 * (j - 1)) = 8 * j + 4`by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_mul_n2w]
    \\ DECIDE_TAC]);


(* formulating the final theorem *)

open lisp_opsTheory;

val aSTRING_def = Define `
  aSTRING a str = SEP_EXISTS df f. aBYTE_MEMORY df f *
                    cond (string_mem (STRCAT str null_string) (a,f,df))`;

val pSTRING_def = Define `
  pSTRING a str = SEP_EXISTS df f. pBYTE_MEMORY df f *
                    cond (string_mem (STRCAT str null_string) (a,f,df))`;

val xSTRING_def = Define `
  xSTRING a str = SEP_EXISTS df f. xBYTE_MEMORY df f *
                    cond (string_mem (STRCAT str null_string) (a,f,df))`;

fun AUTO_EXISTS_TAC (asm,tm) = let
    fun ex tm = let
      val (v,tm) = dest_exists tm
      in v :: ex tm end handle e => []
    val xs = ex tm
    val x = hd (list_dest dest_conj (repeat (snd o dest_exists) tm))
    val assum = [``lisp_inv (Dot x1 x2,x2,x3,x4,x5,x6,limit)
      (w1,w2,w3,w4,w5,w6,a',x',xs',s,dm,m,dg,g)``,
     ``lisp_inv (x1,x2,x3,x4,x5,x6,limit)
      (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g)``]
     val tm2 = hd (filter (can (match_term x)) asm)
     val (s,_) = match_term x tm2
     val ys = map (subst s) xs
     fun exx [] = ALL_TAC | exx (x::xs) = EXISTS_TAC x THEN exx xs
     in exx ys (asm,tm) end

fun store_string2sexp_thm target extra post = let
  fun get_thm s [] = fail()
    | get_thm s ((t,th)::xs) = if s = t then th else get_thm s xs
  val th = get_thm target arm_string2sexp_thms
  val p = find_term (can (match_term ``aPC p``)) (cdr (concl th)) handle e =>
          find_term (can (match_term ``pPC p``)) (cdr (concl th)) handle e =>
          find_term (can (match_term ``xPC p``)) (cdr (concl th))
  val p = cdr p
  val post = subst [mk_var("p",``:word32``) |-> p] post
  val imp = arm_string2sexp_lemma
  val tm = (cdr o car o concl) imp
  val s = INST (map (fn (x,y) => mk_var(y,``:word32``) |-> mk_var("r"^x,``:word32``))
            [("3","eax"),("4","ecx"),("5","edx"),("6","ebx"),
             ("7","edi"),("8","esi"),("9","ebp")])
  val s = Q.INST [`r4`|->`n2w l`] o s
  val s = MATCH_MP progTheory.SPEC_FRAME o s
  val s = SPEC tm o Q.GEN `c` o Q.SPEC `cond c` o s
  val s = MATCH_MP progTheory.SPEC_FRAME o s
  val s = Q.SPEC extra o s
  val s = MATCH_MP progTheory.SPEC_WEAKEN o s
  val th = s th
  val th = SPEC post th
  val tm = (cdr o car o concl) th
  val tac =
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND]
    THEN REPEAT STRIP_TAC
    THEN (STRIP_ASSUME_TAC o UNDISCH_ALL o
          REWRITE_RULE [GSYM AND_IMP_INTRO] o
          SIMP_RULE std_ss []) imp
    THEN ASM_SIMP_TAC std_ss [LET_DEF,aSTRING_def,pSTRING_def,xSTRING_def,SEP_CLAUSES]
    THEN REWRITE_TAC [aLISP_def,pLISP_def,xLISP_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_def,STAR_ASSOC]
    THEN SIMP_TAC (std_ss++sep_cond_ss) []
    THEN SIMP_TAC (std_ss) [cond_STAR,SEP_EXISTS]
    THEN REPEAT STRIP_TAC
    THEN Q.EXISTS_TAC `df`
    THEN Q.EXISTS_TAC `f`
    THEN AUTO_EXISTS_TAC
    THEN FULL_SIMP_TAC std_ss [AC STAR_COMM STAR_ASSOC]
  val thi = TAC_PROOF(([], tm),tac)
  val th = MP th thi
  val th = DISCH_ALL th
  val th = SIMP_RULE (std_ss++sep_cond_ss) [progTheory.SPEC_MOVE_COND,AND_IMP_INTRO,SEP_CLAUSES] th
  val tm = (cdr o car o concl) th
  val tm2 = (cdr o car o concl) imp
  val tm3 = mk_imp(tm2,tm)
  val tac =
    SIMP_TAC std_ss []
    THEN REPEAT STRIP_TAC
    THEN (STRIP_ASSUME_TAC o UNDISCH_ALL o
          REWRITE_RULE [GSYM AND_IMP_INTRO] o
          SIMP_RULE std_ss []) imp
    THEN ASM_SIMP_TAC std_ss []
  val thi = prove(tm3,tac)
  val th = DISCH_ALL (MP th (UNDISCH thi))
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND] th
  val _ = save_thm("arm_string2sexp_" ^ target ^ "_thm",th)
  in th end;

val th = store_string2sexp_thm "arm" `emp`
  ``aLISP (s,Sym "nil",Sym "nil",Sym "nil",Sym "nil",Sym "nil",l) *
    ~aR 0x0w * aSTRING r3 (sexp2string s) * aPC p * ~aS``

val th = store_string2sexp_thm "ppc" `~pR 0x2w`
  ``pLISP (s,Sym "nil",Sym "nil",Sym "nil",Sym "nil",Sym "nil",l) *
    pSTRING r3 (sexp2string s) * pPC p * ~pS``

val th = store_string2sexp_thm "x86" `emp`
  ``xLISP (s,Sym "nil",Sym "nil",Sym "nil",Sym "nil",Sym "nil",l) *
    xSTRING r3 (sexp2string s) * xPC p * ~xS``


val _ = export_theory();
