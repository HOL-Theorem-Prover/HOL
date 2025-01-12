
open HolKernel boolLib bossLib Parse;
open decompilerLib prog_x86Lib;

val decompile_x86 = decompile x86_tools

open pred_setTheory arithmeticTheory pairTheory listTheory wordsTheory;
open addressTheory set_sepTheory progTheory prog_x86Theory;
open wordsLib x86_encodeLib helperLib;

open jit_inputTheory jit_opsTheory;

open compilerLib;
open export_codeLib;

val _ = new_theory "jit_codegen";


(* compiler setup code *)

(* val _ = set_x86_exec_flag false; *)

(* make function "f" have exec permissions *)
val _ = add_executable_data_name "f"

(* assign meanings to r1, r2, r3, r4 etc *)
val _ = codegen_x86Lib.set_x86_regs
  [(1,"eax"),(6,"ebx"),(5,"ecx"),(2,"edx"),(3,"edi"),(4,"esi"),(7,"ebp")]

val dec_byte = let
  val (th1,th2) = decompile_x86 "dec_byte"
    [QUOTE (x86_encodeLib.x86_encode "DEC BYTE [eax]" ^ "/f")]
  in SIMP_RULE std_ss [th2,LET_DEF] th1 end

val _ = codegenLib.add_compiled [dec_byte];


(*

r1 = pointer to generated code
r2 = pointer to byte code instr
r3 = pointer to start of byte code
r4 = pointer to start of generated code
r5 = temp
r6 = temp
r7 = pointer to initial stack

*)


val (th1,x86_istop_def,x86_istop_pre_def) = compile "x86" ``
  (x86_isub (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 =+ 0x2Bw) f in
    let f = (r1 + 1w =+ 0x07w) f in
    let r1 = r1 + 2w in
      (r1,df,f)) /\
  (x86_iswap (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 =+ 0x87w) f in
    let f = (r1 + 1w =+ 0x07w) f in
    let r1 = r1 + 2w in
      (r1,df,f)) /\
  (x86_ipop (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 =+ 0x8Bw) f in
    let f = (r1 + 1w =+ 0x07w) f in
    let f = (r1 + 2w =+ 0x83w) f in
    let f = (r1 + 3w =+ 0xC7w) f in
    let f = (r1 + 4w =+ 0x04w) f in
    let r1 = r1 + 5w in
      (r1,df,f)) /\
  (x86_ipush (r1:word32,r6:word32,df:word32 set,f:word32->word8) =
    let f = (r1 =+ 0x83w) f in
    let f = (r1 + 1w =+ 0xEFw) f in
    let f = (r1 + 2w =+ 0x04w) f in
    let f = (r1 + 3w =+ 0x89w) f in
    let f = (r1 + 4w =+ 0x07w) f in
    let f = (r1 + 5w =+ 0xB8w) f in
    let f = (r1 + 6w =+ w2w r6) f in
    let f = (r1 + 7w =+ 0x00w) f in
    let f = (r1 + 8w =+ 0x00w) f in
    let f = (r1 + 9w =+ 0x00w) f in
    let r1 = r1 + 10w in
      (r1,df,f)) /\
  (x86_istop (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 =+ 0xFFw) f in
    let f = (r1 + 1w =+ 0xE2w) f in
    let r1 = r1 + 2w in
      (r1,df,f)) /\
  (x86_ijump (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 =+ 0xE9w) f in
    let r5 = 5w:word32 in
      (r1,r5,df,f)) /\
  (x86_ijeq (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 + 3w =+ 0x84w) f in
    let r5 = 8w:word32 in
      (r1,r5,df,f)) /\
  (x86_ijlt (r1:word32,df:word32 set,f:word32->word8) =
    let f = (r1 + 3w =+ 0x82w) f in
    let r5 = 8w:word32 in
      (r1,r5,df,f))``

fun ord_eval tm = let
  val tms = find_terml (can (match_term ``n2w (ORD c):'a word``)) tm
  in (snd o dest_eq o concl o REWRITE_CONV (map EVAL tms)) tm end

val (th1,x86_codegen_jump_op_def,x86_codegen_jump_op_pre_def) = (compile "x86" o ord_eval) ``
  x86_codegen_jump_op (r1:word32,r5:word32,df,f) =
    if r5 = n2w (ORD #"j") then
      let (r1,r5,df,f) = x86_ijump (r1,df,f) in (r1,r5,df,f)
    else
      let f = (r1 =+ 0x3Bw) f in
      let f = (r1 + 1w =+ 0x07w) f in
      let f = (r1 + 2w =+ 0x0Fw) f in
        if r5 = n2w (ORD #"=") then
          let (r1,r5,df,f) = x86_ijeq (r1,df,f) in (r1,r5,df,f)
        else
          let (r1,r5,df,f) = x86_ijlt (r1,df,f) in (r1,r5,df,f)``;

(* r6 - pointer to bytecode, r5 - address in generated code *)
val (th1,x86_addr_def,x86_addr_pre_def) = (compile "x86" o ord_eval) ``
  x86_addr (r1:word32,r5:word32,r6:word32,df:word32 set,f:word32->word8,dg:word32 set,g:word32->word8) =
    if f r1 = 0w then (r1,r5,df,f,dg,g) else
      let f = (r1 =+ f r1 - 1w) f in
        if (g r6 = n2w (ORD #"-")) \/ (g r6 = n2w (ORD #"s")) \/ (g r6 = n2w (ORD #"."))
        then let r6 = r6 + 1w in let r5 = r5 + 2w in x86_addr (r1,r5,r6,df,f,dg,g) else
        if g r6 = n2w (ORD #"p") then let r6 = r6 + 1w in let r5 = r5 + 5w in x86_addr (r1,r5,r6,df,f,dg,g) else
        if g r6 = n2w (ORD #"c") then let r6 = r6 + 2w in let r5 = r5 + 10w in x86_addr (r1,r5,r6,df,f,dg,g) else
        if g r6 = n2w (ORD #"j") then let r6 = r6 + 2w in let r5 = r5 + 5w in x86_addr (r1,r5,r6,df,f,dg,g) else
        if (g r6 = n2w (ORD #"=")) \/ (g r6 = n2w (ORD #"<")) then let r6 = r6 + 2w in let r5 = r5 + 8w in x86_addr (r1,r5,r6,df,f,dg,g) else
          (r1,r5,df,f,dg,g)``;

val (th1,x86_codegen_jumps_def,x86_codegen_jumps_pre_def) = compile "x86" ``
  x86_codegen_jumps (r1,r2,r3,r4,r5,df,f,dg,g) =
    let (r1,r5,df,f) = x86_codegen_jump_op (r1,r5,df,f) in
    let r1 = r1 + r5 in
    let r5 = r4 in
    let r6 = (w2w (g r2)):word32 in
    let r1 = r1 - 1w in
    let r6 = r6 - 48w in
    let f = (r1 =+ w2w r6) f in
    let r6 = r3 in
    let (r1,r5,df,f,dg,g) = x86_addr (r1,r5,r6,df,f,dg,g) in
    (* store offset *)
    let r1 = r1 + 1w in
    let r5 = r5 - r1 in
    let f = (r1 - 4w =+ w2w r5) f in
    let r5 = r5 >>> 8 in
    let f = (r1 - 3w =+ w2w r5) f in
    let r5 = r5 >>> 8 in
    let f = (r1 - 2w =+ w2w r5) f in
    let r5 = r5 >>> 8 in
    let f = (r1 - 1w =+ w2w r5) f in
      (r1,r2,r3,r4,df,f,dg,g)``

val (th1,x86_codegen_loop_def,x86_codegen_loop_pre_def) = (compile "x86" o ord_eval) ``
  x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g) =
    let r5 = (w2w (g r2)):word32 in
    let r2 = r2 + 1w in
      if r5 = 0w then
        (r4,df,f,dg,g)
      else if r5 = n2w (ORD #"-") then
        let (r1,df,f) = x86_isub (r1,df,f) in
          x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g)
      else if r5 = n2w (ORD #"s") then
        let (r1,df,f) = x86_iswap (r1,df,f) in
          x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g)
      else if r5 = n2w (ORD #"p") then
        let (r1,df,f) = x86_ipop (r1,df,f) in
          x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g)
      else if r5 = n2w (ORD #"c") then
        let r6 = (w2w (g r2)):word32 in
        let r2 = r2 + 1w in
        let r6 = r6 - 48w in
        let (r1,df,f) = x86_ipush (r1,r6,df,f) in
          x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g)
      else if r5 = n2w (ORD #".") then
        let (r1,df,f) = x86_istop (r1,df,f) in
          x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g)
      else (* must be a jump of some kind *)
        let (r1,r2,r3,r4,df,f,dg,g) = x86_codegen_jumps (r1,r2,r3,r4,r5,df,f,dg,g) in
        let r2 = r2 + 1w in
          x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g)``

val (x86_codegen_th,x86_codegen_def,x86_codegen_pre_def) = compile "x86" ``
  x86_codegen (r1,r2,df,f,dg,g) =
    let r3 = r2 in
    let r4 = r1 in
    let (r4,df,f,dg,g) = x86_codegen_loop (r1,r2,r3,r4,df,f,dg,g) in
      (r4,df,f,dg,g)``;

val SEP_BYTES_IN_MEM_def = Define `
  (SEP_BYTES_IN_MEM a [] = emp) /\
  (SEP_BYTES_IN_MEM a (x::xs) = one (a,x) * SEP_BYTES_IN_MEM (a+1w) xs)`;

val SEP_CODE_IN_MEM_LOOP_def = Define `
  (SEP_CODE_IN_MEM_LOOP a [] (a1,ns1) = emp) /\
  (SEP_CODE_IN_MEM_LOOP a (n::ns) (a1,ns1) =
     let branch j = ADDR ns1 a1 j - a in
     let xs = X86_ENCODE branch n in
       SEP_BYTES_IN_MEM a xs * SEP_CODE_IN_MEM_LOOP (a + n2w (LENGTH xs)) ns (a1,ns1))`;

val SEP_CODE_IN_MEM_def = Define `
  SEP_CODE_IN_MEM a ns = SEP_CODE_IN_MEM_LOOP a ns (a,ns)`;

val CODE_LENGTH_def = Define `
  (CODE_LENGTH [] = 0) /\
  (CODE_LENGTH (n::ns) = LENGTH (X86_ENCODE (\x.0w) n) + CODE_LENGTH ns)`;

val one_list_def = Define `
  (one_list a [] b = cond (b = a)) /\
  (one_list a (x::xs) b = one (a,x) * one_list (a + 1w) xs b)`;

val one_space_def = Define `
  (one_space a 0 b = cond (b = a)) /\
  (one_space a (SUC n) b = SEP_EXISTS y. one (a,y) * one_space (a + 1w) n b)`;

val one_string_def = Define `
  one_string a (s:string) b = one_list a (MAP (n2w o ORD) s) b`;

val one_string_0_def = Define `
  one_string_0 a (s:string) b = one_string a (s ++ [CHR 0]) b`;

val one_string_STRCAT = store_thm("one_string_STRCAT",
  ``!s t a c.
      one_string a (s ++ t) c =
      one_string a s (a + n2w (LENGTH s)) *
      one_string (a + n2w (LENGTH s)) t c``,
  Induct
  \\ FULL_SIMP_TAC std_ss [one_string_def,WORD_ADD_0,SEP_CLAUSES,
       ADD,MAP,LENGTH,one_list_def,APPEND]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w]
  \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,STAR_ASSOC]);

val one_string_0_STRCAT = store_thm("one_string_0_STRCAT",
  ``!s t a c.
      one_string_0 a (s ++ t) c =
      one_string a s (a + n2w (LENGTH s)) *
      one_string_0 (a + n2w (LENGTH s)) t c``,
  SIMP_TAC std_ss [one_string_0_def,GSYM APPEND_ASSOC]
  \\ REWRITE_TAC [one_string_STRCAT]);

val one_space_ADD = store_thm("one_space_ADD",
  ``!m n a c.
      one_space a (m + n) c =
      one_space a m (a + n2w m) *
      one_space (a + n2w m) n c``,
  Induct
  \\ ASM_SIMP_TAC std_ss [one_space_def,WORD_ADD_0,SEP_CLAUSES,ADD]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w]
  \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,STAR_ASSOC]);

val LENGTH_X86_ENCODE = prove(
  ``!n b. LENGTH (X86_ENCODE b n) = LENGTH (X86_ENCODE (\x.0w) n)``,
  Cases THEN SIMP_TAC std_ss [LENGTH,X86_ENCODE_def,X86_IMMEDIATE_def,APPEND]);

fun TRY_TAC t goal = t goal handle e => ALL_TAC goal;

val x86_addr_thm = prove(
  ``!y ns r x b2 f df r1 r5 r6.
      (r * one_string_0 r6 (iENCODE ns) b1) (fun2set (g,dg)) /\
      (x * one (r1,n2w y)) (fun2set (f,df)) /\ y < 256 ==>
      ?fi z. x86_addr_pre (r1,r5,r6,df,f,dg,g) /\
             (x86_addr (r1,r5,r6,df,f,dg,g) = (r1,ADDR ns r5 y,df,fi,dg,g)) /\
             (x * one (r1,z)) (fun2set (fi,df))``,
  SIMP_TAC std_ss [] \\ Induct THEN1
   (ONCE_REWRITE_TAC [x86_addr_def,x86_addr_pre_def]
    \\ REPEAT STRIP_TAC \\ Cases_on `ns`
    \\ `(f r1 = 0w) /\ (r1 IN df)` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [ADDR_def,LET_DEF] \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [x86_addr_def,x86_addr_pre_def]
  \\ `(f r1 = n2w (SUC y)) /\ r1 IN df` by SEP_READ_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC std_ss [WORD_ADD_SUB,ADD1,GSYM word_add_n2w]
  \\ Q.ABBREV_TAC `f2 = (r1 =+ n2w y) f`
  \\ `(x * one (r1,n2w y)) (fun2set (f2,df))` by
        (Q.UNABBREV_TAC `f2` \\ SEP_WRITE_TAC)
  \\ Cases_on `ns` THEN1
   (FULL_SIMP_TAC (std_ss++sep_cond_ss) [ADDR_def,GSYM ADD1,iENCODE_def,
      one_string_0_def,APPEND,one_string_def,MAP,one_list_def,cond_STAR,
      stringTheory.ORD_CHR_RWT]
    \\ `r6 IN dg /\ (g r6 = 0w)` by SEP_READ_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [LENGTH,iENCODE_def,one_string_0_STRCAT,LET_DEF]
  \\ `y < 256` by DECIDE_TAC
  \\ REWRITE_TAC [GSYM ADD1,ADDR_def,TL,HD]
  \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [iENCODE1_def,LENGTH,one_string_def,MAP,APPEND,
       STAR_ASSOC,one_list_def,SEP_CLAUSES,stringTheory.ORD_CHR_RWT,
       iIMM_def,word_arith_lemma1]
  \\ `r6 IN dg` by SEP_READ_TAC
  \\ TRY_TAC (`g r6 = 0x2Dw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x20w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x73w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x70w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x2Ew` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x63w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x6Aw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x3Dw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x3Cw` by SEP_READ_TAC)
  \\ ASM_SIMP_TAC std_ss [xENC_LENGTH_def,X86_ENCODE_def,LENGTH,X86_IMMEDIATE_def,APPEND]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ ASSUME_TAC (Q.SPEC `c` (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:7``] w2n_lt)))
  \\ `48 + w2n c < 256` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [stringTheory.ORD_CHR_RWT]
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x2Dw)`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x73w)`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x2Ew)`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x70w)`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x63w) * one (r6 + 0x1w,n2w (48 + w2n c))`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x6Aw) * one (r6 + 0x1w,n2w (48 + w2n c))`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x3Dw) * one (r6 + 0x1w,n2w (48 + w2n c))`
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (Q.PAT_ASSUM `!ns.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `r * one (r6,0x3Cw) * one (r6 + 0x1w,n2w (48 + w2n c))`
    \\ ASM_SIMP_TAC std_ss []));

val w2w_w2w_n2w_lemma = prove(
  ``!c:word7. w2w (w2w ((n2w (48 + w2n c)):word8) - 0x30w:word32) =
              (n2w (w2n c)):word8``,
  Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ `48 + n < 256` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ `n < 2**32` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]);

val x86_codegen_loop_lemma = prove(
  ``!ns r x a r2 df f dg g b1 b2 y a1 r3 r4.
      (y * one_string_0 r3 (iENCODE ns1) b1) (fun2set (g,dg)) /\
      (x * one_string_0 r2 (iENCODE ns) b1) (fun2set (g,dg)) /\
      (r * one_space a (CODE_LENGTH ns) b2) (fun2set (f,df)) ==>
      ?fi.
        x86_codegen_loop_pre (a,r2,r3,r4,df,f,dg,g) /\
        (x86_codegen_loop (a,r2,r3,r4,df,f,dg,g) = (r4,df,fi,dg,g)) /\
        (r * SEP_CODE_IN_MEM_LOOP a ns (r4,ns1)) (fun2set (fi,df))``,
  Induct THEN1
   (SIMP_TAC std_ss [SEP_CODE_IN_MEM_LOOP_def,CODE_LENGTH_def,iENCODE_def,
      one_string_0_def,APPEND,one_space_def,one_string_def,one_list_def,MAP]
    \\ SIMP_TAC std_ss [EVAL ``ORD (CHR 0)``,cond_STAR]
    \\ REPEAT STRIP_TAC
    \\ `(g r2 = 0w) /\ r2 IN dg` by SEP_READ_TAC
    \\ ONCE_REWRITE_TAC [x86_codegen_loop_pre_def,x86_codegen_loop_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,SEP_CLAUSES])
  \\ SIMP_TAC std_ss [iENCODE_def,CODE_LENGTH_def,one_string_0_STRCAT]
  \\ SIMP_TAC std_ss [SEP_CODE_IN_MEM_LOOP_def,LET_DEF,one_space_ADD,STAR_ASSOC]
  \\ SIMP_TAC std_ss [LENGTH_X86_ENCODE]
  \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `r2j = r2 + n2w (STRLEN (iENCODE1 h))`
  \\ Cases_on `h`
  \\ FULL_SIMP_TAC bool_ss [SEP_BYTES_IN_MEM_def,X86_ENCODE_def,STAR_ASSOC,
       SEP_CLAUSES,iENCODE1_def,one_string_def,MAP,one_list_def,cond_STAR,
       LENGTH,APPEND,X86_IMMEDIATE_def,one_space_def]
  \\ FULL_SIMP_TAC std_ss [stringTheory.ORD_CHR_RWT,word_arith_lemma1,
       SEP_CLAUSES,SEP_EXISTS]
  \\ Q.PAT_ASSUM `pp (fun2set (g,dg))` MP_TAC
  \\ REWRITE_TAC [GSYM STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ STRIP_TAC \\ IMP_RES_TAC read_fun2set
  \\ Q.PAT_ASSUM `pp (fun2set (g,dg))` MP_TAC
  \\ REWRITE_TAC [STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ REWRITE_TAC [STAR_ASSOC]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [x86_codegen_loop_def,x86_codegen_loop_pre_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11,
       x86_istop_def,x86_istop_pre_def]
  \\ TRY_TAC (`a IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+1w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+2w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+3w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+4w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+5w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+6w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+7w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+8w IN df` by SEP_READ_TAC)
  \\ TRY_TAC (`a+9w IN df` by SEP_READ_TAC)
  \\ ASM_SIMP_TAC std_ss []
  THEN1
   (Q.PAT_ASSUM `!xx. bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x2Dw)`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2`
    \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (Q.PAT_ASSUM `!xx. bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x73w)`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2`
    \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (Q.PAT_ASSUM `!xx. bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x2Ew)`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2`
    \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (Q.PAT_ASSUM `!xx. bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x70w)`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2`
    \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (FULL_SIMP_TAC (std_ss++sep_cond_ss) [iIMM_def,stringTheory.ORD_CHR_RWT,MAP,
      one_list_def,STAR_ASSOC]
    \\ `r2 + 0x1w IN dg` by SEP_READ_TAC
    \\ `g (r2 + 1w) = n2w (ORD (CHR (48 + w2n c)))` by SEP_READ_TAC
    \\ ASSUME_TAC (Q.SPEC `c` (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:7``] w2n_lt)))
    \\ `48 + w2n c < 256` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,w2w_w2w_n2w_lemma,GSYM w2w_def,stringTheory.ORD_CHR_RWT]
    \\ Q.PAT_ASSUM `!xx. bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x63w) * one (r2 + 0x1w,n2w (48 + w2n c))`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2`
    \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [cond_STAR]
    \\ Q.PAT_ASSUM `r2j = r2 + 2w` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  \\ SIMP_TAC (std_ss++SIZES_ss) [x86_codegen_jumps_def,
       x86_codegen_jumps_pre_def,LET_DEF,x86_codegen_jump_op_pre_def,
       x86_codegen_jump_op_def,n2w_11,x86_istop_def,x86_istop_pre_def]
  \\ SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma2]
  \\ SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,w2w_eq_n2w]
  \\ Q.UNABBREV_TAC `r2j`
  \\ FULL_SIMP_TAC std_ss [iIMM_def,MAP,one_list_def,LENGTH,
       word_arith_lemma1,SEP_CLAUSES,EVAL ``ORD #"0"``]
  \\ ASSUME_TAC (Q.SPEC `c` (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:7``] w2n_lt)))
  \\ `48 + w2n c < 256` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [stringTheory.ORD_CHR_RWT]
  THEN1
   (`(g (r2 + 0x1w) = n2w (48 + w2n c)) /\ r2 + 0x1w IN dg` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [w2w_w2w_n2w_lemma]
    \\ Q.ABBREV_TAC `f2 = (a + 0x4w =+ n2w (w2n c)) ((a =+ 0xE9w) f)`
    \\ `w2n c < 256` by DECIDE_TAC
    \\ `(r * one (a,0xE9w) * one (a + 0x1w,y'') * one (a + 0x2w,y''') *
         one (a + 0x3w,y'''') * one_space (a + 0x5w) (CODE_LENGTH ns) b2 *
         one (a + 0x4w,n2w (w2n (c:word7)))) (fun2set (f2,df))` by
           (Q.UNABBREV_TAC `f2` \\ SEP_WRITE_TAC)
    \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.SPECL [`w2n (c:word7)`,`ns1`,`y`,
         `r * one (a,0xE9w) * one (a + 0x1w,y'') *
         one (a + 0x2w,y''') * one (a + 0x3w,y'''') *
         one_space (a + 0x5w) (CODE_LENGTH ns) b2`,
         `b2`,`f2`,`df`,`a+4w`,`r4`,`r3`]) x86_addr_thm
    \\ ASM_SIMP_TAC std_ss [GSYM w2w_def,word_arith_lemma1]
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.ABBREV_TAC `imm = ADDR ns1 r4 (w2n c) - a - 0x5w`
    \\ SIMP_TAC std_ss [LSR_ADD,WORD_ADD_0,word_arith_lemma3,word_arith_lemma4]
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!xx.bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x6Aw) * one (r2 + 0x1w,n2w (48 + w2n (c:word7)))`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2` \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  THEN1
   (`(g (r2 + 0x1w) = n2w (48 + w2n c)) /\ r2 + 0x1w IN dg` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [w2w_w2w_n2w_lemma]
    \\ Q.PAT_ABBREV_TAC `f2 = (a + 0x7w =+ (n2w (w2n (c:word7))):word8) ff`
    \\ `w2n c < 256` by DECIDE_TAC
    \\ `(r * one (a,0x3Bw) * one (a + 0x1w,7w) * one (a + 0x2w,0xFw) *
         one (a + 0x3w,0x84w) * one (a + 0x4w,y''''') *
         one (a + 0x5w,y'''''') * one (a + 0x6w,y''''''') *
         one_space (a + 0x8w) (CODE_LENGTH ns) b2 *
         one (a + 0x7w,n2w (w2n (c:word7)))) (fun2set (f2,df))` by
           (Q.UNABBREV_TAC `f2` \\ SEP_WRITE_TAC)
    \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.SPECL [`w2n (c:word7)`,`ns1`,`y`,
         `r * one (a,0x3Bw) * one (a + 0x1w,0x7w) * one (a + 0x2w,0xFw) *
        one (a + 0x3w,0x84w) * one (a + 0x4w,y''''') *
        one (a + 0x5w,y'''''') * one (a + 0x6w,y''''''') *
        one_space (a + 0x8w) (CODE_LENGTH ns) b2`,
         `b2`,`f2`,`df`,`a+7w`,`r4`,`r3`]) x86_addr_thm
    \\ ASM_SIMP_TAC std_ss [GSYM w2w_def,word_arith_lemma1]
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.ABBREV_TAC `imm = ADDR ns1 r4 (w2n c) - a - 0x8w`
    \\ SIMP_TAC std_ss [LSR_ADD,WORD_ADD_0,word_arith_lemma3,word_arith_lemma4]
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!xx.bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x3Dw) * one (r2 + 0x1w,n2w (48 + w2n (c:word7)))`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2` \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (`(g (r2 + 0x1w) = n2w (48 + w2n c)) /\ r2 + 0x1w IN dg` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [w2w_w2w_n2w_lemma]
    \\ Q.PAT_ABBREV_TAC `f2 = (a + 0x7w =+ (n2w (w2n (c:word7))):word8) ff`
    \\ `w2n c < 256` by DECIDE_TAC
    \\ `(r * one (a,0x3Bw) * one (a + 0x1w,7w) * one (a + 0x2w,0xFw) *
         one (a + 0x3w,0x82w) * one (a + 0x4w,y''''') *
         one (a + 0x5w,y'''''') * one (a + 0x6w,y''''''') *
         one_space (a + 0x8w) (CODE_LENGTH ns) b2 *
         one (a + 0x7w,n2w (w2n (c:word7)))) (fun2set (f2,df))` by
           (Q.UNABBREV_TAC `f2` \\ SEP_WRITE_TAC)
    \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.SPECL [`w2n (c:word7)`,`ns1`,`y`,
         `r * one (a,0x3Bw) * one (a + 0x1w,0x7w) * one (a + 0x2w,0xFw) *
        one (a + 0x3w,0x82w) * one (a + 0x4w,y''''') *
        one (a + 0x5w,y'''''') * one (a + 0x6w,y''''''') *
        one_space (a + 0x8w) (CODE_LENGTH ns) b2`,
         `b2`,`f2`,`df`,`a+7w`,`r4`,`r3`]) x86_addr_thm
    \\ ASM_SIMP_TAC std_ss [GSYM w2w_def,word_arith_lemma1]
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.ABBREV_TAC `imm = ADDR ns1 r4 (w2n c) - a - 0x8w`
    \\ SIMP_TAC std_ss [LSR_ADD,WORD_ADD_0,word_arith_lemma3,word_arith_lemma4]
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!xx.bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `x * one (r2,0x3Cw) * one (r2 + 0x1w,n2w (48 + w2n (c:word7)))`
    \\ Q.EXISTS_TAC `b1` \\ Q.EXISTS_TAC `b2` \\ Q.EXISTS_TAC `y`
    \\ ASM_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC));

val x86_codegen_thm = save_thm("x86_codegen_thm",let
  val th = SPEC_ALL x86_codegen_loop_lemma
  val th = Q.INST [`y`|->`x`,`r4`|->`a`,`ns1`|->`ns`,`r3`|->`r2`] th
  val th = RW [GSYM CONJ_ASSOC,GSYM SEP_CODE_IN_MEM_def] (RW [CONJ_ASSOC] th)
  val cc = SIMP_CONV std_ss [LET_DEF] THENC DEPTH_CONV FORCE_PBETA_CONV
           THENC SIMP_CONV std_ss [LET_DEF]
  val def1 = CONV_RULE cc x86_codegen_def
  val pre1 = CONV_RULE cc x86_codegen_pre_def
  val th = RW [GSYM def1,GSYM pre1] (Q.INST [`a`|->`r1`] th)
  in th end);

val SEP_CODE_IN_MEM_LOOP_thm = prove(
  ``!ns a ns1 a2 x.
      (x * SEP_CODE_IN_MEM_LOOP a ns (a1,ns1)) (fun2set (f,df)) ==>
      !p n.
        (iFETCH p ns = SOME n) ==>
        (let branch = \j. ADDR ns1 a1 j - ADDR ns a p in
           BYTES_IN_MEM (ADDR ns a p) df f (X86_ENCODE branch n))``,
  Induct THEN1 SIMP_TAC std_ss [iFETCH_def]
  \\ SIMP_TAC std_ss [iFETCH_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `p`)
  \\ FULL_SIMP_TAC std_ss []
  THEN1
   (FULL_SIMP_TAC std_ss [ADDR_def,SEP_CODE_IN_MEM_LOOP_def,LET_DEF,
       STAR_ASSOC,DECIDE ``~(SUC n = 0)``] \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_X86_ENCODE,GSYM xENC_LENGTH_def])
  \\ Q.PAT_ASSUM `!xx.bb` (K ALL_TAC)
  \\ Cases_on `n`
  \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,ADDR_def,STAR_ASSOC,
       SEP_CODE_IN_MEM_LOOP_def,LET_DEF,SEP_BYTES_IN_MEM_def,X86_ENCODE_def,
       BYTES_IN_MEM_def,SEP_CLAUSES,X86_IMMEDIATE_def,APPEND]
  \\ SEP_READ_TAC);

val SEP_CODE_IN_MEM_IMP = store_thm("SEP_CODE_IN_MEM_IMP",
  ``!x a ns f df xs l p ns.
      (x * SEP_CODE_IN_MEM a ns) (fun2set (f,df)) ==>
      CODE_IN_MEM (xs,l,p,ns) a df f``,
  SIMP_TAC std_ss [SEP_CODE_IN_MEM_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SEP_CODE_IN_MEM_LOOP_thm
  \\ FULL_SIMP_TAC std_ss [CODE_IN_MEM_def,LET_DEF]);

fun subst_SPEC_PC th tm = let
  val p = find_term (can (match_term ``aPC p``)) (cdr (concl th)) handle e =>
          find_term (can (match_term ``pPC p``)) (cdr (concl th)) handle e =>
          find_term (can (match_term ``xPC p``)) (cdr (concl th))
  val p = cdr p
  val tm = subst [mk_var("p",``:word32``) |-> p] tm
  in tm end;

val _ = write_code_to_file "codegen.s" x86_codegen_th

val x86_codegen_better = save_thm("x86_codegen_better",let
  val th = Q.INST [`eax`|->`r1`,`edx`|->`r2`] x86_codegen_th
  val tm = (fst o dest_imp o concl) x86_codegen_thm
  val th = SPEC_BOOL_FRAME_RULE th tm
  val (th,goal) = SPEC_WEAKEN_RULE th (subst_SPEC_PC th ``
    xCODE_IN_MEM df ns * xBYTE_MEMORY dg g * ~xR EAX * ~xR EBX *
    ~xR ECX * ~xR EDI * ~xR EDX * xPC p * ~xS``)
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC x86_codegen_thm
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss [LET_DEF,xCODE_IN_MEM_def,SEP_CLAUSES]
    \\ IMP_RES_TAC SEP_CODE_IN_MEM_IMP
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `fi`
    \\ Q.EXISTS_TAC `r1`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [cond_STAR]
    \\ FULL_SIMP_TAC std_ss [CODE_IN_MEM_def])
  val th = MP th lemma
  val th = RW [SPEC_MOVE_COND,AND_IMP_INTRO] th
  val tm2 = (fst o dest_imp o concl) th
  val goal = mk_imp(tm,tm2)
  val lemma = prove(goal,
    SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC x86_codegen_thm);
  val th = DISCH_ALL (MP th (UNDISCH lemma))
  val th = RW [GSYM SPEC_MOVE_COND] th
  in th end);


val _ = export_theory();
