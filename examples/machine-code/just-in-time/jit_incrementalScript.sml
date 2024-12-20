
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory pairTheory listTheory wordsTheory;
open addressTheory set_sepTheory progTheory prog_x86Theory;
open wordsLib x86_encodeLib helperLib;
open combinTheory;

open jit_inputTheory;
open jit_opsTheory;
open jit_codegenTheory;

open compilerLib;
open export_codeLib;

val _ = new_theory "jit_incremental";
val _ = ParseExtras.temp_loose_equality()
val bool_ss = bool_ss -* ["lift_disj_eq", "list_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "list_imp_disj"]

(* compiler setup begins *)

(* make function "f" have exec permissions *)
val _ = decompilerLib.add_executable_data_name "f"

(* assign meanings to r1, r2, r3, r4 etc *)
val _ = codegen_x86Lib.set_x86_regs
  [(1,"eax"),(6,"ebx"),(5,"ecx"),(2,"edx"),(3,"edi"),(4,"esi"),(7,"ebp")]

(* informal codegen spec:

  r1 eax - preserved (top of stack)
  r2 edx - preserved (return address)
  r3 edi - preserved (rest of stack)
  r4 esi - input: code pointer, output ignored
  r5 ecx - input: bytecode code pointer, output: 0
  r6 ebx - preserved (poniter to code generator)
  r7 ebp - pointer to j map and temp memory

*)

(* compiler setup ends *)

(* calls to code generator execute "xor ecx, index; call ebx" *)

val (xor_lemma,call_lemma) = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val _ = prog_x86Lib.set_x86_code_write_perm_flag true
  val ((th1,_,_),_) = spec "83F1"
  val ((th2,_,_),_) = spec "FFD3"
  val _ = prog_x86Lib.set_x86_code_write_perm_flag false
  val th1 = HIDE_STATUS_RULE true s th1
  val th2 = Q.INST [`df`|->`{esp-4w}`,`f`|->`\x.w`] th2
  val th2 = SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th2
  val th2 = SIMP_RULE bool_ss [IN_INSERT,xM_THM] th2
  val th2 = SIMP_RULE std_ss [GSYM SPEC_MOVE_COND] th2
  val th2 = HIDE_PRE_RULE ``xM (esp - 4w)`` th2
  val th1 = Q.INST [`ecx`|->`0w`,`imm8`|->`n2w t`] th1
  fun foo th = RW [] (DISCH_ALL (SIMP_RULE std_ss [ALIGNED,WORD_XOR_CLAUSES] th))
  in (foo th1, foo th2) end;

(* invariant definition *)

val ENCODES_JUMP_def = Define `
  ENCODES_JUMP a (p:num) j (bs:word8 list) =
    (bs = [0x83w; 0xF1w; n2w p; 0xFFw; 0xD3w:word8]) \/
    ?w. (j p = SOME w) /\ (bs = [0xE9w] ++ X86_IMMEDIATE (w - a - 5w))`;

val X86_ENCODE_def = Define `
  (X86_ENCODE (iSUB)    a p j bs = (bs = [0x2Bw; 0x07w])) /\
  (X86_ENCODE (iSWAP)   a p j bs = (bs = [0x87w; 0x07w])) /\
  (X86_ENCODE (iSTOP)   a p j bs = (bs = [0xFFw; 0xE2w])) /\
  (X86_ENCODE (iPOP)    a p j bs = (bs = [0x8Bw; 0x07w; 0x83w; 0xC7w; 0x04w])) /\
  (X86_ENCODE (iPUSH i) a p j bs = (bs = [0x83w; 0xEFw; 0x04w; 0x89w; 0x07w; 0xB8w; w2w i; 0x00w; 0x00w; 0x00w])) /\
  (X86_ENCODE (iJUMP i) a p j bs = ENCODES_JUMP a (w2n i) j bs) /\
  (X86_ENCODE (iJEQ i)  a p j bs = ?bs0 bs1 bs2. (bs = bs0 ++ bs1 ++ bs2) /\
     (bs0 = [0x3Bw;0x07w;0x0Fw;0x84w;0x5w;0w;0w;0w]) /\
     ENCODES_JUMP (a + 8w) (p+1) j bs1 /\ ENCODES_JUMP (a + 13w) (w2n i) j bs2) /\
  (X86_ENCODE (iJLT i)  a p j bs = ?bs0 bs1 bs2. (bs = bs0 ++ bs1 ++ bs2) /\
     (bs0 = [0x3Bw;0x07w;0x0Fw;0x82w;0x5w;0w;0w;0w]) /\
     ENCODES_JUMP (a + 8w) (p+1) j bs1 /\ ENCODES_JUMP (a + 13w) (w2n i) j bs2)`;

val INSTR_LENGTH_def = Define `
  (INSTR_LENGTH (iSUB) = 2) /\
  (INSTR_LENGTH (iSWAP) = 2) /\
  (INSTR_LENGTH (iSTOP) = 2) /\
  (INSTR_LENGTH (iPOP) = 5) /\
  (INSTR_LENGTH (iPUSH i) = 10) /\
  (INSTR_LENGTH (iJUMP i) = 5) /\
  (INSTR_LENGTH (iJEQ i) = 18) /\
  (INSTR_LENGTH (iJLT i) = 18)`;

val INSTR_LENGTH_THM = prove(
  ``!i a p j bs. X86_ENCODE i a p j bs ==> (INSTR_LENGTH i = LENGTH bs)``,
  Cases THEN SIMP_TAC std_ss [X86_ENCODE_def,LENGTH,
    INSTR_LENGTH_def,ENCODES_JUMP_def,X86_IMMEDIATE_def,APPEND]
  THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [LENGTH,APPEND]);

val SEP_BYTES_IN_MEM_def = Define `
  (SEP_BYTES_IN_MEM a [] = emp) /\
  (SEP_BYTES_IN_MEM a (x::xs) = one (a,x) * SEP_BYTES_IN_MEM (a+1w) xs)`;

val INSTR_IN_MEM_def = Define `
  (INSTR_IN_MEM NONE c p j = emp) /\
  (INSTR_IN_MEM (SOME a) c p j =
     SEP_EXISTS bs. cond (X86_ENCODE c a p j bs) *
                    SEP_BYTES_IN_MEM a bs)`;

val CODE_LOOP_def = Define `
  (CODE_LOOP i j [] = emp) /\
  (CODE_LOOP i j (c::cs) = INSTR_IN_MEM (j i) c i j * CODE_LOOP (i + 1) j cs)`;

val SPACE_LENGTH_def = Define `
  (SPACE_LENGTH i j [] = 0) /\
  (SPACE_LENGTH i (j:num->word32 option) (c::cs) =
     if ~(j i = NONE) then SPACE_LENGTH (i + 1) j cs else
          INSTR_LENGTH c + SPACE_LENGTH (i + 1) j cs)`;

val CODE_SPACE_def = Define `
  (CODE_SPACE a 0 = emp) /\
  (CODE_SPACE a (SUC n) = SEP_EXISTS x. one (a,x) * CODE_SPACE (a+1w) n)`;

val CODE_INV_def = Define `
  CODE_INV a cs j = CODE_LOOP 0 j cs * CODE_SPACE a (SPACE_LENGTH 0 j cs)`;

val MAP_ROW_def = Define `
  (MAP_ROW a NONE = one (a,0w) * one ((a:word32)+4w,0w:word32)) /\
  (MAP_ROW a (SOME w) = one (a,1w) * one (a+4w,w))`;

val MAP_INV_def = Define `
  (MAP_INV a i j [] = emp) /\
  (MAP_INV a i j (c::cs) = MAP_ROW a (j i) * MAP_INV (a + 8w) (i + 1) j cs)`;

val TEMP_INV_def = Define `
  (TEMP_INV a 0 = emp) /\
  (TEMP_INV a (SUC n) = SEP_EXISTS w. one (a - 4w:word32,w:word32) * TEMP_INV (a-4w) n)`;

val TEMP_INV_UNROLL = prove(
  ``0 < n ==> (TEMP_INV a n =
      SEP_EXISTS w. one (a - 4w:word32,w:word32) * TEMP_INV (a-4w) (n - 1))``,
  Cases_on `n` \\ SIMP_TAC std_ss [TEMP_INV_def] \\ SIMP_TAC std_ss [ADD1]);

val MAP_TEMP_INV_def = Define `
  MAP_TEMP_INV a x y j cs =
    TEMP_INV (a - 8w) 7 * one (a-8w, x) * one (a-4w, y) * MAP_INV a 0 j cs * SEP_T`;

val IS_JUMP_def = Define `
  (IS_JUMP (iJUMP i) = T) /\
  (IS_JUMP (iJEQ i) = T) /\
  (IS_JUMP (iJLT i) = T) /\
  (IS_JUMP (iSTOP) = T) /\
  (IS_JUMP x = F)`;

val ON_OFF_def = Define `
  ON_OFF cs j p =
    !i.
      (iFETCH p cs = SOME i) /\ ~(iFETCH (p+1) cs = NONE) /\ ~(IS_JUMP i) ==>
      ((j p = NONE) = (j (p + 1) = NONE)) /\
      !w. (j p = SOME w) ==> (j (p + 1) = SOME (w + n2w (INSTR_LENGTH i)))`;

val state_inv_def = Define `
  state_inv cs dh h dg (g:word32->word8) df f jw j =
    ?a b b1.
      (one_string_0 b (iENCODE cs) b1) (fun2set (g,dg)) /\
      (MAP_TEMP_INV jw a b j cs) (fun2set (h,dh)) /\
      (CODE_INV a cs j) (fun2set (f,df)) /\ ALIGNED jw /\
      (!p. ON_OFF cs j p) /\ LENGTH cs < 128 /\
      !i. LENGTH cs <= i ==> (j i = NONE)`;

(* code generator *)

(* informal codegen spec:

  r1 eax - preserved (top of stack)
  r2 edx - preserved (return address)
  r3 edi - preserved (rest of stack)
  r4 esi - input: generated code pointer, output: where to continue execution
  r5 ecx - input: bytecode program counter, output: 0
  r6 ebx - preserved (poniter to code generator)
  r7 ebp - unchanged (pointer to j map and temp memory)

  during execution:

  r3 - pointer to next code to be generated
  r4 - pointer to current j table entry
  r6 - pointer to bytecode

fun teach_compiler func_name s = let
  val (th1,th2) = decompilerLib.decompile_x86 "_auto_"
    [QUOTE (x86_encodeLib.x86_encode s ^ "/" ^ func_name)]
  val th3 = SIMP_RULE (std_ss++SIZES_ss) [th2,LET_DEF,w2n_n2w] th1
  val _ = codegenLib.add_compiled [th3];
  in th3 end;
val _ = teach_compiler "m" "lea esi, [8 * ecx + ebp]"

*)

fun ord_eval tm = let
  val tms = find_terml (can (match_term ``n2w (ORD c):'a word``)) tm
  in (snd o dest_eq o concl o REWRITE_CONV (map EVAL tms)) tm end;

val _ = Parse.hide "x86_access_j";
val (th1,x86_access_j_def,x86_access_j_pre_def) = compile "x86" ``
  x86_access_j (r5,r7:word32,dh:word32 set,h:word32->word32) =
    let r2 = r5 << 3 in
    let r2 = r2 + r7 in
    let r1 = h (r2) in
    let r2 = h (r2 + 4w) in
      (r1,r2,r5,r7,dh,h)``;

val _ = Parse.hide "x86_encodes_jump";
val (th1,x86_encodes_jump_def,x86_encodes_jump_pre_def) = compile "x86" ``
  x86_encodes_jump (r3:word32,r6:word32,df:word32 set,f:word32->word8) =
    let f = (r3 =+ 0x83w) f in
    let f = (r3 + 1w =+ 0xF1w) f in
    let f = (r3 + 2w =+ w2w r6) f in
    let f = (r3 + 3w =+ 0xFFw) f in
    let f = (r3 + 4w =+ 0xD3w) f in
    let r3 = r3 + 5w in
      (r3,r6,df,f)``;

val _ = Parse.hide "x86_write_jcc";
val (th1,x86_write_jcc_def,x86_write_jcc_pre_def) = (compile "x86" o ord_eval) ``
  x86_write_jcc (r1:word32,r3,r6,df,f) =
    if r1 = n2w (ORD #"j") then (r1,r3,r6,df,f) else
      let f = (r3 =+ 0x3Bw) f in
      let f = (r3 + 1w =+ 0x07w) f in
      let f = (r3 + 2w =+ 0x0Fw) f in
      let f = (r3 + 3w =+ 0x84w) f in
      let f = (r3 + 4w =+ 0x05w) f in
      let f = (r3 + 5w =+ 0x00w) f in
      let f = (r3 + 6w =+ 0x00w) f in
      let f = (r3 + 7w =+ 0x00w) f in
      let r3 = r3 + 8w in
      let (r3,r6,df,f) = x86_encodes_jump (r3,r6,df,f) in
        if r1 = n2w (ORD #"=") then (r1,r3,r6,df,f) else
          let f = (r3 - 10w =+ 0x82w) f in (r1,r3,r6,df,f)``;

val _ = Parse.hide "x86_writecode";
val (th1,x86_writecode_def,x86_writecode_pre_def) = (compile "x86" o ord_eval) ``
  x86_writecode (r3:word32,r4:word32,r5:word32,r6:word32,df:word32 set,f:word32->word8,dg:word32 set,g:word32->word8,dh:word32 set,h:word32->word32) =
    (* r6 = pointer to bytecode encoding *)
    (* r5 = index of bytecode instruction *)
    (* r4 = pointer to row in map j *)
    (* r3 = pointer to place where new code is written *)
    let r1 = (w2w (g r6)):word32 in
    let r5 = r5 + 1w in
    if r1 = 0w then (r3,df,f,dg,g,dh,h) else
    let h = (r4 =+ 1w) h in
    let h = (r4 + 4w =+ r3) h in
    let r4 = r4 + 8w in
    let r6 = r6 + 1w in
      if r1 = n2w (ORD #"-") then
        let f = (r3 =+ 0x2Bw) f in
        let f = (r3 + 1w =+ 0x07w) f in
        let r3 = r3 + 2w in
          x86_writecode (r3,r4,r5,r6,df,f,dg,g,dh,h)
      else if r1 = n2w (ORD #"s") then
        let f = (r3 =+ 0x87w) f in
        let f = (r3 + 1w =+ 0x07w) f in
        let r3 = r3 + 2w in
          x86_writecode (r3,r4,r5,r6,df,f,dg,g,dh,h)
      else if r1 = n2w (ORD #"p") then
        let f = (r3 =+ 0x8Bw) f in
        let f = (r3 + 1w =+ 0x07w) f in
        let f = (r3 + 2w =+ 0x83w) f in
        let f = (r3 + 3w =+ 0xC7w) f in
        let f = (r3 + 4w =+ 0x04w) f in
        let r3 = r3 + 5w in
          x86_writecode (r3,r4,r5,r6,df,f,dg,g,dh,h)
      else if r1 = n2w (ORD #".") then
        let f = (r3 =+ 0xFFw) f in
        let f = (r3 + 1w =+ 0xE2w) f in
        let r3 = r3 + 2w in
          (r3,df,f,dg,g,dh,h)
      else if r1 = n2w (ORD #"c") then
        let r2 = (w2w (g r6)):word32 in
        let r1 = r2 - 48w in
        let r6 = r6 + 1w in
        let r2 = r2 + 1w in
        let f = (r3 =+ 0x83w) f in
        let f = (r3 + 1w =+ 0xEFw) f in
        let f = (r3 + 2w =+ 0x04w) f in
        let f = (r3 + 3w =+ 0x89w) f in
        let f = (r3 + 4w =+ 0x07w) f in
        let f = (r3 + 5w =+ 0xB8w) f in
        let f = (r3 + 6w =+ w2w r1) f in
        let f = (r3 + 7w =+ 0w) f in
        let f = (r3 + 8w =+ 0w) f in
        let f = (r3 + 9w =+ 0w) f in
        let r3 = r3 + 10w in
          x86_writecode (r3,r4,r5,r6,df,f,dg,g,dh,h)
      else
        let r2 = (w2w (g r6)):word32 in
        let r6 = r5 in
        let (r1,r3,r6,df,f) = x86_write_jcc (r1,r3,r6,df,f) in
        let r6 = r2 - 48w in
        let (r3,r6,df,f) = x86_encodes_jump (r3,r6,df,f) in
          (r3,df,f,dg,g,dh,h)``;

val _ = Parse.hide "x86_findbyte";
val (th1,x86_findbyte_def,x86_findbyte_pre_def) = (compile "x86" o ord_eval) ``
  x86_findbyte (r1:word32,r2:word32,r5:word32,r6:word32,dg:word32 set,g:word32->word8) =
    if r5 = 0w then (r1,r2,r6,dg,g) else
      let r5 = r5 - 1w in
        if g r2 = n2w (ORD #"-") then let r2 = r2 + 1w in x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #"s") then let r2 = r2 + 1w in x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #"p") then let r2 = r2 + 1w in x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #"c") then let r2 = r2 + 2w in x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #".") then
          let r2 = r2 + 1w in let r6 = r2 in let r1 = r5 in
            x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #"j") then
          let r2 = r2 + 1w in let r2 = r2 + 1w in
          let r6 = r2 in let r1 = r5 in
            x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #"=") then
          let r2 = r2 + 1w in let r2 = r2 + 1w in
          let r6 = r2 in let r1 = r5 in
            x86_findbyte (r1,r2,r5,r6,dg,g) else
        if g r2 = n2w (ORD #"<") then
          let r2 = r2 + 1w in let r2 = r2 + 1w in
          let r6 = r2 in let r1 = r5 in
            x86_findbyte (r1,r2,r5,r6,dg,g) else
          (r1,r2,r6,dg,g)``;

val _ = Parse.hide "x86_newcode";
val (th1,x86_newcode_def,x86_newcode_pre_def) = compile "x86" ``
  x86_newcode (r1:word32,r5:word32,r7:word32,df:word32 set,f:word32->word8,dg:word32 set,g:word32->word8,dh:word32 set,h:word32->word32) =
    if ~(r1 = 0w) then (r7,df,f,dg,g,dh,h) else
      (* find location r5 in bytecode, pointed to by r6 *)
      let r6 = h (r7 - 4w) in (* pointer to start of bytecode *)
      let r1 = r5 in
      let r2 = r6 in
      let (r1,r2,r6,dg,g) = x86_findbyte (r1,r2,r5,r6,dg,g) in
      (* here r6 points to right byte code *)
      let r5 = h (r7 - 32w) in
      let r5 = r5 - r1 in (* r5 holds index that corresponds to pointer r6 *)
      (* write the new code *)
      let r3 = h (r7 - 8w) in
      let r1 = r5 << 3 in
      let r4 = r7 + r1 in
      let (r3,df,f,dg,g,dh,h) = x86_writecode (r3,r4,r5,r6,df,f,dg,g,dh,h) in
      let h = ((r7 - 8w) =+ r3) h in
        (r7,df,f,dg,g,dh,h)``

val _ = Parse.hide "x86_write_jump";
val (th1,x86_write_jump_def,x86_write_jump_pre_def) = compile "x86" ``
  x86_write_jump (r2:word32,r4:word32,df:word32 set,f:word32->word8) =
    let f = (r4 - 5w =+ 0xE9w) f in
    let r2 = r2 - r4 in
    let f = (r4 - 4w =+ w2w r2) f in
    let r2 = r2 >>> 8 in
    let f = (r4 - 3w =+ w2w r2) f in
    let r2 = r2 >>> 8 in
    let f = (r4 - 2w =+ w2w r2) f in
    let r2 = r2 >>> 8 in
    let f = (r4 - 1w =+ w2w r2) f in
      (df,f)``;

val _ = Parse.hide "x86_write_jump_cond";
val (th1,x86_write_jump_cond_def,x86_write_jump_cond_pre_def) = compile "x86" ``
  x86_write_jump_cond (r1:word32,r2:word32,r4:word32,df:word32 set,f:word32->word8) =
    if r1 = 0w then
      let (df,f) = x86_write_jump (r2,r4,df,f) in (df,f)
    else (df,f)``

val _ = Parse.hide "x86_inc";
val (x86_inc_th,x86_inc_def,x86_inc_pre_def) = compile "x86" ``
  x86_inc (r1,r2,r3,r4,r5,r6,r7,dh,h,df,f,dg,g) =
    let h = (r7 - 12w =+ r1) h in
    let h = (r7 - 16w =+ r2) h in
    let h = (r7 - 20w =+ r3) h in
    let h = (r7 - 24w =+ r4) h in (* address from which we got here *)
    let h = (r7 - 28w =+ r6) h in
    let h = (r7 - 32w =+ r5) h in
    (* read state map j *)
    let (r1,r2,r5,r7,dh,h) = x86_access_j (r5,r7,dh,h) in
    let (r7,df,f,dg,g,dh,h) = x86_newcode (r1,r5,r7,df,f,dg,g,dh,h) in
    let r5 = h (r7 - 32w) in
    let (r1,r2,r5,r7,dh,h) = x86_access_j (r5,r7,dh,h) in
    let r4 = h (r7 - 24w) in
    let r1 = h (r7 - 0x24w) in
    let r6 = r2 in
    let r4 = r4 + 5w in
    let (df,f) = x86_write_jump_cond (r1,r2,r4,df,f) in (* only do this if not first time *)
    let r5 = 0w:word32 in
    let r1 = h (r7 - 12w) in
    let r2 = h (r7 - 16w) in
    let r3 = h (r7 - 20w) in
    let r4 = r6 in
    let r6 = h (r7 - 28w) in
    let h = (r7 - 0x24w =+ r5) h in
      (r1,r2,r3,r4,r5,r6,r7,dh,h,df,f,dg,g)``

(* idea:

  look up j map entry
  if j i = none then
    make j i some
    - find right instruction in bytecode
    - repeatedly update map j, write instruction,
        stop after first jump instruction
  write jump to point to generated code

*)

val UNFOLD_MAP_INV = (SIMP_RULE std_ss [] o Q.SPEC `0` o prove)(
  ``!k a cs i.
      i < LENGTH cs ==>
      ?q. MAP_INV a k j cs = MAP_ROW (a + n2w (8 * i)) (j (i + k)) * q``,
  Induct_on `cs` \\ SIMP_TAC std_ss [LENGTH] \\ Cases_on `i`
  \\ SIMP_TAC std_ss [MAP_INV_def,WORD_ADD_0] \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [] \\ RES_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`k+1`,`a+8w`])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES,word_arith_lemma1,ADD1]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ Q.EXISTS_TAC `q * MAP_ROW a (j k)` \\ SIMP_TAC (std_ss++star_ss) []);

val x86_access_j_thm = prove(
  ``i < LENGTH cs /\ LENGTH cs <= 128 /\ ALIGNED r7 /\
    (r * MAP_INV r7 0 j cs) (fun2set (h,dh)) ==>
    x86_access_j_pre (n2w i,r7,dh,h) /\
    (x86_access_j (n2w i,r7,dh,h) =
       (if j i = NONE then 0w else 1w,
        if j i = NONE then 0w else THE (j i),n2w i,r7,dh,h))``,
  STRIP_TAC \\ SIMP_TAC std_ss [x86_access_j_def,x86_access_j_pre_def,LET_DEF]
  \\ SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,AC ADD_ASSOC ADD_COMM,w2n_n2w]
  \\ SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED,WORD_MUL_LSL]
  \\ IMP_RES_TAC UNFOLD_MAP_INV
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`j`,`r7`])
  \\ Cases_on `j i`
  \\ FULL_SIMP_TAC std_ss [MAP_ROW_def]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ASM_SIMP_TAC bool_ss [DECIDE ``8 = 4 * 2``,GSYM word_mul_n2w,
       ALIGNED_CLAUSES,GSYM WORD_MULT_ASSOC]
  \\ SIMP_TAC std_ss [word_mul_n2w,MULT_ASSOC]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC,AC MULT_ASSOC MULT_COMM]
  \\ SEP_READ_TAC);

val CODE_LOOP_UNROLL = (SIMP_RULE std_ss [] o Q.SPEC `0` o prove) (
  ``!i cs p instr j r.
      (iFETCH p cs = SOME c) ==>
      ?q. CODE_LOOP i j cs = INSTR_IN_MEM (j (p + i)) c (p + i) j * q``,
  Induct_on `cs` \\ SIMP_TAC std_ss [iFETCH_def] \\ REPEAT STRIP_TAC \\ Cases_on `p`
  THEN1 (FULL_SIMP_TAC std_ss [CODE_LOOP_def,INSTR_IN_MEM_def,SEP_CLAUSES] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [ADD1,CODE_LOOP_def]
  \\ Q.PAT_X_ASSUM `!i.bbb` (ASSUME_TAC o Q.SPECL [`i+1`,`n`,`j`])
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `INSTR_IN_MEM (j i) h i j * q`
  \\ SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM,AC ADD_COMM ADD_ASSOC]);

val CODE_LOOP_IMP_BYTES_IN_MEM = prove(
  ``(CODE_LOOP 0 j cs * r) (fun2set (f,df)) ==>
    !p c w.
      (iFETCH p cs = SOME c) /\ (j p = SOME w) ==>
      ?bs. BYTES_IN_MEM w df f bs /\ X86_ENCODE c w p j bs``,
   REPEAT STRIP_TAC
   \\ IMP_RES_TAC CODE_LOOP_UNROLL
   \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `j`)
   \\ FULL_SIMP_TAC std_ss [INSTR_IN_MEM_def,SEP_CLAUSES]
   \\ FULL_SIMP_TAC std_ss [SEP_EXISTS_THM,cond_STAR,GSYM STAR_ASSOC]
   \\ Q.EXISTS_TAC `bs` \\ ASM_SIMP_TAC std_ss []
   \\ Q.PAT_X_ASSUM `(SEP_BYTES_IN_MEM w bs * (q * r)) (fun2set (f,df))` MP_TAC
   \\ Q.SPEC_TAC (`w`,`a`) \\ Q.SPEC_TAC (`q * r`,`rr`) \\ REPEAT (POP_ASSUM (K ALL_TAC))
   \\ Induct_on `bs` \\ SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,BYTES_IN_MEM_def]
   \\ REPEAT STRIP_TAC THEN1 SEP_READ_TAC THEN1 SEP_READ_TAC
   \\ Q.PAT_X_ASSUM `!rr. bb` MATCH_MP_TAC \\ Q.EXISTS_TAC `one (a,h) * rr`
   \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val cont_jump_def = Define `
  cont_jump j p cs a (t:word7) =
    (iFETCH p cs = SOME (iJUMP t)) /\ (j p = SOME a) \/
    (iFETCH p cs = SOME (iJLT t)) /\ (j p = SOME (a - 13w)) \/
    (iFETCH p cs = SOME (iJEQ t)) /\ (j p = SOME (a - 13w)) \/
    (?r. (iFETCH p cs = SOME (iJLT r)) /\ (j p = SOME (a - 8w)) /\ (p + 1 = w2n t)) \/
    (?r. (iFETCH p cs = SOME (iJEQ r)) /\ (j p = SOME (a - 8w)) /\ (p + 1 = w2n t))`;

val x86_write_jump_thm = prove(
  ``(CODE_LOOP 0 j cs * r) (fun2set (f,df)) /\
    cont_jump j p cs a t /\ (j (w2n t) = SOME w) ==>
    ?f2. x86_write_jump_pre(w,a + 5w,df,f) /\
         (x86_write_jump(w,a + 5w,df,f) = (df,f2)) /\
         (CODE_LOOP 0 j cs * r) (fun2set (f2,df))``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [cont_jump_def]
  \\ IMP_RES_TAC CODE_LOOP_UNROLL
  \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [INSTR_IN_MEM_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_EXISTS,cond_STAR]
  \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
  THEN1
   (`?x1 x2 x3 x4 x5. y = [x1;x2;x3;x4;x5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [x86_write_jump_def,x86_write_jump_pre_def,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,SEP_BYTES_IN_MEM_def]
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC,word_arith_lemma4,
         WORD_ADD_0,word_arith_lemma1,SEP_CLAUSES]
    \\ STRIP_TAC THEN1 SEP_READ_TAC
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.EXISTS_TAC `[0xE9w] ++ X86_IMMEDIATE (w - a - 5w)`
    \\ SIMP_TAC std_ss [X86_IMMEDIATE_def,LSR_ADD,APPEND,SEP_BYTES_IN_MEM_def]
    \\ SIMP_TAC std_ss [word_arith_lemma1,ENCODES_JUMP_def,CONS_11]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,X86_IMMEDIATE_def,APPEND]
    \\ SIMP_TAC std_ss [SEP_CLAUSES] \\ SEP_WRITE_TAC)
  THEN1
   (`?x1 x2 x3 x4 x5. bs2 = [x1;x2;x3;x4;x5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ `?y1 y2 y3 y4 y5. bs1 = [y1;y2;y3;y4;y5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [x86_write_jump_def,x86_write_jump_pre_def,LET_DEF]
    \\ Q.PAT_X_ASSUM `y = bbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,SEP_BYTES_IN_MEM_def]
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC,word_arith_lemma4,
         WORD_ADD_0,word_arith_lemma1,SEP_CLAUSES,word_arith_lemma3]
    \\ STRIP_TAC THEN1 SEP_READ_TAC
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x82w; 0x5w; 0x0w; 0x0w; 0x0w; y1; y2; y3; y4;
         y5; 0xE9w] ++ X86_IMMEDIATE (w - a - 5w)`
    \\ REVERSE STRIP_TAC THEN1
     (SIMP_TAC std_ss [X86_IMMEDIATE_def,LSR_ADD,APPEND,SEP_BYTES_IN_MEM_def]
      \\ SIMP_TAC std_ss [word_arith_lemma1,ENCODES_JUMP_def,CONS_11]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,X86_IMMEDIATE_def,APPEND]
      \\ SIMP_TAC std_ss [SEP_CLAUSES,word_arith_lemma3,WORD_ADD_0]
      \\ SEP_WRITE_TAC)
    \\ Q.EXISTS_TAC `bs1` \\ Q.EXISTS_TAC `[0xE9w] ++ X86_IMMEDIATE (w - a - 5w)`
    \\ ASM_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,CONS_11]
    \\ ASM_SIMP_TAC std_ss [ENCODES_JUMP_def,X86_IMMEDIATE_def,APPEND])
  THEN1
   (`?x1 x2 x3 x4 x5. bs2 = [x1;x2;x3;x4;x5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ `?y1 y2 y3 y4 y5. bs1 = [y1;y2;y3;y4;y5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [x86_write_jump_def,x86_write_jump_pre_def,LET_DEF]
    \\ Q.PAT_X_ASSUM `y = bbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,SEP_BYTES_IN_MEM_def]
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC,word_arith_lemma4,
         WORD_ADD_0,word_arith_lemma1,SEP_CLAUSES,word_arith_lemma3]
    \\ STRIP_TAC THEN1 SEP_READ_TAC
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w; y1; y2; y3; y4;
         y5; 0xE9w] ++ X86_IMMEDIATE (w - a - 5w)`
    \\ REVERSE STRIP_TAC THEN1
     (SIMP_TAC std_ss [X86_IMMEDIATE_def,LSR_ADD,APPEND,SEP_BYTES_IN_MEM_def]
      \\ SIMP_TAC std_ss [word_arith_lemma1,ENCODES_JUMP_def,CONS_11]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,X86_IMMEDIATE_def,APPEND]
      \\ SIMP_TAC std_ss [SEP_CLAUSES,word_arith_lemma3,WORD_ADD_0]
      \\ SEP_WRITE_TAC)
    \\ Q.EXISTS_TAC `bs1` \\ Q.EXISTS_TAC `[0xE9w] ++ X86_IMMEDIATE (w - a - 5w)`
    \\ ASM_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,CONS_11]
    \\ ASM_SIMP_TAC std_ss [ENCODES_JUMP_def,X86_IMMEDIATE_def,APPEND])
  THEN1
   (`?x1 x2 x3 x4 x5. bs2 = [x1;x2;x3;x4;x5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ `?y1 y2 y3 y4 y5. bs1 = [y1;y2;y3;y4;y5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [x86_write_jump_def,x86_write_jump_pre_def,LET_DEF]
    \\ Q.PAT_X_ASSUM `y = bbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,SEP_BYTES_IN_MEM_def]
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC,word_arith_lemma4,
         WORD_ADD_0,word_arith_lemma1,SEP_CLAUSES,word_arith_lemma3]
    \\ STRIP_TAC THEN1 SEP_READ_TAC
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x82w; 0x5w; 0x0w; 0x0w; 0x0w] ++
          [0xE9w] ++ X86_IMMEDIATE (w - a - 5w) ++ [x1;x2;x3;x4;x5]`
    \\ REVERSE STRIP_TAC THEN1
     (SIMP_TAC std_ss [X86_IMMEDIATE_def,LSR_ADD,APPEND,SEP_BYTES_IN_MEM_def]
      \\ SIMP_TAC std_ss [word_arith_lemma1,ENCODES_JUMP_def,CONS_11]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,X86_IMMEDIATE_def,APPEND]
      \\ SIMP_TAC std_ss [SEP_CLAUSES,word_arith_lemma3,WORD_ADD_0]
      \\ SEP_WRITE_TAC)
    \\ Q.EXISTS_TAC `[0xE9w] ++ X86_IMMEDIATE (w - a - 5w)` \\ Q.EXISTS_TAC `bs2`
    \\ ASM_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,CONS_11]
    \\ ASM_SIMP_TAC std_ss [ENCODES_JUMP_def,X86_IMMEDIATE_def,APPEND])
  THEN1
   (`?x1 x2 x3 x4 x5. bs2 = [x1;x2;x3;x4;x5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ `?y1 y2 y3 y4 y5. bs1 = [y1;y2;y3;y4;y5]` by
      FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,ENCODES_JUMP_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [x86_write_jump_def,x86_write_jump_pre_def,LET_DEF]
    \\ Q.PAT_X_ASSUM `y = bbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,SEP_BYTES_IN_MEM_def]
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC,word_arith_lemma4,
         WORD_ADD_0,word_arith_lemma1,SEP_CLAUSES,word_arith_lemma3]
    \\ STRIP_TAC THEN1 SEP_READ_TAC
    \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w] ++
          [0xE9w] ++ X86_IMMEDIATE (w - a - 5w) ++ [x1;x2;x3;x4;x5]`
    \\ REVERSE STRIP_TAC THEN1
     (SIMP_TAC std_ss [X86_IMMEDIATE_def,LSR_ADD,APPEND,SEP_BYTES_IN_MEM_def]
      \\ SIMP_TAC std_ss [word_arith_lemma1,ENCODES_JUMP_def,CONS_11]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,X86_IMMEDIATE_def,APPEND]
      \\ SIMP_TAC std_ss [SEP_CLAUSES,word_arith_lemma3,WORD_ADD_0]
      \\ SEP_WRITE_TAC)
    \\ Q.EXISTS_TAC `[0xE9w] ++ X86_IMMEDIATE (w - a - 5w)` \\ Q.EXISTS_TAC `bs2`
    \\ ASM_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,CONS_11]
    \\ ASM_SIMP_TAC std_ss [ENCODES_JUMP_def,X86_IMMEDIATE_def,APPEND]));

val x86_write_jump_cond_thm = prove(
  ``(CODE_LOOP 0 j cs * r) (fun2set (f,df)) /\
    ((v = 0w) ==> cont_jump j p cs a t) /\ (j (w2n t) = SOME w) ==>
    ?f2. x86_write_jump_cond_pre(v,w,a + 5w,df,f) /\
         (x86_write_jump_cond(v,w,a + 5w,df,f) = (df,f2)) /\
         (CODE_LOOP 0 j cs * r) (fun2set (f2,df))``,
  Cases_on `v = 0w`
  \\ ASM_SIMP_TAC std_ss [x86_write_jump_cond_def,x86_write_jump_cond_pre_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC x86_write_jump_thm
  \\ ASM_SIMP_TAC std_ss [LET_DEF]);

fun TRY_TAC t goal = t goal handle e => ALL_TAC goal;

(* r6 remembers last poniter *)
(* r1 remembers how many to drop for r6 *)

val DROP_EQ_CONS = prove(
  ``!cs n. n < LENGTH cs ==> (DROP n cs = EL n cs :: DROP (n + 1) cs)``,
  Induct \\ SIMP_TAC std_ss [LENGTH,DROP_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n`
  THEN1 (Cases_on `cs` \\ SIMP_TAC std_ss [EL,HD,DROP_def])
  \\ FULL_SIMP_TAC std_ss [EL,TL] \\ FULL_SIMP_TAC std_ss [ADD1]);

val iFETCH_IMP = prove(
  ``!cs p c. p < LENGTH cs /\ (EL p cs = c) ==> (iFETCH p cs = SOME c)``,
  Induct \\ SIMP_TAC std_ss [LENGTH,iFETCH_def] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `p` \\ FULL_SIMP_TAC std_ss [EL,HD,TL] \\ SIMP_TAC std_ss [ADD1]);

val prev_jump_def = Define `
  (prev_jump cs 0 = 0) /\
  (prev_jump cs (SUC i) = if IS_JUMP (EL i cs) then i + 1 else prev_jump cs i)`;

val x86_findbyte_thm = (SIMP_RULE std_ss [prev_jump_def,DROP_0] o Q.SPECL [`p`,`0`,`p`,`r2`,`r2`,`q`,`q`] o prove)(
  ``!k i j r2 r6 r q.
      i + k < LENGTH cs /\ LENGTH cs <= 128 /\
      (r * one_string_0 r2 (iENCODE (DROP i cs)) b1) (fun2set (g,dg)) /\
      (q * one_string_0 r6 (iENCODE (DROP (prev_jump cs i) cs)) b1) (fun2set (g,dg)) /\
      (prev_jump cs i = i + k - j) /\ j <= i + k ==>
      ?r2i r6i ji qi.
         x86_findbyte_pre (n2w j,r2,n2w k,r6,dg,g) /\
         (x86_findbyte (n2w j,r2,n2w k,r6,dg,g) = (n2w ji,r2i,r6i,dg,g)) /\
         (qi * one_string_0 r6i (iENCODE (DROP (prev_jump cs (i + k)) cs)) b1) (fun2set (g,dg)) /\
         (prev_jump cs (i + k) = i + k - ji) /\ ji <= i + k``,
  Induct THEN1
   (REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [x86_findbyte_def,x86_findbyte_pre_def]
    \\ SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `j`
    \\ FULL_SIMP_TAC std_ss [DROP_def,DECIDE ``i <= 0 = (i = 0)``] \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC
  \\ `SUC k < 4294967296` by DECIDE_TAC
  \\ `~(n2w (SUC k) = 0w:word32)` by (ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [x86_findbyte_def,x86_findbyte_pre_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_arith_lemma1]
  \\ `i < LENGTH cs` by DECIDE_TAC
  \\ IMP_RES_TAC DROP_EQ_CONS
  \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `EL i cs`
  \\ FULL_SIMP_TAC std_ss [iENCODE_def,iENCODE1_def,one_string_0_STRCAT,iIMM_def]
  \\ FULL_SIMP_TAC std_ss [one_string_def,MAP,LENGTH,one_list_def,word_arith_lemma1,
         stringTheory.ORD_CHR_RWT,SEP_CLAUSES,STAR_ASSOC,iIMM_def,APPEND]
  \\ TRY_TAC (`g r2 = 0x2Dw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x20w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x73w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x2Ew` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x6Aw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x3Dw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x3Cw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x70w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r2 = 0x63w` by SEP_READ_TAC)
  \\ TRY_TAC (`r2 IN dg` by SEP_READ_TAC)
  \\ TRY_TAC (`(r2 + 1w) IN dg` by SEP_READ_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``i + (k + 1) = (i + 1) + k``,ADD1]
  \\ Q.PAT_X_ASSUM `!i.bbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [RW[ADD1]prev_jump_def,IS_JUMP_def]
  \\ METIS_TAC []);

val x86_encodes_jump_thm = prove(
  ``(SEP_BYTES_IN_MEM a [x1;x2;x3;x4;x5] * r) (fun2set (f,df)) /\ i < 256 ==>
    ?f2 bs. x86_encodes_jump_pre (a,n2w i,df,f) /\
            (x86_encodes_jump (a,n2w i,df,f) = (a+5w,n2w i,df,f2)) /\
            (SEP_BYTES_IN_MEM a bs * r) (fun2set (f2,df)) /\
            ENCODES_JUMP a i j bs``,
  SIMP_TAC std_ss [x86_encodes_jump_def,x86_encodes_jump_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF,SEP_BYTES_IN_MEM_def,word_arith_lemma1]
  \\ SIMP_TAC std_ss [SEP_CLAUSES]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `[0x83w; 0xF1w; n2w i; 0xFFw; 0xD3w]`
  \\ SIMP_TAC std_ss [ENCODES_JUMP_def,SEP_BYTES_IN_MEM_def,word_arith_lemma1]
  \\ SIMP_TAC std_ss [SEP_CLAUSES]
  \\ `i < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1 SEP_WRITE_TAC
  \\ SEP_READ_TAC);

val LENGTH_LE_DROP = prove(
  ``!xs n. LENGTH xs <= n ==> (DROP n xs = [])``,
  Induct \\ SIMP_TAC std_ss [DROP_def] \\ Cases_on `n`
  \\ ASM_SIMP_TAC std_ss [DROP_def,LENGTH,ADD1]);

val SPACE_LENGTH_UPDATE = prove(
  ``!cs i k.
      i < k ==> (SPACE_LENGTH k ((i =+ w) j) cs = SPACE_LENGTH k j cs)``,
  Induct \\ SIMP_TAC std_ss [SPACE_LENGTH_def,APPLY_UPDATE_THM,
    DECIDE ``n < m ==> ~(n = m:num)``]
  \\ REPEAT STRIP_TAC
  \\ `i < k + 1` by DECIDE_TAC  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val SPACE_LENGTH_UNROLL = (SIMP_RULE std_ss [] o Q.SPEC `0` o prove) (
  ``!i cs p c j r w.
      (iFETCH p cs = SOME c) /\ (j (p + i) = NONE) ==>
      (SPACE_LENGTH i j cs =
       INSTR_LENGTH c + SPACE_LENGTH i ((p + i =+ SOME w) j) cs)``,
  Induct_on `cs` \\ SIMP_TAC std_ss [iFETCH_def] \\ REPEAT STRIP_TAC \\ Cases_on `p`
  THEN1 (FULL_SIMP_TAC std_ss [SPACE_LENGTH_def,APPLY_UPDATE_THM]
         \\ `i < i + 1` by DECIDE_TAC
         \\ ASM_SIMP_TAC std_ss [SPACE_LENGTH_UPDATE])
  \\ FULL_SIMP_TAC std_ss [ADD1,SPACE_LENGTH_def,APPLY_UPDATE_THM]
  \\ Q.PAT_X_ASSUM `!i.bbb` (ASSUME_TAC o Q.SPECL [`i+1`,`n`,`c`,`j`,`w`])
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM,AC ADD_COMM ADD_ASSOC]
  \\ RES_TAC \\ Cases_on `j i <> NONE`
  \\ FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM,AC ADD_COMM ADD_ASSOC]);

val ENCODE_JUMP_UPDATE = prove(
  ``(j k = NONE) /\ ENCODES_JUMP x i j y ==>
    ENCODES_JUMP x i ((k =+ SOME w) j) y``,
  SIMP_TAC std_ss [ENCODES_JUMP_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `k = i` \\ FULL_SIMP_TAC std_ss []);

val SEP_IMP_INSTR_IN_MEM_UPDATE = prove(
  ``~(i = k) /\ (j k = NONE) ==>
    SEP_IMP (INSTR_IN_MEM (j i) h i j)
            (INSTR_IN_MEM (j i) h i ((k =+ SOME w) j))``,
  Cases_on `j i` \\ ASM_SIMP_TAC std_ss [INSTR_IN_MEM_def,SEP_IMP_REFL]
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `y` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
  THEN1 METIS_TAC [ENCODE_JUMP_UPDATE]
  \\ Q.EXISTS_TAC `bs1` \\ Q.EXISTS_TAC `bs2`
  \\ SIMP_TAC std_ss []
  \\ METIS_TAC [ENCODE_JUMP_UPDATE]);

val SEP_IMP_CODE_LOOP_UPDATE = prove(
  ``!cs i j k.
      k < i /\ (j k = NONE) ==>
      SEP_IMP (CODE_LOOP i j cs)
              (CODE_LOOP i ((k =+ SOME w) j) cs)``,
  Induct \\ SIMP_TAC std_ss [CODE_LOOP_def,SEP_IMP_REFL,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC
  \\ `~(i = k) /\ k < i + 1` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC SEP_IMP_STAR
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC [SEP_IMP_INSTR_IN_MEM_UPDATE]);

val CODE_LOOP_PULL = (SIMP_RULE std_ss [] o Q.SPEC `0` o prove) (
  ``!i cs p c j r w.
      (iFETCH p cs = SOME c) /\ (j (p + i) = NONE) ==>
      SEP_IMP (INSTR_IN_MEM (SOME w) c (p + i) ((p + i =+ SOME w) j) * CODE_LOOP i j cs)
              (CODE_LOOP i ((p + i =+ SOME w) j) cs)``,
  Induct_on `cs` \\ SIMP_TAC std_ss [iFETCH_def] \\ REPEAT STRIP_TAC \\ Cases_on `p`
  THEN1 (FULL_SIMP_TAC std_ss [CODE_LOOP_def,APPLY_UPDATE_THM]
         \\ MATCH_MP_TAC SEP_IMP_STAR
         \\ SIMP_TAC std_ss [SEP_IMP_REFL]
         \\ SIMP_TAC std_ss [INSTR_IN_MEM_def,SEP_CLAUSES]
         \\ MATCH_MP_TAC SEP_IMP_CODE_LOOP_UPDATE
         \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [ADD1,CODE_LOOP_def,APPLY_UPDATE_THM]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ MATCH_MP_TAC SEP_IMP_STAR
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ REPEAT STRIP_TAC THEN1
   (REWRITE_TAC [DECIDE ``1 + i = i + 1``]
    \\ Q.PAT_X_ASSUM `!i.bbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [DECIDE ``1 + i = i + 1``])
  \\ MATCH_MP_TAC SEP_IMP_INSTR_IN_MEM_UPDATE
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val CODE_SPACE_ADD = prove(
  ``!n m a.
      CODE_SPACE a (n + m) = CODE_SPACE a n * CODE_SPACE (a + n2w n) m``,
  Induct \\ ASM_SIMP_TAC std_ss [CODE_SPACE_def,SEP_CLAUSES,WORD_ADD_0,ADD]
  \\ SIMP_TAC std_ss [STAR_ASSOC,ADD1,word_arith_lemma1]
  \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]);

val CODE_INV_UPDATE = prove(
  ``!p cs c j f f2 df.
      (iFETCH p cs = SOME c) /\ (j p = NONE) /\
      (!r. (CODE_SPACE w (INSTR_LENGTH c) * r) (fun2set (f,df)) ==>
           (INSTR_IN_MEM (SOME w) c p ((p =+ SOME w) j) * r) (fun2set (f2,df))) /\
      (CODE_INV w cs j) (fun2set (f,df)) ==>
      (CODE_INV (w + n2w (INSTR_LENGTH c)) cs ((p =+ SOME w) j)) (fun2set (f2,df))``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [CODE_INV_def]
  \\ IMP_RES_TAC SPACE_LENGTH_UNROLL
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `w`)
  \\ FULL_SIMP_TAC std_ss [CODE_SPACE_ADD,STAR_ASSOC]
  \\ Q.PAT_X_ASSUM `!r. bbb`  (ASSUME_TAC o Q.SPEC `CODE_LOOP 0 j cs *
       CODE_SPACE (w + n2w (INSTR_LENGTH c)) (SPACE_LENGTH 0 ((p =+ SOME w) j) cs)`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ RES_TAC
  \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`fun2set(f2,df)`,`r`)
  \\ REWRITE_TAC [GSYM SEP_IMP_def,STAR_ASSOC]
  \\ MATCH_MP_TAC SEP_IMP_STAR
  \\ SIMP_TAC std_ss [SEP_IMP_REFL]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ MATCH_MP_TAC CODE_LOOP_PULL
  \\ ASM_SIMP_TAC std_ss []);

val CODE_SPACE_UNWIND = prove(
  ``!n a. 0 < n ==>
          (CODE_SPACE a n = SEP_EXISTS w. one (a,w) * CODE_SPACE (a+1w) (n-1))``,
  Cases \\ SIMP_TAC std_ss [CODE_SPACE_def]);

val MAP_INV_IGNORE = prove(
  ``!cs n k a j.
      n < k ==> (MAP_INV a k ((n =+ w) j) cs = MAP_INV a k j cs)``,
  Induct \\ SIMP_TAC std_ss [MAP_INV_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ `~(n = k) /\ n < k + 1` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

val iFETCH_NOT_NONE = prove(
  ``!cs n. n < LENGTH cs = ~(iFETCH n cs = NONE)``,
  Induct \\ SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `n` \\ ASM_SIMP_TAC std_ss [LENGTH,iFETCH_def]
  \\ ASM_SIMP_TAC std_ss [ADD1]);

val ENCODES_JUMP_IMP = prove(
  ``!a i j bs. ENCODES_JUMP a i j bs ==> ?z1 z2 z3 z4 z5. bs = [z1;z2;z3;z4;z5]``,
  SIMP_TAC std_ss [ENCODES_JUMP_def]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [CONS_11,X86_IMMEDIATE_def,APPEND]);

val ENCODE_JUMP_LENGTH = prove(
  ``ENCODES_JUMP a i j bs ==> (LENGTH bs = 5)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ENCODES_JUMP_IMP \\ ASM_SIMP_TAC std_ss [LENGTH]);

val x86_writecode_thm = prove(
  ``!n cs q j g f r3 r4 r6 pp h.
      LENGTH cs < 128 /\ ALIGNED r4 /\ (!p. n <= p ==> ON_OFF cs j p) /\
      (n < LENGTH cs ==> (j n = NONE)) /\
      (q * one_string_0 r6 (iENCODE (DROP n cs)) b1) (fun2set (g,dg)) /\
      (CODE_INV r3 cs j) (fun2set (f,df)) /\
      (pp * MAP_INV r4 n j (DROP n cs)) (fun2set (h,dh)) ==>
      ?f2 r3i j2 h2.
        x86_writecode_pre (r3,r4,n2w n,r6,df,f,dg,g,dh,h) /\
        (x86_writecode (r3,r4,n2w n,r6,df,f,dg,g,dh,h) =
          (r3i,df,f2,dg,g,dh,h2)) /\
        (CODE_INV r3i cs j2) (fun2set (f2,df)) /\
        (pp * MAP_INV r4 n j2 (DROP n cs)) (fun2set (h2,dh)) /\
        (!p. n <= p ==> ON_OFF cs j2 p) /\
        (n < LENGTH cs ==> (j2 n = SOME r3)) /\
        (!p. p < n ==> (j p = j2 p)) /\
        (!i. ~(j i = NONE) \/ LENGTH cs <= i ==> (j2 i = j i))``,
  STRIP_TAC \\ STRIP_TAC \\ Induct_on `LENGTH cs - n`
  \\ REPEAT STRIP_TAC THEN1
   (`LENGTH cs <= n /\ ~(n < LENGTH cs)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_LE_DROP,iENCODE_def,one_string_0_def]
    \\ FULL_SIMP_TAC std_ss [APPEND,one_string_def,MAP,one_list_def]
    \\ FULL_SIMP_TAC std_ss [stringTheory.ORD_CHR_RWT]
    \\ `r6 IN dg /\ (g r6 = 0w)` by SEP_READ_TAC
    \\ ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ FULL_SIMP_TAC std_ss [MAP_INV_def]
    \\ METIS_TAC [])
  \\ `v = LENGTH cs - (n + 1)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!cs n. bbb` (ASSUME_TAC o RW [] o Q.SPECL [`cs`,`n + 1`])
  \\ `n < LENGTH cs` by DECIDE_TAC
  \\ IMP_RES_TAC DROP_EQ_CONS
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `j n = NONE` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [MAP_INV_def,MAP_ROW_def,STAR_ASSOC]
  \\ `(pp * MAP_ROW r4 ((n =+ SOME r3) j n) *
       MAP_INV (r4 + 0x8w) (n + 1) j (DROP (n + 1) cs))
         (fun2set ((r4 + 0x4w =+ r3) ((r4 =+ 0x1w) h),dh))` by
    (SIMP_TAC std_ss [APPLY_UPDATE_THM,MAP_ROW_def] \\ SEP_WRITE_TAC)
  \\ `(!p. n + 1 <= p ==> ON_OFF cs ((n =+ SOME r3) j) p)` by
   (FULL_SIMP_TAC std_ss [ON_OFF_def] \\ REPEAT STRIP_TAC
    \\ `~(n = p) /\ ~(n = p + 1) /\ n <= p` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC [])
  \\ Cases_on `EL n cs`
  \\ FULL_SIMP_TAC std_ss [iENCODE_def,one_string_0_STRCAT,one_string_def,STAR_ASSOC,MAP_APPEND,
       iENCODE1_def,LENGTH,SEP_CLAUSES,iIMM_def]
  \\ FULL_SIMP_TAC std_ss [APPEND,one_list_def,MAP,stringTheory.ORD_CHR_RWT,
       LENGTH,word_arith_lemma1,SEP_CLAUSES]
  \\ TRY_TAC (`g r6 = 0x2Dw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x20w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x73w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x2Ew` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x6Aw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x3Dw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x3Cw` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x70w` by SEP_READ_TAC)
  \\ TRY_TAC (`g r6 = 0x63w` by SEP_READ_TAC)
  \\ `r6 IN dg` by SEP_READ_TAC
  \\ TRY_TAC (`(r6 + 1w) IN dg` by SEP_READ_TAC)
  \\ Q.ABBREV_TAC `hi = (r4 + 0x4w =+ r3) ((r4 =+ 0x1w) h)`
  \\ IMP_RES_TAC iFETCH_IMP
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `~(IS_JUMP iSUB)` by EVAL_TAC
    \\ `(n + 1 < LENGTH cs) ==> (((n =+ SOME r3) j) (n + 1) = NONE)` by
         (SIMP_TAC std_ss [APPLY_UPDATE_THM,DECIDE ``~(n = n + 1)``]
          \\ `ON_OFF cs j n` by METIS_TAC [LESS_EQ_REFL]
          \\ POP_ASSUM MP_TAC
          \\ SIMP_TAC std_ss [ON_OFF_def] \\ METIS_TAC [iFETCH_NOT_NONE])
    \\ Q.ABBREV_TAC `c = iSUB`
    \\ Q.ABBREV_TAC `fi = (r3 + 0x1w =+ 0x7w) ((r3 =+ 0x2Bw) f)`
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH c)) cs ((n =+ SOME r3) j)
         (fun2set (fi,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `c` \\ Q.UNABBREV_TAC `fi`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def]
      \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
    \\ Q.PAT_X_ASSUM `!q j g. bbb` (MP_TAC o
         Q.SPECL [`q * one_string r6 (iENCODE1 c) (r6 + 1w)`,`(n =+ SOME r3) j`,
                  `g`,`fi`,`r3 + n2w (INSTR_LENGTH c)`,`r4 + 8w`, `r6+1w`,
                  `pp * MAP_ROW r4 (((n:num) =+ SOME r3) j n)`,`hi`])
    \\ ASM_SIMP_TAC std_ss [ALIGNED]
    \\ Q.UNABBREV_TAC `c`
    \\ SIMP_TAC std_ss [iENCODE1_def,INSTR_LENGTH_def,one_string_def,
         MAP,one_list_def,SEP_CLAUSES,stringTheory.ORD_CHR_RWT]
    \\ SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ STRIP_TAC
    \\ POP_ASSUM (ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [word_add_n2w]
    \\ Q.EXISTS_TAC `j2`
    \\ ASM_SIMP_TAC std_ss []
    \\ `j2 n = SOME r3` by METIS_TAC [DECIDE ``n < n+1``,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1 (`p < n + 1 /\ ~(n = p)` by DECIDE_TAC \\ METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM iFETCH_NOT_NONE])
    \\ SEP_READ_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `~(IS_JUMP iSWAP)` by EVAL_TAC
    \\ `(n + 1 < LENGTH cs) ==> (((n =+ SOME r3) j) (n + 1) = NONE)` by
         (SIMP_TAC std_ss [APPLY_UPDATE_THM,DECIDE ``~(n = n + 1)``]
          \\ `ON_OFF cs j n` by METIS_TAC [LESS_EQ_REFL]
          \\ POP_ASSUM MP_TAC
          \\ SIMP_TAC std_ss [ON_OFF_def] \\ METIS_TAC [iFETCH_NOT_NONE])
    \\ Q.ABBREV_TAC `c = iSWAP`
    \\ Q.ABBREV_TAC `fi = (r3 + 0x1w =+ 0x7w) ((r3 =+ 0x87w) f)`
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH c)) cs ((n =+ SOME r3) j)
         (fun2set (fi,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `c` \\ Q.UNABBREV_TAC `fi`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def]
      \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
    \\ Q.PAT_X_ASSUM `!q j g. bbb` (MP_TAC o
         Q.SPECL [`q * one_string r6 (iENCODE1 c) (r6 + 1w)`,`(n =+ SOME r3) j`,
                  `g`,`fi`,`r3 + n2w (INSTR_LENGTH c)`,`r4 + 8w`, `r6+1w`,
                  `pp * MAP_ROW r4 (((n:num) =+ SOME r3) j n)`,`hi`])
    \\ ASM_SIMP_TAC std_ss [ALIGNED]
    \\ Q.UNABBREV_TAC `c`
    \\ SIMP_TAC std_ss [iENCODE1_def,INSTR_LENGTH_def,one_string_def,
         MAP,one_list_def,SEP_CLAUSES,stringTheory.ORD_CHR_RWT]
    \\ SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ STRIP_TAC
    \\ POP_ASSUM (ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [word_add_n2w]
    \\ Q.EXISTS_TAC `j2`
    \\ ASM_SIMP_TAC std_ss []
    \\ `j2 n = SOME r3` by METIS_TAC [DECIDE ``n < n+1``,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1 (`p < n + 1 /\ ~(n = p)` by DECIDE_TAC \\ METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM iFETCH_NOT_NONE])
    \\ SEP_READ_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `(IS_JUMP iSTOP)` by EVAL_TAC
    \\ Q.ABBREV_TAC `c = iSTOP`
    \\ Q.ABBREV_TAC `fi = (r3 + 0x1w =+ 0xE2w) ((r3 =+ 0xFFw) f)`
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH c)) cs ((n =+ SOME r3) j)
         (fun2set (fi,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `c` \\ Q.UNABBREV_TAC `fi`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def]
      \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
    \\ Q.EXISTS_TAC `(n =+ SOME r3) j`
    \\ Q.UNABBREV_TAC `c`
    \\ FULL_SIMP_TAC std_ss [INSTR_LENGTH_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [MAP_ROW_def,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ SIMP_TAC std_ss [DECIDE ``n < m ==> ~(n = m:num)``]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def])
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES]
    \\ SEP_READ_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `~(IS_JUMP iPOP)` by EVAL_TAC
    \\ `(n + 1 < LENGTH cs) ==> (((n =+ SOME r3) j) (n + 1) = NONE)` by
         (SIMP_TAC std_ss [APPLY_UPDATE_THM,DECIDE ``~(n = n + 1)``]
          \\ `ON_OFF cs j n` by METIS_TAC [LESS_EQ_REFL]
          \\ POP_ASSUM MP_TAC
          \\ SIMP_TAC std_ss [ON_OFF_def] \\ METIS_TAC [iFETCH_NOT_NONE])
    \\ Q.ABBREV_TAC `c = iPOP`
    \\ Q.ABBREV_TAC `fi = (r3 + 0x4w =+ 0x4w)
        ((r3 + 0x3w =+ 0xC7w)
           ((r3 + 0x2w =+ 0x83w)
              ((r3 + 0x1w =+ 0x7w) ((r3 =+ 0x8Bw) f))))`
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH c)) cs ((n =+ SOME r3) j)
         (fun2set (fi,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `c` \\ Q.UNABBREV_TAC `fi`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def,word_arith_lemma1]
      \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
    \\ Q.PAT_X_ASSUM `!q j g. bbb` (MP_TAC o
         Q.SPECL [`q * one_string r6 (iENCODE1 c) (r6 + 1w)`,`(n =+ SOME r3) j`,
                  `g`,`fi`,`r3 + n2w (INSTR_LENGTH c)`,`r4 + 8w`, `r6+1w`,
                  `pp * MAP_ROW r4 (((n:num) =+ SOME r3) j n)`,`hi`])
    \\ ASM_SIMP_TAC std_ss [ALIGNED]
    \\ Q.UNABBREV_TAC `c`
    \\ SIMP_TAC std_ss [iENCODE1_def,INSTR_LENGTH_def,one_string_def,
         MAP,one_list_def,SEP_CLAUSES,stringTheory.ORD_CHR_RWT]
    \\ SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ STRIP_TAC
    \\ POP_ASSUM (ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [word_add_n2w]
    \\ Q.EXISTS_TAC `j2`
    \\ ASM_SIMP_TAC std_ss []
    \\ `j2 n = SOME r3` by METIS_TAC [DECIDE ``n < n+1``,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1 (`p < n + 1 /\ ~(n = p)` by DECIDE_TAC \\ METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM iFETCH_NOT_NONE])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ SEP_READ_TAC)
  \\ `n2w (w2n ((n2w (ORD (CHR (48 + w2n c)))):word8)) - 0x30w = n2w (w2n c):word32` by
      (ASSUME_TAC (Q.SPEC `c` (INST_TYPE [``:'a``|->``:7``] w2n_lt))
       \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
       \\ `48 + w2n c < 256 /\ 48 + w2n c < 4294967296` by DECIDE_TAC
       \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [stringTheory.ORD_CHR_RWT,w2n_n2w]
       \\ ONCE_REWRITE_TAC [ADD_COMM]
       \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB])
  \\ `(w2n c) < 256` by
      (ASSUME_TAC (Q.SPEC `c` (INST_TYPE [``:'a``|->``:7``] w2n_lt))
       \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [] \\ DECIDE_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `~(IS_JUMP (iPUSH c))` by EVAL_TAC
    \\ `(n + 1 < LENGTH cs) ==> (((n =+ SOME r3) j) (n + 1) = NONE)` by
         (SIMP_TAC std_ss [APPLY_UPDATE_THM,DECIDE ``~(n = n + 1)``]
          \\ `ON_OFF cs j n` by METIS_TAC [LESS_EQ_REFL]
          \\ POP_ASSUM MP_TAC
          \\ SIMP_TAC std_ss [ON_OFF_def] \\ METIS_TAC [iFETCH_NOT_NONE])
    \\ `g (r6 + 1w) = n2w (ORD (CHR (48 + w2n c)))` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ `w2n c < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
    \\ Q.ABBREV_TAC `d = iPUSH c`
    \\ Q.ABBREV_TAC `fi = (r3 + 0x9w =+ 0x0w)
        ((r3 + 0x8w =+ 0x0w)
           ((r3 + 0x7w =+ 0x0w)
              ((r3 + 0x6w =+ n2w (w2n c))
                 ((r3 + 0x5w =+ 0xB8w)
                    ((r3 + 0x4w =+ 0x7w)
                       ((r3 + 0x3w =+ 0x89w)
                          ((r3 + 0x2w =+ 0x4w)
                             ((r3 + 0x1w =+ 0xEFw)
                                ((r3 =+ 0x83w) f)))))))))`
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH d)) cs ((n =+ SOME r3) j)
         (fun2set (fi,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `d` \\ Q.UNABBREV_TAC `fi`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def,word_arith_lemma1,w2w_def]
      \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
    \\ Q.PAT_X_ASSUM `!q j g. bbb` (MP_TAC o
         Q.SPECL [`q * one_string r6 (iENCODE1 d) (r6 + 2w)`,`(n =+ SOME r3) j`,
                  `g`,`fi`,`r3 + n2w (INSTR_LENGTH d)`,`r4 + 8w`, `r6+2w`,
                  `pp * MAP_ROW r4 (((n:num) =+ SOME r3) j n)`,`hi`])
    \\ Q.UNABBREV_TAC `d`
    \\ ASM_SIMP_TAC std_ss [ALIGNED]
    \\ SIMP_TAC std_ss [iENCODE1_def,INSTR_LENGTH_def,one_string_def,
         MAP,one_list_def,SEP_CLAUSES,stringTheory.ORD_CHR_RWT,
         one_list_def,iIMM_def,MAP,APPEND,word_arith_lemma1]
    \\ SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ STRIP_TAC
    \\ POP_ASSUM (ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH o RW [GSYM AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [word_add_n2w]
    \\ Q.EXISTS_TAC `j2`
    \\ ASM_SIMP_TAC std_ss []
    \\ `j2 n = SOME r3` by METIS_TAC [DECIDE ``n < n+1``,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1 (`p < n + 1 /\ ~(n = p)` by DECIDE_TAC \\ METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM iFETCH_NOT_NONE])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ SEP_READ_TAC)
  \\ Q.PAT_X_ASSUM `!q j g. bbb` (K ALL_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `(IS_JUMP (iJUMP c))` by EVAL_TAC
    \\ Q.ABBREV_TAC `d = iJUMP c`
    \\ SIMP_TAC std_ss [x86_write_jcc_def,x86_write_jcc_pre_def]
    \\ `g (r6 + 1w) = n2w (ORD (CHR (48 + w2n c)))` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `fi = SND (SND (SND (x86_encodes_jump (r3,n2w (w2n c),df,f))))`
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH d)) cs ((n =+ SOME r3) j)
         (fun2set (fi,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `d` \\ Q.UNABBREV_TAC `fi`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def]
      \\ SIMP_TAC std_ss [word_arith_lemma1]
    \\ REPEAT STRIP_TAC
    \\ `(SEP_BYTES_IN_MEM r3 [y;y';y'';y''';y''''] * r) (fun2set (f,df))`
          by FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES,
                STAR_ASSOC,word_arith_lemma1]
    \\ IMP_RES_TAC x86_encodes_jump_thm
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ Q.EXISTS_TAC `bs` \\ ASM_SIMP_TAC std_ss [])
    \\ `x86_encodes_jump (r3,n2w (w2n c),df,f) = (r3 + 5w,n2w (w2n c),df,fi)` by (Q.UNABBREV_TAC `fi` \\ SIMP_TAC std_ss [x86_encodes_jump_def,LET_DEF])
    \\ ASM_SIMP_TAC std_ss [x86_encodes_jump_pre_def,LET_DEF]
    \\ Q.EXISTS_TAC `(n =+ SOME r3) j` \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `d` \\ FULL_SIMP_TAC std_ss [INSTR_LENGTH_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ SIMP_TAC std_ss [DECIDE ``n < m ==> ~(n = m:num)``]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def])
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def,ENCODES_JUMP_def]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES,X86_IMMEDIATE_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ SEP_READ_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `(IS_JUMP (iJEQ c))` by EVAL_TAC
    \\ Q.ABBREV_TAC `d = iJEQ c`
    \\ SIMP_TAC std_ss [x86_write_jcc_def,x86_write_jcc_pre_def,LET_DEF]
    \\ `g (r6 + 1w) = n2w (ORD (CHR (48 + w2n c)))` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ Q.ABBREV_TAC `f3 = (r3 + 0x7w =+ 0x0w)
              ((r3 + 0x6w =+ 0x0w)
                 ((r3 + 0x5w =+ 0x0w)
                    ((r3 + 0x4w =+ 0x5w)
                       ((r3 + 0x3w =+ 0x84w)
                          ((r3 + 0x2w =+ 0xFw)
                             ((r3 + 0x1w =+ 0x7w)
                                ((r3 =+ 0x3Bw) f)))))))`
    \\ `?f4. x86_encodes_jump (r3 + 0x8w,n2w n + 0x1w,df,f3) =
             (r3 + 0xDw,n2w n + 0x1w,df,f4)` by
          SIMP_TAC std_ss [x86_encodes_jump_def,LET_DEF,word_arith_lemma1]
    \\ ASM_SIMP_TAC std_ss []
    \\ `?f5. x86_encodes_jump (r3 + 0xDw,n2w (w2n c),df,f4) =
             (r3 + 0x12w,n2w (w2n c),df,f5)` by
          SIMP_TAC std_ss [x86_encodes_jump_def,LET_DEF,word_arith_lemma1]
    \\ ASM_SIMP_TAC std_ss [x86_encodes_jump_pre_def,LET_DEF,GSYM CONJ_ASSOC]
    \\ SIMP_TAC std_ss [word_arith_lemma1]
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH d)) cs ((n =+ SOME r3) j) (fun2set (f5,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `d`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def,word_arith_lemma1]
      \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
      \\ Q.SPEC_TAC (`y`,`y0`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'`,`y1`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''`,`y2`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''`,`y3`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''`,`y4`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''`,`y5`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''`,`y6`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''`,`y7`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''`,`y8`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''`,`y9`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''`,`y10`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''`,`y11`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''''`,`y12`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''''`,`y13`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''''''`,`y14`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''''''`,`y15`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''''''''`,`y16`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''''''''`,`y17`) \\ STRIP_TAC
      \\ REPEAT STRIP_TAC
      \\ `(SEP_BYTES_IN_MEM (r3 + 8w) [y8;y9;y10;y11;y12] *
          (SEP_BYTES_IN_MEM r3 [0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w] *
           SEP_BYTES_IN_MEM (r3 + 13w) [y13;y14;y15;y16;y17] * r)) (fun2set (f3,df))` by
        (Q.UNABBREV_TAC `f3`
         \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES,word_arith_lemma1]
         \\ SEP_WRITE_TAC)
      \\ Q.PAT_X_ASSUM `Abbrev (f3 = fff)` (K ALL_TAC)
      \\ `n + 1 < 256` by DECIDE_TAC
      \\ IMP_RES_TAC (Q.INST [`i`|->`i+1`] x86_encodes_jump_thm)
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `f2 = f4` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
      \\ `(SEP_BYTES_IN_MEM (r3 + 0xDw) [y13; y14; y15; y16; y17] *
        (SEP_BYTES_IN_MEM r3 [0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w] *
         SEP_BYTES_IN_MEM (r3 + 0x8w) bs * r))
         (fun2set (f2,df))` by FULL_SIMP_TAC (std_ss++star_ss) []
      \\ Q.PAT_X_ASSUM `(SEP_BYTES_IN_MEM (r3 + 0x8w) bs * rr) ggg` (K ALL_TAC)
      \\ IMP_RES_TAC (Q.INST [`i`|->`w2n (c:word7)`,`a`|->`a+0xDw`] x86_encodes_jump_thm)
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `f2' = f5` (fn th => FULL_SIMP_TAC std_ss [th])
      \\ IMP_RES_TAC (Q.SPEC `a + 8w` ENCODES_JUMP_IMP)
      \\ IMP_RES_TAC (Q.SPEC `a + 0xDw` ENCODES_JUMP_IMP)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w] ++
                       [z1; z2; z3; z4; z5] ++ [z1'; z2'; z3'; z4'; z5']`
      \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
       (Q.EXISTS_TAC `[z1; z2; z3; z4; z5]`
        \\ Q.EXISTS_TAC `[z1'; z2'; z3'; z4'; z5']`
        \\ ASM_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,word_arith_lemma1,SEP_CLAUSES,APPEND]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ Q.PAT_X_ASSUM `Abbrev (f3 = fff)` (K ALL_TAC)
    \\ Q.EXISTS_TAC `(n =+ SOME r3) j` \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `d` \\ FULL_SIMP_TAC std_ss [INSTR_LENGTH_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ SIMP_TAC std_ss [DECIDE ``n < m ==> ~(n = m:num)``]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def])
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ IMP_RES_TAC ENCODES_JUMP_IMP
    \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES,X86_IMMEDIATE_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ SEP_READ_TAC)
  THEN1
   (ONCE_REWRITE_TAC [x86_writecode_def,x86_writecode_pre_def]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
    \\ `(IS_JUMP (iJLT c))` by EVAL_TAC
    \\ Q.ABBREV_TAC `d = iJLT c`
    \\ SIMP_TAC std_ss [x86_write_jcc_def,x86_write_jcc_pre_def,LET_DEF]
    \\ `g (r6 + 1w) = n2w (ORD (CHR (48 + w2n c)))` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ Q.ABBREV_TAC `f3 = (r3 + 0x7w =+ 0x0w)
              ((r3 + 0x6w =+ 0x0w)
                 ((r3 + 0x5w =+ 0x0w)
                    ((r3 + 0x4w =+ 0x5w)
                       ((r3 + 0x3w =+ 0x84w)
                          ((r3 + 0x2w =+ 0xFw)
                             ((r3 + 0x1w =+ 0x7w)
                                ((r3 =+ 0x3Bw) f)))))))`
    \\ `?f4. x86_encodes_jump (r3 + 0x8w,n2w n + 0x1w,df,f3) =
             (r3 + 0xDw,n2w n + 0x1w,df,f4)` by
          SIMP_TAC std_ss [x86_encodes_jump_def,LET_DEF,word_arith_lemma1]
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4]
    \\ `?f5. x86_encodes_jump (r3 + 0xDw,n2w (w2n c),df,(r3 + 0x3w =+ 0x82w) f4) =
             (r3 + 0x12w,n2w (w2n c),df,f5)` by
          SIMP_TAC std_ss [x86_encodes_jump_def,LET_DEF,word_arith_lemma1]
    \\ ASM_SIMP_TAC std_ss [x86_encodes_jump_pre_def,LET_DEF,GSYM CONJ_ASSOC]
    \\ SIMP_TAC std_ss [word_arith_lemma1]
    \\ Q.EXISTS_TAC `(n =+ SOME r3) j` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ `CODE_INV (r3 + n2w (INSTR_LENGTH d)) cs ((n =+ SOME r3) j) (fun2set (f5,df))` by
     (MATCH_MP_TAC CODE_INV_UPDATE
      \\ Q.EXISTS_TAC `f` \\ Q.UNABBREV_TAC `d`
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def,INSTR_IN_MEM_def]
      \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,CODE_SPACE_UNWIND]
      \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,X86_ENCODE_def,SEP_BYTES_IN_MEM_def]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,CODE_SPACE_def,word_arith_lemma1]
      \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
      \\ Q.SPEC_TAC (`y`,`y0`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'`,`y1`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''`,`y2`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''`,`y3`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''`,`y4`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''`,`y5`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''`,`y6`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''`,`y7`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''`,`y8`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''`,`y9`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''`,`y10`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''`,`y11`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''''`,`y12`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''''`,`y13`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''''''`,`y14`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''''''`,`y15`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y''''''''''''''''`,`y16`) \\ STRIP_TAC
      \\ Q.SPEC_TAC (`y'''''''''''''''''`,`y17`) \\ STRIP_TAC
      \\ REPEAT STRIP_TAC
      \\ `(SEP_BYTES_IN_MEM (r3 + 8w) [y8;y9;y10;y11;y12] *
          (SEP_BYTES_IN_MEM r3 [0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w] *
           SEP_BYTES_IN_MEM (r3 + 13w) [y13;y14;y15;y16;y17] * r)) (fun2set (f3,df))` by
        (Q.UNABBREV_TAC `f3`
         \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES,word_arith_lemma1]
         \\ SEP_WRITE_TAC)
      \\ Q.PAT_X_ASSUM `Abbrev (f3 = fff)` (K ALL_TAC)
      \\ `n + 1 < 256` by DECIDE_TAC
      \\ IMP_RES_TAC (Q.INST [`i`|->`i+1`] x86_encodes_jump_thm)
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `f2 = f4` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
      \\ `(SEP_BYTES_IN_MEM (r3 + 0xDw) [y13; y14; y15; y16; y17] *
        (SEP_BYTES_IN_MEM r3 [0x3Bw; 0x7w; 0xFw; 0x82w; 0x5w; 0x0w; 0x0w; 0x0w] *
         SEP_BYTES_IN_MEM (r3 + 0x8w) bs * r))
         (fun2set ((r3 + 0x3w =+ 0x82w) f2,df))` by
       (FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,word_arith_lemma1,SEP_CLAUSES]
        \\ SEP_WRITE_TAC)
      \\ Q.PAT_X_ASSUM `(SEP_BYTES_IN_MEM (r3 + 0x8w) bs * rr) ggg` (K ALL_TAC)
      \\ IMP_RES_TAC (Q.INST [`i`|->`w2n (c:word7)`,`a`|->`a+0xDw`] x86_encodes_jump_thm)
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `f2' = f5` (fn th => FULL_SIMP_TAC std_ss [th])
      \\ IMP_RES_TAC (Q.SPEC `a + 8w` ENCODES_JUMP_IMP)
      \\ IMP_RES_TAC (Q.SPEC `a + 0xDw` ENCODES_JUMP_IMP)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x82w; 0x5w; 0x0w; 0x0w; 0x0w] ++
                       [z1; z2; z3; z4; z5] ++ [z1'; z2'; z3'; z4'; z5']`
      \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
       (Q.EXISTS_TAC `[z1; z2; z3; z4; z5]`
        \\ Q.EXISTS_TAC `[z1'; z2'; z3'; z4'; z5']`
        \\ ASM_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,word_arith_lemma1,SEP_CLAUSES,APPEND]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ Q.PAT_X_ASSUM `Abbrev (f3 = fff)` (K ALL_TAC)
    \\ Q.UNABBREV_TAC `d` \\ FULL_SIMP_TAC std_ss [INSTR_LENGTH_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [MATCH_MP MAP_INV_IGNORE (DECIDE ``n < n+1``)]
    \\ SIMP_TAC std_ss [DECIDE ``n < m ==> ~(n = m:num)``]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`i <> n` by DECIDE_TAC \\ METIS_TAC [])
    THEN1 (METIS_TAC [])
    THEN1
     (`(n + 1 <= p) \/ (n = p)` by DECIDE_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [ON_OFF_def]
      \\ ASM_SIMP_TAC std_ss [INSTR_LENGTH_def])
    \\ IMP_RES_TAC CODE_LOOP_UNROLL
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `(n =+ SOME r3) j`)
    \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
    \\ IMP_RES_TAC ENCODES_JUMP_IMP
    \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ Q.PAT_X_ASSUM `y = bbbb` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES,X86_IMMEDIATE_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ SEP_READ_TAC));

val prev_jump_NONE = prove(
  ``!j cs n. n < LENGTH cs /\ (!p. ON_OFF cs j p) ==>
             ((j (prev_jump cs n) = NONE) = (j n = NONE))``,
  STRIP_TAC \\ STRIP_TAC \\ Induct
  \\ SIMP_TAC std_ss [prev_jump_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `IS_JUMP (EL n cs)` \\ FULL_SIMP_TAC std_ss [ADD1]
  \\ `n < LENGTH cs` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `?c. EL n cs = c` by METIS_TAC []
  \\ `?c2. EL (n+1) cs = c2` by METIS_TAC []
  \\ IMP_RES_TAC iFETCH_IMP
  \\ FULL_SIMP_TAC std_ss [ON_OFF_def]);

val MAP_INV_DROP_THM = prove(
  ``!n i j a cs. MAP_INV a i j cs = MAP_INV a i j (TAKE n cs) * MAP_INV (a + n2w (8 * n)) (i + n) j (DROP n (cs:input_type list))``,
  Induct \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [TAKE_0,DROP_0,SEP_CLAUSES,MAP_INV_def,WORD_ADD_0]
  \\ Cases_on `cs` \\ SIMP_TAC std_ss [MAP_INV_def,DROP_def,SEP_CLAUSES,TAKE_def]
  \\ SIMP_TAC std_ss [MULT_CLAUSES,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [RW1[ADD_COMM]ADD1,ADD_ASSOC]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`i+1`,`j`,`a + 8w`,`t`])
  \\ ASM_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC std_ss [STAR_ASSOC,MAP_INV_def]);

val IS_JUMP_prev_jump = prove(
  ``!n cs. 0 < prev_jump cs n ==> IS_JUMP (EL (prev_jump cs n - 1) cs)``,
  Induct \\ SIMP_TAC std_ss [prev_jump_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `IS_JUMP (EL n cs)` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []);

val iFETCH_IMP_EL = prove(
  ``!p cs i. (iFETCH p cs = SOME i) ==> (EL p cs = i)``,
  Induct \\ Cases \\ ASM_SIMP_TAC std_ss [iFETCH_def,EL,HD,ADD1,TL]);

val IMP_ON_OFF = prove(
  ``(!p. (prev_jump cs n) <= p ==> ON_OFF cs j2 p) /\
    (!p. ON_OFF cs j p) /\
    (!p. p < prev_jump cs n ==> (j p = j2 p)) ==>
    (!p. ON_OFF cs j2 p)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
  \\ Cases_on `prev_jump cs n <= p` THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [DECIDE ``~(n <= m) = m < n:num``]
  \\ Cases_on `p + 1 < prev_jump cs n` THEN1
   (RES_TAC \\ `ON_OFF cs j p` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [ON_OFF_def])
  \\ `(prev_jump cs n = p + 1) /\ 0 < prev_jump cs n` by DECIDE_TAC
  \\ IMP_RES_TAC IS_JUMP_prev_jump
  \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [ON_OFF_def]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC iFETCH_IMP_EL
  \\ FULL_SIMP_TAC std_ss []);

val MAP_INV_TAKE_EQ = prove(
  ``!k a cs i.
      (!p. p < i + k ==> (j p = j2 p)) ==>
      (MAP_INV a i j (TAKE k cs) = MAP_INV a i j2 (TAKE k (cs:input_type list)))``,
  Induct \\ SIMP_TAC std_ss [TAKE_0,MAP_INV_def]
  \\ Cases_on `cs` \\ SIMP_TAC std_ss [TAKE_def,MAP_INV_def]
  \\ SIMP_TAC std_ss [ADD1,MAP_INV_def] \\ REPEAT STRIP_TAC
  \\ `i < i + (k + 1)` by DECIDE_TAC
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(p = q) ==> (f m p = f m q)``)
  \\ Q.PAT_X_ASSUM `!a cs. bb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]);

val x86_newcode_thm = prove(
  ``  LENGTH cs < 128 /\ ALIGNED r7 /\ n < LENGTH cs /\
      (CODE_INV r3 cs j) (fun2set (f,df)) /\
      (pp * one (r7 - 0x20w,n2w n) * one (r7 - 8w,r3) * one (r7 - 4w,r6) * MAP_INV r7 0 j cs) (fun2set (h,dh)) /\
      (q * one_string_0 r6 (iENCODE cs) b1) (fun2set (g,dg)) ==>
      (!p. ON_OFF cs j p) /\
      ((r1 = 0w) = (j n = NONE)) ==>
      ?f2 h2 j2 r3i.
        x86_newcode_pre (r1,n2w n,r7,df,f,dg,g,dh,h) /\
        (x86_newcode (r1,n2w n,r7,df,f,dg,g,dh,h) =
           (r7,df,f2,dg,g,dh,h2)) /\
        ~(j2 n = NONE) /\
        (CODE_INV r3i cs j2) (fun2set (f2,df)) /\
        (pp * one (r7 - 0x20w,n2w n) * one (r7 - 8w,r3i) * one (r7 - 4w,r6) * MAP_INV r7 0 j2 cs) (fun2set (h2,dh)) /\
        (!p. ON_OFF cs j2 p) /\ !i. ~(j i = NONE) \/ LENGTH cs <= i ==> (j2 i = j i)``,
  SIMP_TAC std_ss [x86_newcode_def,x86_newcode_pre_def]
  \\ REVERSE (Cases_on `j n = NONE`) \\ ASM_SIMP_TAC std_ss []
  THEN1 (REPEAT STRIP_TAC \\ Q.EXISTS_TAC `j` \\ Q.EXISTS_TAC `r3`
         \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ `(h (r7 - 4w) = r6) /\ (r7 - 4w) IN dh` by SEP_READ_TAC
  \\ `(h (r7 - 8w) = r3) /\ (r7 - 8w) IN dh` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ `LENGTH cs <= 128` by DECIDE_TAC
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
      Q.INST [`p`|->`n`,`r2`|->`r6`]) x86_findbyte_thm
  \\ `r7 - 0x20w IN dh /\ (h (r7 - 0x20w) = n2w n)` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED,word_arith_lemma2,
         DECIDE ``n < j = ~(j <= n:num)``]
  \\ `j (n - ji) = NONE` by METIS_TAC [prev_jump_NONE]
  \\ `n - ji < LENGTH cs` by DECIDE_TAC
  \\ `ALIGNED (r7 + n2w (8 * (n - ji)))` by
       (ASM_SIMP_TAC bool_ss [DECIDE ``8 = 4 * 2``,GSYM WORD_MULT_ASSOC,
          ALIGNED_CLAUSES,GSYM word_mul_n2w])
  \\ STRIP_ASSUME_TAC (Q.SPECL [`n - ji`,`0`,`j`,`r7`,`cs`] MAP_INV_DROP_THM)
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
  \\ MP_TAC (Q.INST [`q`|->`qi`,`pp`|->`pp * one (r7 - 0x20w,n2w n) * one (r7 - 0x8w,r3) * one (r7 - 0x4w,r6) * MAP_INV r7 0 j (TAKE (n - ji) cs)`]
       (MATCH_INST (SPEC_ALL x86_writecode_thm)
        ``x86_writecode (r3,r7 + 0x8w * n2w (n - ji),n2w (n - ji),r6i,df,f,dg,g,dh,h)``))
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w,STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,WORD_MUL_LSL,word_mul_n2w]
  \\ Q.EXISTS_TAC `j2` \\ Q.EXISTS_TAC `r3i`
  \\ `r7 - 0x8w IN dh` by SEP_READ_TAC
  \\ FULL_SIMP_TAC bool_ss [DECIDE ``m <= n + p = m - n <= p:num``]
  \\ `!p. ON_OFF cs j2 p` by METIS_TAC [IMP_ON_OFF]
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_ASSUME_TAC (Q.SPECL [`n - ji`,`0`,`j2`,`r7`,`cs`] MAP_INV_DROP_THM)
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`k`,`a`,`cs`,`0`] MAP_INV_TAKE_EQ))
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (GSYM prev_jump_NONE) \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 SEP_WRITE_TAC
  \\ METIS_TAC []);

val lemma1 = prove(
  ``!x. ((if x = NONE then 0x0w else 0x1w) = 0x0w) = (x = NONE)``,
  Cases \\ SIMP_TAC std_ss [n2w_11,ONE_LT_dimword,ZERO_LT_dimword]);

val x86_inc_thm = prove(
  ``state_inv cs dh h dg g df f r7 j /\ n < LENGTH cs /\
    ((h (r7 - 0x24w) = 0w) ==> cont_jump j p cs r4 (n2w n)) ==>
    ?h2 f2 j2 w.
       x86_inc_pre (r1,r2,r3,r4,n2w n,r6,r7,dh,h,df,f,dg,g) /\
       (x86_inc (r1,r2,r3,r4,n2w n,r6,r7,dh,h,df,f,dg,g) =
          (r1,r2,r3,w,0w,r6,r7,dh,h2,df,f2,dg,g)) /\
       state_inv cs dh h2 dg g df f2 r7 j2 /\ (j2 n = SOME w)``,
  SIMP_TAC std_ss [state_inv_def,SimpLHS,MAP_TEMP_INV_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [x86_inc_def,x86_inc_pre_def,LET_DEF]
  \\ Q.PAT_ABBREV_TAC `h3 = (r7 - 0x20w:word32 =+ (n2w n):word32) fff`
  \\ `?ww. (SEP_T * one (r7 - 0xCw,r1) * one (r7 - 0x10w,r2) * one (r7 - 0x14w,r3) *
            one (r7 - 0x18w,r4) * one (r7 - 0x1Cw,r6) * one (r7 - 0x24w,ww) *
            one (r7 - 0x20w,n2w n) * one (r7 - 0x8w,a) * one (r7 - 0x4w,b) *
            MAP_INV r7 0 j cs) (fun2set (h3,dh))` by
   (FULL_SIMP_TAC std_ss [TEMP_INV_UNROLL,word_arith_lemma1,TEMP_INV_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
    \\ Q.EXISTS_TAC `y''''''` \\ Q.UNABBREV_TAC `h3` \\ SEP_WRITE_TAC)
  \\ `h (r7 - 0x24w) = ww` by
   (`h (r7 - 0x24w) = h3 (r7 - 0x24w)` by (Q.UNABBREV_TAC `h3`
       \\ SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,WORD_EQ_ADD_LCANCEL,
         word_sub_def,word_2comp_n2w,n2w_11])
    \\ ASM_SIMP_TAC std_ss [] \\ SEP_READ_TAC)
  \\ Q.PAT_X_ASSUM `Abbrev bbb` (K ALL_TAC)
  \\ `LENGTH cs <= 128` by DECIDE_TAC
  \\ IMP_RES_TAC x86_access_j_thm
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
  \\ REPEAT (Q.PAT_X_ASSUM `x86_access_j bb = nnn` (K ALL_TAC))
  \\ REPEAT (Q.PAT_X_ASSUM `x86_access_j_pre bb` (K ALL_TAC))
  \\ ASM_SIMP_TAC std_ss []
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [SEP_CLAUSES] o
   Q.INST [`r3`|->`a`,`r6`|->`b`,`pp`|->`SEP_T * one (r7 - 0xCw,r1) * one (r7 - 0x10w,r2) *
       one (r7 - 0x14w,r3) * one (r7 - 0x18w,r4) * one (r7 - 0x1Cw,r6) * one (r7 - 0x24w,ww)`,`q`|->`emp`] o
   RW [lemma1,GSYM AND_IMP_INTRO] o MATCH_INST x86_newcode_thm)
      ``x86_newcode (if (j:num->word32 option) n = NONE
        then 0x0w else 0x1w,n2w n,r7,df,f,dg,g,dh,h3)``
  \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `x86_newcode bb = nnn` (K ALL_TAC))
  \\ REPEAT (Q.PAT_X_ASSUM `x86_newcode_pre bb` (K ALL_TAC))
  \\ `h2 (r7 - 0x20w) = n2w n` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC x86_access_j_thm
  \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `x86_access_j bb = nnn` (K ALL_TAC))
  \\ REPEAT (Q.PAT_X_ASSUM `x86_access_j_pre bb` (K ALL_TAC))
  \\ Cases_on `j2 n` \\ FULL_SIMP_TAC std_ss []
  \\ `h2 (r7 - 0x18w) = r4` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < 128` by DECIDE_TAC
  \\ `(ww = 0w) ==> cont_jump j2 p cs r4 (n2w n)` by
    (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [cont_jump_def,input_type_11])
  \\ (STRIP_ASSUME_TAC o UNDISCH o UNDISCH o UNDISCH o UNDISCH o
   REWRITE_RULE [GSYM CODE_INV_def] o
   Q.INST [`r`|->`CODE_SPACE r3i (SPACE_LENGTH 0 j2 cs)`] o
   SIMP_RULE (std_ss++SIZES_ss) [WORD_SUB_ADD,w2n_n2w,GSYM AND_IMP_INTRO] o
   DISCH ``n < 128`` o Q.INST [`t`|->`n2w n`,`j`|->`j2`] o
   MATCH_INST x86_write_jump_cond_thm) ``x86_write_jump_cond (ww,x,r4 + 0x5w,df,f2)``
  \\ `h2 (r7 - 0x24w) = ww` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `j2`
  \\ ASM_SIMP_TAC std_ss [CONJ_ASSOC]
  \\ STRIP_TAC THEN1 SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `r3i`
  \\ Q.EXISTS_TAC `b`
  \\ Q.EXISTS_TAC `b1`
  \\ ASM_SIMP_TAC std_ss [TEMP_INV_UNROLL,word_arith_lemma1]
  \\ SIMP_TAC std_ss [SEP_CLAUSES,TEMP_INV_def,STAR_ASSOC]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ Q.EXISTS_TAC `r1`
  \\ Q.EXISTS_TAC `r2`
  \\ Q.EXISTS_TAC `r3`
  \\ Q.EXISTS_TAC `r4`
  \\ Q.EXISTS_TAC `r6`
  \\ Q.EXISTS_TAC `n2w n`
  \\ Q.EXISTS_TAC `0w`
  \\ SEP_WRITE_TAC);

val SPEC_PUSH_COND = prove(
  ``SPEC m (p * cond b) c q ==> SPEC m (p * cond b) c (q * cond b)``,
  SIMP_TAC std_ss [SPEC_MOVE_COND,SEP_CLAUSES]);

val X86_STACK_def = Define `
  X86_STACK (esp,xs,l) = xR ESP esp * xLIST esp xs *
    xSPACE esp l * cond (ALIGNED esp)`;

val pop_esi = let
  val ((th,_,_),_) = prog_x86Lib.x86_spec (x86_encodeLib.x86_encode "pop esi")
  val th = Q.INST [`df`|->`{esp}`] (DISCH ``ALIGNED esp`` th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM,ALIGNED] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND] th
  val th = SPEC_FRAME_RULE th ``xLIST (esp+4w) xs * xSPACE esp n * cond (ALIGNED esp)``
  val th = HIDE_POST_RULE ``xM esp`` th
  val th = HIDE_PRE_RULE ``xR ESI`` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``xPC eip * X86_STACK (esp,w::xs,n) * ~xR ESI``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [X86_STACK_def,SEP_IMP_MOVE_COND,
      ALIGNED_INTRO,SEP_CLAUSES,xLIST_def]
    \\ SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL])
  val th = MP th lemma
  val (th,goal) = SPEC_WEAKEN_RULE th ``xPC (eip+1w) * X86_STACK (esp+4w,xs,n+1) * xR ESI w``
  val lemma = prove(goal,
    SIMP_TAC (bool_ss++sep_cond_ss) [X86_STACK_def,SEP_IMP_MOVE_COND,
      ALIGNED_INTRO,SEP_CLAUSES,xLIST_def,xSPACE_def,GSYM ADD1]
    \\ SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL,WORD_ADD_SUB,ALIGNED,SEP_CLAUSES])
  val th = DISCH_ALL (MP th lemma)
  val th = Q.INST [`esp`|->`esp-4w`,`n`|->`0`,`xs`|->`[]`] th
  val th = SIMP_RULE std_ss [WORD_SUB_ADD] th
  in RW [] th end

val (codege_code_def,x86_inc_lemma) = let
  val th = DISCH
  ``x86_inc (eax,edx,edi,esi,ecx,ebx,ebp,dh,h,df,f,dg,g) =
            (eax,edx,edi,w,0w,ebx,ebp,dh,h3,df,f3,dg,g)`` x86_inc_th
  val th = DISCH ``ALIGNED edi`` th
  val th = DISCH ``state_inv cs dh h dg g df f ebp j /\ n < LENGTH cs /\
    ((h (ebp - 0x24w) = 0w) ==> cont_jump j pi cs esi (n2w n))`` th
  val th = SIMP_RULE std_ss [LET_DEF] th
  val th = RW [GSYM SPEC_MOVE_COND] th
  val ((sub_esi,_,_),_) = prog_x86Lib.x86_spec (x86_encodeLib.x86_encode "sub esi, 5")
  val (_,_,sts,_) = prog_x86Lib.x86_tools
  val sub_esi = HIDE_STATUS_RULE true sts sub_esi
  val th = SPEC_COMPOSE_RULE [Q.INST [`w`|->`esi`] pop_esi,sub_esi,th,xCODE_INTRO]
  val th = RW [STAR_ASSOC] th
  val th = SIMP_RULE (std_ss++sep_cond_ss) [] th
  val th = MATCH_MP SPEC_PUSH_COND th
  val th = Q.INST [`eip`|->`p`] th
  val (_,_,c,_) = dest_spec (concl th)
  val tm = ``(codegen_code (p:word32)):word32 # word8 list # bool -> bool``
  val def = new_definition("codegen_code",mk_eq(tm,c))
  val th = RW [GSYM def] th
  val th = RW [STAR_ASSOC] (RW1 [GSYM X86_SPEC_CODE] th)
  val th = Q.SPEC `xLIST edi xs * xSPACE edi l` (MATCH_MP SPEC_FRAME th)
  val th = RW [STAR_ASSOC] th
  val th = Q.INST [`eax`|->`x`,`p`|->`ebx`,`ecx`|->`n2w n`,`esi`|->`cp + 5w`] th
  val th = SIMP_RULE std_ss [WORD_SUB_ADD,WORD_ADD_SUB] th
  in (def,th) end

(* main invariant definition: xINC_def *)

val xINC_def = Define `
  xINC (xs,l,p,cs:input_type list) (pw,r,esp) =
    SEP_EXISTS dh dg df jw g h f j eip.
      xR EBX pw * xCODE (codegen_code pw) * ~xR ESI * xR ECX 0w *
      xSTACK (xs,l,p,cs) * xMEMORY dh h * xBYTE_MEMORY dg g * xR EDX r *
      xR EBP jw * ~xS * xPC eip * xCODE (xCODE_SET df f) * X86_STACK (esp,[],1) *
      cond (state_inv cs dh h dg g df f jw j /\ (j p = SOME eip))`;

val xINC_CODEGEN_def = Define `
  xINC_CODEGEN (xs,l,p,cs:input_type list) (pw,r,esp) t =
    SEP_EXISTS dh h dg g df f jw j cp.
      xR EBX pw * xCODE (codegen_code pw) * ~xR ESI * xR ECX (n2w t) *
      xSTACK (xs,l,p,cs) * xMEMORY dh h * xBYTE_MEMORY dg g * xR EDX r *
      xR EBP jw * ~xS * xPC pw * xBYTE_MEMORY_X df f * X86_STACK (esp-4w,[cp+5w],0) *
      cond (state_inv cs dh h dg g df f jw j /\ p < LENGTH cs /\ t < LENGTH cs /\
         ((h (jw - 0x24w) = 0x0w) ==> cont_jump j p cs cp (n2w t)))`;

val xINC_JUMP_def = Define `
  xINC_JUMP (xs,l,p,cs:input_type list) (pw,r,esp) t =
    SEP_EXISTS dh dg df jw g h f j eip bs.
      xR EBX pw * xCODE (codegen_code pw) * ~xR ESI * xR ECX 0w *
      xSTACK (xs,l,p,cs) * xMEMORY dh h * xBYTE_MEMORY dg g * xR EDX r *
      xR EBP jw * ~xS * xPC eip * xCODE (xCODE_SET df f) * X86_STACK (esp,[],1) *
      cond (state_inv cs dh h dg g df f jw j /\ t < LENGTH cs /\
            ENCODES_JUMP eip t j bs /\ BYTES_IN_MEM eip df f bs /\
            cont_jump j p cs eip (n2w t))`;

val xINC_STOP_def = Define `
  xINC_STOP (xs,l,p,cs:input_type list) (pw,r,esp) =
    SEP_EXISTS dh dg df jw g h f.
      xR EBX pw * xCODE (codegen_code pw) * ~xR ESI * xR ECX 0w *
      xSTACK (xs,l,p,cs) * xMEMORY dh h * xBYTE_MEMORY dg g * xR EDX r *
      xR EBP jw * ~xS * xPC r * xCODE (xCODE_SET df f) * X86_STACK (esp,[],1)`;

fun QGENL [] th = th
  | QGENL (x::xs) th = Q.GEN x (QGENL xs th)

fun QEXISTSL_TAC [] = ALL_TAC
  | QEXISTSL_TAC (x::xs) = Q.EXISTS_TAC x \\ (QEXISTSL_TAC xs)

val xINC_CODEGEN_THM = let
  val th = x86_inc_lemma
  val (th,goal) = SPEC_WEAKEN_RULE th ``xINC (x::xs,l,n,cs) (ebx,edx,esp)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_MOVE_COND]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC x86_inc_thm
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`ebx`,`edi`,`edx`,`x`])
    \\ FULL_SIMP_TAC std_ss [xINC_def,xSTACK_def,SEP_CLAUSES,STAR_ASSOC]
    \\ SIMP_TAC (std_ss++sep_cond_ss) []
    \\ SIMP_TAC std_ss [SEP_IMP_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [Q.ISPEC `xR ESI` SEP_HIDE_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS_THM]
    \\ Q.EXISTS_TAC `dh`
    \\ Q.EXISTS_TAC `dg`
    \\ Q.EXISTS_TAC `df`
    \\ Q.EXISTS_TAC `ebp`
    \\ Q.EXISTS_TAC `g`
    \\ Q.EXISTS_TAC `h3`
    \\ Q.EXISTS_TAC `f3`
    \\ Q.EXISTS_TAC `j2`
    \\ Q.EXISTS_TAC `w`
    \\ Q.EXISTS_TAC `edi`
    \\ Q.EXISTS_TAC `w`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ METIS_TAC [])
  val th = MP th lemma
  val th = Q.INST [`n`|->`t`] th
  val th = QGENL [`w`,`pi`,`j`,`h3`,`h`,`g`,`f3`,`f`,`cp`,`edi`,`ebp`,`dh`,`dg`,`df`] th
  val th = SIMP_RULE std_ss [SPEC_PRE_EXISTS] th
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``xINC_CODEGEN (x::xs,l,p,cs) (ebx,edx,esp) t``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,xINC_CODEGEN_def,SEP_EXISTS_THM]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM iFETCH_NOT_NONE]
    \\ IMP_RES_TAC x86_inc_thm
    \\ FULL_SIMP_TAC std_ss [xINC_def,SEP_CLAUSES,STAR_ASSOC,xSTACK_def,SEP_EXISTS_THM]
    \\ Q.PAT_X_ASSUM `!r6' r3' r2' r1'. ?h2. bbb` (STRIP_ASSUME_TAC o Q.SPECL [`ebx`,`edi`,`edx`,`x`])
    \\ REPEAT (Q.PAT_X_ASSUM `!b. bb` (K ALL_TAC))
    \\ QEXISTSL_TAC [`w`,`p`,`j`,`h2`,`h`,`g`,`f2`,`f`,
         `cp`,`edi`,`jw`,`dh`,`dg`,`df`]
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val lemma = prove(
    ``SPEC X86_MODEL (xINC_CODEGEN (xs,l,p,cs) (ebx,edx,esp) t) {}
                     (xINC (xs,l,t,cs) (ebx,edx,esp))``,
    Cases_on `xs`
    THEN1 SIMP_TAC std_ss [xINC_CODEGEN_def,xSTACK_def,SEP_CLAUSES,SPEC_FALSE_PRE]
    \\ SIMP_TAC std_ss [RW [] (DISCH_ALL th)])
  in lemma end;


(* proving that the generated code + the code generator simulate the bytecode *)

val fix_jump = let
  val lemma1 = EVAL ``(5w:word32) >>> 8``
  val lemma2 = EVAL ``(5w:word32) >>> 16``
  val lemma3 = EVAL ``(5w:word32) >>> 24``
  val lemma4 = EVAL ``(w2w (5w:word32)):word8``
  val lemma5 = EVAL ``(w2w (0w:word32)):word8``
  in SIMP_RULE std_ss [word_arith_lemma1] o
     RW [lemma1,lemma2,lemma3,lemma4,lemma5] o Q.INST [`imm32`|->`5w`] end;

val je_th = fix_jump je_lemma
val je_nop_th = fix_jump je_nop_lemma
val jb_th = fix_jump jb_lemma
val jb_nop_th = fix_jump jb_nop_lemma;

val SPEC_EXISTS_EXISTS = prove(
  ``(!x. SPEC m (p x) c (q x)) ==> SPEC m (SEP_EXISTS x. p x) c (SEP_EXISTS x. q x)``,
  SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS] \\ REPEAT STRIP_TAC
  \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o
      SPEC_ALL o UNDISCH o SPEC_ALL) SPEC_WEAKEN
  \\ Q.EXISTS_TAC `q x`
  \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS]
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val iEXEC_IMP = prove(
  ``!xs l p cs t. iEXEC (xs,l,p,cs) t ==> ~(iFETCH p cs = NONE)``,
  ONCE_REWRITE_TAC [iEXEC_cases] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PAIR_EQ,iSTEP_cases]
  \\ NTAC 2 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss []);

val state_inv_IMP = prove(
  ``(iFETCH p cs = SOME c) /\
    state_inv cs dh h dg g df f jw j /\ (j p = SOME eip) ==>
    (~(iFETCH (p + 1) cs = NONE) /\ ~IS_JUMP c ==>
     (j (p + 1) = SOME (eip + n2w (INSTR_LENGTH c)))) /\
    ?bs. X86_ENCODE c eip p j bs /\ BYTES_IN_MEM eip df f bs``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [state_inv_def]
  THEN1 METIS_TAC [ON_OFF_def]
  \\ IMP_RES_TAC CODE_LOOP_UNROLL
  \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [CODE_INV_def,INSTR_IN_MEM_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ Q.EXISTS_TAC `y` \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `ppp (fun2set (f,df))` MP_TAC
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ Q.SPEC_TAC (`q * CODE_SPACE a (SPACE_LENGTH 0 j cs)`,`x`)
  \\ Q.SPEC_TAC (`eip`,`a`)
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `y`
  \\ ASM_SIMP_TAC std_ss [BYTES_IN_MEM_def,SEP_BYTES_IN_MEM_def,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SEP_READ_TAC);

val SEP_EXISTS_EQ = prove(
  ``(SEP_EXISTS z. p z * cond (x = z)) = p x``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,SEP_EXISTS,cond_STAR]);

val SPEC_POST_EXISTS = prove(
  ``!m p c q. (?x. SPEC m p c (q x)) ==> SPEC m p c (SEP_EXISTS x. q x)``,
  REPEAT STRIP_TAC
  \\ sg `SEP_IMP (q x) (SEP_EXISTS x. q x)`
  \\ IMP_RES_TAC SPEC_WEAKEN
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC []);

val CASES_ON_xs1 = prove(
  ``(xs1 = []) \/ ?x xs. (xs1:word32 list) = x::xs``,
  Cases_on `xs1` \\ SIMP_TAC std_ss [CONS_11]);

val SPEC_COMPOSE_LEMMA = prove(
  ``!x p m q. SPEC x p {} m /\ SPEC x m {} q ==> SPEC x p {} q``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC SPEC_COMPOSE
  \\ FULL_SIMP_TAC std_ss [UNION_IDEMPOT]);

val xBYTE_MEMORY_X_FLIP = prove(
  ``SPEC X86_MODEL p {(a,xs,T)} q /\ BYTES_IN_MEM a df f xs ==>
    SPEC X86_MODEL (p * xCODE (xCODE_SET df f)) {}
                   (q * xBYTE_MEMORY_X df f)``,
  REPEAT STRIP_TAC
  \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o
      SPEC_ALL o UNDISCH_ALL o SPEC_ALL) SPEC_WEAKEN
  \\ Q.EXISTS_TAC `q * xCODE (xCODE_SET df f)`
  \\ SIMP_TAC std_ss [RW1[STAR_COMM] X86_SPEC_CODE]
  \\ STRIP_TAC THEN1 (METIS_TAC [SPEC_X86_MODEL_IN_BYTE_MEM])
  \\ MATCH_MP_TAC SEP_IMP_STAR
  \\ SIMP_TAC std_ss [SEP_IMP_REFL,xCODE_IMP_BYTE_MEMORY]);

val xINC_JUMP_THM = prove(
  ``SPEC X86_MODEL (xINC_JUMP (xs,l,p,cs) (v,r,e) t) {}
                   (xINC (xs,l,t,cs) (v,r,e))``,
  SIMP_TAC std_ss [xINC_JUMP_def]
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS]
  \\ SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ REVERSE (FULL_SIMP_TAC std_ss [ENCODES_JUMP_def]) THEN1
   (SIMP_TAC std_ss [xINC_def]
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `dh`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `dg`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `df`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `jw`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `g`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `h`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `f`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `j`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `w`
    \\ Cases_on `xs` \\ SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE,xSTACK_def]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [STAR_ASSOC,SEP_CLAUSES]
    \\ ONCE_REWRITE_TAC [STAR_COMM]
    \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ SIMP_TAC std_ss [RW1 [STAR_COMM] X86_SPEC_CODE]
    \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] SPEC_X86_MODEL_IN_BYTE_MEM))
    \\ Q.EXISTS_TAC `bs` \\ Q.EXISTS_TAC `eip`
    \\ ASM_SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND]
    \\ `xPC w = xPC (eip + 5w + (w - eip - 0x5w))` by
       (SIMP_TAC std_ss [WORD_ADD_ASSOC]
        \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
        \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,WORD_SUB_ADD])
    \\ Cases_on `ALIGNED edi`
    \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
    \\ Q.SPEC_TAC (`h'`,`hh`) \\ STRIP_TAC
    \\ Q.SPEC_TAC (`t'`,`tt`) \\ STRIP_TAC
    \\ SPEC_PROVE_TAC [Q.INST [`imm32`|->`w - eip - 5w`] jmp_lemma])
  \\ MATCH_MP_TAC SPEC_COMPOSE_LEMMA
  \\ Q.EXISTS_TAC `xINC_CODEGEN (xs,l,p,cs) (v,r,e) t`
  \\ SIMP_TAC std_ss [xINC_CODEGEN_THM]
  \\ SIMP_TAC std_ss [xINC_CODEGEN_def]
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `dh`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `h`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `dg`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `g`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `df`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `f`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `jw`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `j`
  \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `eip`
  \\ `p < LENGTH cs` by
   (`~(j p = NONE)` by FULL_SIMP_TAC std_ss [cont_jump_def]
    \\ FULL_SIMP_TAC std_ss [state_inv_def]
    \\ `~(LENGTH cs <= p)` by METIS_TAC [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ MATCH_MP_TAC SPEC_COMPOSE_LEMMA
  \\ Q.EXISTS_TAC `
       (X86_STACK (e,[],1) * xR EBX v * xCODE (codegen_code v) * ~xR ESI *
        xR ECX (n2w t) * xSTACK (xs,l,p,cs) * xMEMORY dh h *
        xBYTE_MEMORY dg g * xR EDX r * xR EBP jw * ~xS * xPC (eip+3w) *
        xCODE (xCODE_SET df f))`
  \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC std_ss [RW1[STAR_COMM]X86_SPEC_CODE]
    \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] SPEC_X86_MODEL_IN_BYTE_MEM))
    \\ Q.EXISTS_TAC `[0x83w; 0xF1w; n2w t]` \\ Q.EXISTS_TAC `eip`
    \\ Q.PAT_X_ASSUM `BYTES_IN_MEM eip df f bs` MP_TAC
    \\ FULL_SIMP_TAC std_ss [BYTES_IN_MEM_def,word_arith_lemma1]
    \\ REPEAT STRIP_TAC
    \\ `n2w t = (sw2sw ((n2w t):word8)):word32` by
     (SIMP_TAC (std_ss++SIZES_ss) [sw2sw_def,bitTheory.SIGN_EXTEND_def,
          LET_DEF,w2n_n2w,bitTheory.BIT_def,bitTheory.BITS_THM]
      \\ FULL_SIMP_TAC std_ss [state_inv_def]
      \\ `t < 128 /\ t < 256` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO])
    \\ ASM_SIMP_TAC std_ss [] \\ SPEC_PROVE_TAC [xor_lemma])
  \\ MATCH_MP_TAC (GEN_ALL xBYTE_MEMORY_X_FLIP)
  \\ Q.EXISTS_TAC `[0xFFw; 0xD3w]` \\ Q.EXISTS_TAC `eip+3w`
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `BYTES_IN_MEM eip df f bs` MP_TAC
  \\ FULL_SIMP_TAC std_ss [BYTES_IN_MEM_def,word_arith_lemma1]
  \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (bool_ss++sep_cond_ss) [X86_STACK_def,xLIST_def,
       ALIGNED,xSPACE_def,SEP_CLAUSES, GSYM (EVAL ``SUC 0``),SPEC_MOVE_COND]
  \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
  \\ SPEC_PROVE_TAC [SIMP_RULE std_ss [word_arith_lemma1]
       (Q.INST [`eip`|->`eip+3w`,`esp`|->`e`] call_lemma)]);

val iSTEP_INIT_TAC =
    STRIP_ASSUME_TAC CASES_ON_xs1
    THEN1 FULL_SIMP_TAC std_ss [xINC_def,xSTACK_def,SEP_CLAUSES,
            SPEC_FALSE_PRE,NOT_NIL_CONS]
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [xINC_def]
    \\ NTAC 8 (HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC)
    \\ SIMP_TAC std_ss [xINC_def,GSYM SPEC_PRE_EXISTS]
    \\ SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC iEXEC_IMP
    \\ IMP_RES_TAC state_inv_IMP
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def,IS_JUMP_def]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS_EQ,INSTR_LENGTH_def]
    \\ FULL_SIMP_TAC std_ss [SEP_BYTES_IN_MEM_def,SEP_CLAUSES]
    \\ ONCE_REWRITE_TAC [STAR_COMM] \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ SIMP_TAC std_ss [RW1 [STAR_COMM] X86_SPEC_CODE]
    \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] SPEC_X86_MODEL_IN_BYTE_MEM))
    \\ Q.EXISTS_TAC `bs` \\ Q.EXISTS_TAC `eip`
    \\ Q.PAT_X_ASSUM `bs = xxx` (fn th => FULL_SIMP_TAC std_ss [th])
    \\ REPEAT (Q.PAT_X_ASSUM `yyy = xxx:word8 list` (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT (Q.PAT_X_ASSUM `BYTES_IN_MEM eip df f bss` (K ALL_TAC))
    \\ SIMP_TAC bool_ss [xSTACK_def,SEP_CLAUSES,xLIST_def,xSPACE_def,GSYM ADD1]
    \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS] \\ STRIP_TAC
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]

val BYTES_IN_MEM_APPEND = prove(
  ``!xs ys a.
      BYTES_IN_MEM a df f (xs ++ ys) =
      BYTES_IN_MEM a df f xs /\ BYTES_IN_MEM (a + n2w (LENGTH xs)) df f ys``,
  Induct \\ ASM_SIMP_TAC std_ss [BYTES_IN_MEM_def,LENGTH,APPEND,WORD_ADD_0]
  \\ SIMP_TAC std_ss [ADD1,word_arith_lemma1,AC ADD_COMM ADD_ASSOC]
  \\ METIS_TAC []);

val iSTEP2_TAC =
    ASM_SIMP_TAC std_ss [xINC_JUMP_THM]
    \\ SIMP_TAC std_ss [xINC_def,xINC_JUMP_def]
    \\ NTAC 8 (HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC)
    \\ SIMP_TAC std_ss [xINC_def,GSYM SPEC_PRE_EXISTS]
    \\ SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC iEXEC_IMP
    \\ IMP_RES_TAC state_inv_IMP
    \\ Q.PAT_X_ASSUM `BYTES_IN_MEM eip df f bs` MP_TAC
    \\ Q.PAT_X_ASSUM `X86_ENCODE c eip p j bs` MP_TAC
    \\ SIMP_TAC std_ss [X86_ENCODE_def] \\ STRIP_TAC
    \\ IMP_RES_TAC ENCODE_JUMP_LENGTH
    \\ FULL_SIMP_TAC std_ss [BYTES_IN_MEM_APPEND,LENGTH_APPEND,LENGTH,GSYM iFETCH_NOT_NONE]
    \\ REPEAT STRIP_TAC

val iSTEP3_TAC =
    FULL_SIMP_TAC std_ss [n2w_w2n,IS_JUMP_def]
    \\ FULL_SIMP_TAC std_ss [cont_jump_def,input_type_11,WORD_ADD_SUB,SEP_CLAUSES]
    \\ ONCE_REWRITE_TAC [STAR_COMM] \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ SIMP_TAC std_ss [RW1 [STAR_COMM] X86_SPEC_CODE]
    \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] SPEC_X86_MODEL_IN_BYTE_MEM))

val iSTEP_xINC = prove(
  ``iSTEP (xs1,l,p,cs) (xs2,l2,p2,cs2) /\ iEXEC (xs2,l2,p2,cs2) tt ==>
    SPEC X86_MODEL (xINC (xs1,l,p,cs) (v,r,e)) {} (xINC (xs2,l2,p2,cs2) (v,r,e))``,
  SIMP_TAC std_ss [iSTEP_cases] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1
   (iSTEP_INIT_TAC \\ Q.EXISTS_TAC `edi`
    \\ SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [sub_lemma])
  THEN1
   (iSTEP_INIT_TAC \\ Q.EXISTS_TAC `edi`
    \\ SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [swap_lemma])
  THEN1
   (iSTEP_INIT_TAC \\ Q.EXISTS_TAC `edi + 4w`
    \\ SIMP_TAC std_ss [SEP_CLAUSES,ALIGNED]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND,WORD_ADD_SUB]
    \\ SPEC_PROVE_TAC [pop_lemma])
  THEN1
   (iSTEP_INIT_TAC \\ Q.EXISTS_TAC `edi - 4w`
    \\ SIMP_TAC std_ss [SEP_CLAUSES,ALIGNED]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND,WORD_SUB_ADD]
    \\ SPEC_PROVE_TAC [push_lemma])
  THEN1
   (MATCH_MP_TAC SPEC_COMPOSE_LEMMA
    \\ Q.EXISTS_TAC `xINC_JUMP (xs1,l,p,cs) (v,r,e) (w2n w)`
    \\ SIMP_TAC std_ss [xINC_JUMP_THM]
    \\ SIMP_TAC std_ss [xINC_def,xINC_JUMP_def]
    \\ NTAC 8 (HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC)
    \\ SIMP_TAC std_ss [xINC_def,GSYM SPEC_PRE_EXISTS]
    \\ SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC iEXEC_IMP
    \\ IMP_RES_TAC state_inv_IMP
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `eip`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `bs`
    \\ `cont_jump j p cs eip w` by METIS_TAC [cont_jump_def]
    \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def,n2w_w2n,
         GSYM iFETCH_NOT_NONE,SEP_CLAUSES,SPEC_REFL])
  THEN1
   (MATCH_MP_TAC SPEC_COMPOSE_LEMMA
    \\ Q.EXISTS_TAC `xINC_JUMP (xs1,l,p,cs) (v,r,e) (w2n w)`
    \\ iSTEP2_TAC
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `eip+13w`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `bs2`
    \\ iSTEP3_TAC
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w]` \\ Q.EXISTS_TAC `eip`
    \\ ASM_SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,STAR_ASSOC,xLIST_def]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [je_th])
  THEN1
   (MATCH_MP_TAC SPEC_COMPOSE_LEMMA
    \\ Q.EXISTS_TAC `xINC_JUMP (xs1,l,p,cs) (v,r,e) (p + 1)`
    \\ iSTEP2_TAC
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `eip+8w`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `bs1`
    \\ `w2n ((n2w (p + 1)):word7) = p + 1` by
         (FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,state_inv_def] \\ DECIDE_TAC)
    \\ iSTEP3_TAC
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x84w; 0x5w; 0x0w; 0x0w; 0x0w]` \\ Q.EXISTS_TAC `eip`
    \\ ASM_SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,STAR_ASSOC,xLIST_def]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC
    \\ Q.PAT_X_ASSUM `x <> y` MP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [je_nop_th])
  THEN1
   (MATCH_MP_TAC SPEC_COMPOSE_LEMMA
    \\ Q.EXISTS_TAC `xINC_JUMP (xs1,l,p,cs) (v,r,e) (w2n w)`
    \\ iSTEP2_TAC
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `eip+13w`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `bs2`
    \\ iSTEP3_TAC
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x82w; 0x5w; 0x0w; 0x0w; 0x0w]` \\ Q.EXISTS_TAC `eip`
    \\ ASM_SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,STAR_ASSOC,xLIST_def]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC
    \\ Q.PAT_X_ASSUM `x <+ y` MP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [jb_th])
  THEN1
   (MATCH_MP_TAC SPEC_COMPOSE_LEMMA
    \\ Q.EXISTS_TAC `xINC_JUMP (xs1,l,p,cs) (v,r,e) (p + 1)`
    \\ iSTEP2_TAC
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `eip+8w`
    \\ HO_MATCH_MP_TAC SPEC_POST_EXISTS \\ Q.EXISTS_TAC `bs1`
    \\ `w2n ((n2w (p + 1)):word7) = p + 1` by
         (FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,state_inv_def] \\ DECIDE_TAC)
    \\ iSTEP3_TAC
    \\ Q.EXISTS_TAC `[0x3Bw; 0x7w; 0xFw; 0x82w; 0x5w; 0x0w; 0x0w; 0x0w]` \\ Q.EXISTS_TAC `eip`
    \\ ASM_SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,STAR_ASSOC,xLIST_def]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC
    \\ Q.PAT_X_ASSUM `~(x <+ y)` MP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [jb_nop_th]));

val iEXEC_IMP = prove(
  ``!xs l p cs t. iEXEC (xs,l,p,cs) t ==> ?i2. iFETCH p cs = SOME i2``,
  ONCE_REWRITE_TAC [iEXEC_cases] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PAIR_EQ,iSTEP_cases]);

val sinduction = IndDefLib.derive_strong_induction(iEXEC_rules,iEXEC_ind);

val iEXEC_xINC = prove(
  ``!s t. iEXEC s t ==>
          SPEC X86_MODEL (xINC s (v,r,e)) {} (xINC_STOP t (v,r,e))``,
  HO_MATCH_MP_TAC sinduction \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (MATCH_MP_TAC SPEC_COMPOSE_LEMMA
    \\ Q.EXISTS_TAC `xINC s' (v,r,e)`
    \\ `?xs l p cs. s = (xs,l,p,cs)` by METIS_TAC [PAIR]
    \\ `?xs2 l2 p2 cs2. s' = (xs2,l2,p2,cs2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC iSTEP_xINC
    \\ FULL_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [xINC_STOP_def,xINC_def,SEP_CLAUSES]
  \\ NTAC 7 (HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ STRIP_TAC)
  \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC state_inv_IMP
  \\ FULL_SIMP_TAC std_ss [IS_JUMP_def]
  \\ Q.PAT_X_ASSUM `BYTES_IN_MEM eip df f bs` MP_TAC
  \\ Q.PAT_X_ASSUM `X86_ENCODE iSTOP eip p j bs` MP_TAC
  \\ FULL_SIMP_TAC std_ss [X86_ENCODE_def]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ SIMP_TAC std_ss [RW1[STAR_COMM]X86_SPEC_CODE]
  \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] SPEC_X86_MODEL_IN_BYTE_MEM))
  \\ Q.EXISTS_TAC `bs` \\ Q.EXISTS_TAC `eip` \\ ASM_SIMP_TAC std_ss []
  \\ SPEC_PROVE_TAC [jmp_edx_lemma]);

val xINC_CODEGEN_STOP_THM = prove(
  ``SPEC X86_MODEL
     (xINC_CODEGEN (xs,l,p,cs) (v,r,e) t * cond (iEXEC (xs,l,t,cs) s)) {}
     (xINC_STOP s (v,r,e))``,
  SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SPEC_COMPOSE_LEMMA
  \\ Q.EXISTS_TAC `xINC (xs,l,t,cs) (v,r,e)`
  \\ ASM_SIMP_TAC std_ss [iEXEC_xINC,xINC_CODEGEN_THM]);

val SEP_IMP_PRE_EXISTS = prove(
  ``SEP_IMP (SEP_EXISTS x. p x) q = !x. SEP_IMP (p x) q``,
  SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []);

val SEP_IMP_xINC_STOP = prove(
  ``SEP_IMP (xINC_STOP s (v,r,e))
            (xSTACK s * X86_STACK (e,[],1) *
             xPC r * SEP_T * xCODE (codegen_code v))``,
  NTAC 2 (ONCE_REWRITE_TAC [STAR_COMM] \\ SIMP_TAC std_ss [STAR_ASSOC])
  \\ `?xs l p cs. s = (xs,l,p,cs)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ `xINC_STOP (xs,l,p,cs) (v,r,e) =
     SEP_EXISTS dh dg df jw g h f.
       xR EBX v * ~xR ESI * xR ECX 0x0w *
       xMEMORY dh h * xBYTE_MEMORY dg g *
       xR EDX r * xR EBP jw * ~xS * xCODE (xCODE_SET df f) *
       xCODE (codegen_code v) * xSTACK (xs,l,p,cs) * X86_STACK (e,[],1) * xPC r` by (SIMP_TAC (std_ss++star_ss) [xINC_STOP_def])
  \\ ASM_SIMP_TAC std_ss [SEP_IMP_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ REPEAT (MATCH_MP_TAC SEP_IMP_STAR \\ SIMP_TAC std_ss [SEP_IMP_REFL])
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_T_def]);

val xINC_SETUP_def = Define `
  xINC_SETUP cs =
    SEP_EXISTS dh h dg g df f jw.
      xBYTE_MEMORY_X df f * xMEMORY dh h * xBYTE_MEMORY dg g * xR EBP jw *
      cond (state_inv cs dh h dg g df f jw (\x.NONE) /\ ~(h (jw - 0x24w) = 0x0w))`;

val PRE_LEMMA = prove(
  ``SEP_IMP (SEP_EXISTS cp.
               xINC_SETUP cs * xR EBX pw * ~xR ESI * xR ECX 0w *
               xSTACK (xs,l,0,cs) * xR EDX r * xPC pw * ~xS *
               X86_STACK (esp - 0x4w,[cp],0) * cond (iEXEC (xs,l,0,cs) s) *
               xCODE (codegen_code pw))
       (xINC_CODEGEN (xs,l,0,cs) (pw,r,esp) 0 * cond (iEXEC (xs,l,0,cs) s))``,
  SIMP_TAC std_ss [xINC_CODEGEN_def,xINC_SETUP_def,SEP_CLAUSES]
  \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC
  \\ QEXISTSL_TAC [`dh`,`h`,`dg`,`g`,`df`,`f`,`jw`,`\x.NONE`,`cp-5w`]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_SUB_ADD]
  \\ IMP_RES_TAC iEXEC_IMP
  \\ Cases_on `cs` \\ FULL_SIMP_TAC std_ss [iFETCH_def,LENGTH])

val code_generator_length = let
  val tms = list_dest pred_setSyntax.dest_insert ((cdr o concl o SPEC_ALL) codege_code_def)
  val (x,y) = (dest_pair o last o butlast) tms
  val x = Arbnum.toInt (numSyntax.dest_numeral (cdr (cdr x)))
  val i = (length o fst o listSyntax.dest_list o fst o dest_pair) y
  in x + i end

val assign_eip_to_ebx = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th1,_,_),_) = spec (x86_encode "call 0")
  val ((th2,_,_),_) = spec (x86_encode "mov ebx,[esp]")
  val ((th3,_,_),_) = spec (x86_encode "add ebx,12")
  val th = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th1,th2,th3])
  val th = RW [STAR_ASSOC,combinTheory.APPLY_UPDATE_THM,WORD_ADD_0] th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th
  val th = Q.INST [`df`|->`{esp-4w}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM,ALIGNED,WORD_ADD_0] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND,x86_astTheory.Xrm_distinct] th
  val th = SIMP_RULE std_ss [word_arith_lemma1] th
  val th = HIDE_PRE_RULE ``xM (esp - 4w)`` th
  val th = SPEC_BOOL_FRAME_RULE th ``ALIGNED esp``
  val (th,goal) = SPEC_WEAKEN_RULE th ``xR EBX (eip + 0x11w) *
          xPC (eip + 0xBw) * ~xS * X86_STACK (esp-4w,[eip+5w],0)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [X86_STACK_def,xSPACE_def,xLIST_def,
      SEP_CLAUSES,ALIGNED,SEP_IMP_REFL])
  val th = MP th lemma
  val th = HIDE_PRE_RULE ``xR EBX`` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``~xR EBX *
          xPC eip * ~xS * X86_STACK (esp,[],1)``
  val lemma = prove(goal,
    SIMP_TAC (bool_ss++sep_cond_ss) [X86_STACK_def,xSPACE_def,xLIST_def,
      SEP_CLAUSES,ALIGNED,SEP_IMP_REFL,GSYM (EVAL ``SUC 0``)]
    \\ SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL])
  val th = MP th lemma
  val s = int_to_string (code_generator_length)
  val ((th0,_,_),_) = spec (x86_encode "mov ecx,0")
  val ((th4,_,_),_) = spec (x86_encode ("lea edx,[ebx+"^s^"]"))
  val th = SPEC_COMPOSE_RULE [th0,th,th4]
  val th = SIMP_RULE std_ss [STAR_ASSOC] th
  val th = HIDE_PRE_RULE ``xR EDX`` th
  val th = HIDE_PRE_RULE ``xR ECX`` th
  val th = RW [] (DISCH_ALL th)
  in th end;

val xINC_SETUP_THM = let
  val th = MATCH_MP (MATCH_MP SPEC_WEAKEN xINC_CODEGEN_STOP_THM) SEP_IMP_xINC_STOP
  val th = MATCH_MP (MATCH_MP SPEC_STRENGTHEN th) PRE_LEMMA
  val th = SPEC_ALL (SIMP_RULE std_ss [GSYM SPEC_PRE_EXISTS] th)
  val th = RW [RW1 [STAR_COMM] X86_SPEC_CODE] th
  val th = SPEC_COMPOSE_RULE [assign_eip_to_ebx,th]
  val th = SIMP_RULE std_ss [STAR_ASSOC,word_arith_lemma1] th
  in th end;

val _ = Parse.hide "zero_loop";
val (th1,zero_loop_def,zero_loop_pre_def) = compile "x86" ``
  zero_loop (r5:word32,r2:word32,r4:word32,dh:word32 set,h:word32->word32) =
    if r4 = 0w then (dh,h) else
      let h = (r2 =+ r5) h in
      let r2 = r2 + 4w in
      let r4 = r4 - 1w in
        zero_loop (r5,r2,r4,dh,h)``;

val _ = Parse.hide "x86_inc_init";
val (x86_inc_init_th,x86_inc_init_def,x86_inc_init_pre_def) = compile "x86" ``
  x86_inc_init (r2:word32,r4:word32,r7:word32,dh:word32 set,h:word32->word32) =
    let r5 = 1w:word32 in
    let h = (r7 =+ r5) h in
    let r7 = r7 + 36w in
    let h = (r7 - 4w =+ r2) h in
    let h = (r7 - 8w =+ r4) h in
    let r5 = 0w:word32 in
    let r2 = r7 in
    let r4 = 256w in
    let (dh,h) = zero_loop (r5,r2,r4,dh,h) in
      (r7,dh,h)``

val TEMP_SPACE_def = Define `
  (TEMP_SPACE a 0 = emp) /\
  (TEMP_SPACE a (SUC n) = SEP_EXISTS w. one (a:word32,w:word32) * TEMP_SPACE (a+4w) n)`;

val zero_loop_thm = prove(
  ``!n h dh r2 p.
      n < 1000 /\ ALIGNED r2 ==>
      (p * TEMP_SPACE r2 (2 * n)) (fun2set (h,dh)) ==>
      ?h2. zero_loop_pre (0w,r2,n2w (2 * n),dh,h) /\
           (zero_loop (0w,r2,n2w (2 * n),dh,h) = (dh,h2)) /\
           !k xs. (LENGTH (xs:input_type list) = n) ==> (p * MAP_INV r2 k (\x.NONE) xs) (fun2set (h2,dh))``,
  Induct THEN1
   (SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [zero_loop_def,zero_loop_pre_def]
    \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ Cases_on `xs`
    \\ FULL_SIMP_TAC std_ss [LENGTH,MAP_INV_def,TEMP_SPACE_def]
    \\ `F` by DECIDE_TAC)
  THEN1
   (SIMP_TAC std_ss [TEMP_SPACE_def,STAR_ASSOC,TIMES2,ADD,
      ADD_CLAUSES,SEP_CLAUSES,SEP_EXISTS_THM,word_arith_lemma1]
    \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [zero_loop_def,zero_loop_pre_def]
    \\ ONCE_REWRITE_TAC [zero_loop_def,zero_loop_pre_def]
    \\ SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,n2w_11,ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
    \\ `(n + n + 1) < 4294967296 /\ (n + n + 1 + 1) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,n2w_11,ADD1,word_add_n2w]
    \\ `n < 1000` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED,word_arith_lemma1]
    \\ `(p * one (r2,0w) * one (r2 + 0x4w,0w) * TEMP_SPACE (r2 + 0x8w) (n + n))
          (fun2set ((r2 + 0x4w =+ 0x0w) ((r2 =+ 0x0w) h),dh))` by SEP_WRITE_TAC
    \\ POP_ASSUM MP_TAC
    \\ Q.PAT_X_ASSUM `bbb (fun2set (h,dh))` (K ALL_TAC)
    \\ REPEAT STRIP_TAC
    \\ `ALIGNED (r2 + 8w)` by FULL_SIMP_TAC std_ss [ALIGNED]
    \\ FULL_SIMP_TAC std_ss [TIMES2]
    \\ RES_TAC \\ Q.PAT_X_ASSUM `!p q x. bb` (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC THEN1 SEP_READ_TAC THEN1 SEP_READ_TAC
    \\ Cases_on `xs`
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,MAP_INV_def,MAP_ROW_def,STAR_ASSOC]))

val LENGTH_EXISTS = prove(
  ``!n. ?xs. LENGTH xs = n``,
  Induct THEN1 (Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC std_ss [LENGTH])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `ARB::xs` \\ ASM_SIMP_TAC std_ss [LENGTH])

val LENGTH_EXTEND = prove(
  ``!n xs. LENGTH xs < n ==> ?ys. LENGTH (xs ++ ys) = n``,
  REPEAT STRIP_TAC
  \\ `?m. n = LENGTH xs + m` by (Q.EXISTS_TAC `n - LENGTH xs` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_EXISTS]);

val CODE_LOOP_NONE = prove(
  ``!cs k. CODE_LOOP k (\x. NONE) cs = emp``,
  Induct \\ ASM_SIMP_TAC std_ss [CODE_LOOP_def,INSTR_IN_MEM_def,SEP_CLAUSES]);

val SPACE_LENGTH_NONE = prove(
  ``!cs k. SPACE_LENGTH k (\x. NONE) cs = SUM (MAP INSTR_LENGTH cs)``,
  Induct \\ ASM_SIMP_TAC std_ss [SPACE_LENGTH_def,MAP,listTheory.SUM]);

(* CLEAN *)

fun RENAME_ALPHA_CONV tm = let
  val (v,t) = dest_abs tm
  val (name,ty) = dest_var v
  val cs = rev (explode name)
  fun primes ((#"'")::cs,n) = primes (cs,n+1)
    | primes (cs,n) = (cs,n)
  val (cs,n) = primes (cs,0)
  val _ = if n = 0 then fail() else n
  val vs = map (fst o dest_var) (all_vars tm)
  val v_name = implode cs
  fun find_name m = let
    val new_name = v_name ^ int_to_string m
    in if mem new_name vs then find_name (m+1) else new_name end
  val new_v = mk_var(find_name n,ty)
  in ALPHA_CONV new_v tm end handle HOL_ERR _ => NO_CONV tm

val CLEAN_CONV = DEPTH_CONV RENAME_ALPHA_CONV

fun SPEC_ALL_TAC (hs,goal) =
  (foldr (fn (v,t) => SPEC_TAC (v,v) THEN t) ALL_TAC (free_vars goal)) (hs,goal)

val CLEAN_TAC =
  ONCE_REWRITE_TAC [GSYM markerTheory.Abbrev_def]
  THEN REPEAT (POP_ASSUM MP_TAC)
  THEN SPEC_ALL_TAC
  THEN CONV_TAC CLEAN_CONV
  THEN REPEAT STRIP_TAC
  THEN PURE_ONCE_REWRITE_TAC [markerTheory.Abbrev_def]

(* / CLEAN *)

val MAP_INV_APPEND = prove(
  ``!xs ys a k.
      MAP_INV a k (\x. NONE) (xs++ys) =
      MAP_INV a k (\x. NONE) xs * MAP_INV (a + n2w (8 * LENGTH xs)) (k + LENGTH xs) (\x. NONE) ys``,
  Induct
  \\ ASM_SIMP_TAC std_ss [MAP_INV_def,SEP_CLAUSES,APPEND,LENGTH,
      WORD_ADD_0,MAP_ROW_def,STAR_ASSOC,MULT_CLAUSES,word_arith_lemma1]
  \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,ADD1])

val SEP_IMP_INTRO = prove(
  ``!p q x. SEP_IMP p q ==> (p x ==> q x)``,METIS_TAC [SEP_IMP_def]);

val xINC_SETUP_INTRO = prove(
  ``one_string_0 r3 (iENCODE cs) b1 (fun2set (g,dg)) /\ ALIGNED r5 /\
    (TEMP_SPACE r5 265) (fun2set (h,dh)) /\ LENGTH cs < 128 /\
    (CODE_SPACE r4 (SUM (MAP INSTR_LENGTH cs))) (fun2set (f,df)) ==>
      ?r4i h2. x86_inc_init_pre (r3,r4,r5,dh,h) /\
               (x86_inc_init (r3,r4,r5,dh,h) = (r4i,dh,h2)) /\
               state_inv cs dh h2 dg g df f r4i (\x.NONE) /\
               h2 (r4i - 0x24w) <> 0x0w``,
  ONCE_REWRITE_TAC [x86_inc_init_def,x86_inc_init_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO,ALIGNED,word_arith_lemma4]
  \\ REWRITE_TAC [GSYM (EVAL ``SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (256)))))))))``)]
  \\ REWRITE_TAC [TEMP_SPACE_def]
  \\ SIMP_TAC std_ss [SEP_CLAUSES,word_arith_lemma1,STAR_ASSOC,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `hi = (r5 + 0x1Cw =+ r4) ((r5 + 0x20w =+ r3) ((r5 =+ 0x1w) h))`
  \\ `(one (r5,1w) * one (r5 + 0x4w,w') * one (r5 + 0x8w,w'') *
       one (r5 + 0xCw,w''') * one (r5 + 0x10w,w'''') *
       one (r5 + 0x14w,w''''') * one (r5 + 0x18w,w'''''') *
       one (r5 + 0x1Cw,r4) * one (r5 + 0x20w,r3) *
       TEMP_SPACE (r5 + 0x24w) 256) (fun2set (hi,dh))` by
     (Q.UNABBREV_TAC `hi` \\ SEP_WRITE_TAC)
  \\ Q.PAT_X_ASSUM `bbbb (fun2set (h,dh))` (K ALL_TAC)
  \\ `ALIGNED (r5 + 0x24w)` by ASM_SIMP_TAC std_ss [ALIGNED]
  \\ Q.PAT_X_ASSUM `ALIGNED r5` (K ALL_TAC)
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPEC `128` zero_loop_thm))
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `0`)
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma4,WORD_ADD_0]
  \\ IMP_RES_TAC LENGTH_EXTEND
  \\ Q.PAT_X_ASSUM `!xs. bb` IMP_RES_TAC
  \\ `h2 r5 = 1w` by SEP_READ_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1 SEP_READ_TAC
  \\ FULL_SIMP_TAC std_ss [state_inv_def,ALIGNED,ON_OFF_def]
  \\ Q.EXISTS_TAC `r4`
  \\ Q.EXISTS_TAC `r3`
  \\ Q.EXISTS_TAC `b1`
  \\ ASM_SIMP_TAC std_ss [CODE_INV_def,CODE_LOOP_NONE,
       SPACE_LENGTH_NONE,SEP_CLAUSES]
  \\ ASM_SIMP_TAC std_ss [MAP_TEMP_INV_def,TEMP_INV_UNROLL,word_arith_lemma1,
       word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,SEP_EXISTS_THM,
       SEP_CLAUSES,STAR_ASSOC,TEMP_INV_def]
  \\ CLEAN_TAC \\ QEXISTSL_TAC [`w6`,`w5`,`w4`,`w3`,`w2`,`w1`,`1w`]
  \\ FULL_SIMP_TAC std_ss [MAP_INV_APPEND,STAR_ASSOC]
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC SEP_IMP_INTRO
  \\ MATCH_MP_TAC SEP_IMP_STAR
  \\ REVERSE STRIP_TAC THEN1 (SIMP_TAC std_ss [SEP_T_def,SEP_IMP_def])
  \\ SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL,WORD_ADD_0]);

val xINC_INIT_THM = let
  val imp = MATCH_INST xINC_SETUP_INTRO ``x86_inc_init (edx,esi,ebp,dh,h)``
  val tm = (fst o dest_imp o concl) imp
  val th = x86_inc_init_th
  val th = SPEC_FRAME_RULE th ``xBYTE_MEMORY_X df f * xBYTE_MEMORY dg g``
  val th = SPEC_BOOL_FRAME_RULE th tm
  val p = cdr (find_term (can (match_term ``xPC (p + n2w n)``)) (concl th))
  val (th,goal) = SPEC_WEAKEN_RULE th (subst [``p:word32``|->p] ``xINC_SETUP cs * ~xR ECX *
              ~xR EDX * ~xR ESI * xPC p * ~xS``)
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ STRIP_ASSUME_TAC (UNDISCH_ALL (RW [GSYM AND_IMP_INTRO] imp))
    \\ ASM_SIMP_TAC std_ss [LET_DEF,xINC_SETUP_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ QEXISTSL_TAC [`dh`,`h2`,`dg`,`g`,`df`,`f`,`r4i`]
    \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,AND_IMP_INTRO] th
  val tm2 = (fst o dest_imp o concl) th
  val goal = mk_imp(tm,tm2)
  val lemma = prove(goal,ASM_SIMP_TAC std_ss [] \\ METIS_TAC [imp])
  val th = RW [GSYM SPEC_MOVE_COND] (DISCH_ALL (MP th (UNDISCH lemma)))
  in th end;

val x86_incremental_jit = let
  val th = SPEC_COMPOSE_RULE [xINC_INIT_THM,xINC_SETUP_THM]
  val th = SIMP_RULE (std_ss++sep_cond_ss) [SEP_CLAUSES,STAR_ASSOC] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [codege_code_def,word_arith_lemma1] th
  in save_thm("x86_incremental_jit",th) end;

val _ = write_code_to_file "incremental-jit.s" x86_incremental_jit;

val _ = export_theory();
