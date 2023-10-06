
open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib simpLib;
open decoderTheory bit_listTheory opmonTheory;

open x64_astTheory x64_coretypesTheory;

val _ = new_theory "x64_decoder";
val _ = ParseExtras.temp_loose_equality()


(* ---------------------------------------------------------------------------------- *>

  A decoder for x86 instructions is defined and at the end pre-evaliuated for
  fast execution with EVAL.

  NOTES:

    All instructions can have a REX prefix, making them have access to
    16 registers.  Some instructions require a REX prefix. The REX
    prefic must appear immediately before the rest of opcode part of
    the instruction, i.e. after all the other prefixes.

    The presence of the REX prefix allows for 20 byte-valued registers
    (AL, AH, CL, CH, DL, DH, BL, BH, SPL, BPL, SIL, DIL and
    R8B-R15B). However, this implementation of the x86_64 semantics
    disallows use of AH, CH, DH, BH in order to make the semantics a
    bit more uniform. Formalised in instr_accesses_bad_byte_reg_def.

  ( Addresses are by default 64-bit, but an address-size override
    prefix (0x67) can turn the address size into 32-bits. This feature
    is not supported by this implementation of the x86_64 semantics. )

  TODO:
   - support address-size over-ride prefix
   - make sure the 16-bit operations performs the appropriate sw2sw

<* ---------------------------------------------------------------------------------- *)

(* reading hex strings to bit lists *)

val STR_SPACE_AUX_def = Define `
  (STR_SPACE_AUX n "" = "") /\
  (STR_SPACE_AUX n (STRING c s) =
     if n = 0 then STRING #" " (STRING c (STR_SPACE_AUX 1 s))
              else STRING c (STR_SPACE_AUX (n-1) s))`;

val bytebits_def = Define `
  bytebits = hex2bits o STR_SPACE_AUX 2`;

(* interprete the IA-32 manuals' syntax *)

val check_opcode_def = Define `
  check_opcode s =
    let y = (n2bits 3 o char2num o HD o TL o EXPLODE) s in
      assert (\g. g "Reg/Opcode" = y)`;

val read_SIB_def = Define `
  read_SIB =
    assign_drop "Base" 3 >> assign_drop "Index" 3 >> assign_drop "Scale" 2 >>
    option_try [
      assert (\g. (g "Mod" = [F;F]) /\  (g "Base" = [T;F;T])) >> assign_drop "disp32" 32;
      assert (\g. (g "Mod" = [F;F]) /\ ~(g "Base" = [T;F;T]));
      assert (\g. (g "Mod" = [T;F])) >> assign_drop "disp8" 8;
      assert (\g. (g "Mod" = [F;T])) >> assign_drop "disp32" 32]`;

val read_ModRM_def = Define `
  read_ModRM =
    assign_drop "R/M" 3 >> assign_drop "Reg/Opcode" 3 >> assign_drop "Mod" 2 >>
    option_try [
      assert (\g.  (g "Mod" = [T;T]));
      assert (\g.  (g "Mod" = [F;F]) /\ ~(g "R/M" = [F;F;T]) /\ ~(g "R/M" = [T;F;T]));
      assert (\g.  (g "Mod" = [F;F]) /\  (g "R/M" = [T;F;T])) >> assign_drop "disp32" 32;
      assert (\g.  (g "Mod" = [T;F]) /\ ~(g "R/M" = [F;F;T])) >> assign_drop "disp8" 8;
      assert (\g.  (g "Mod" = [F;T]) /\ ~(g "R/M" = [F;F;T])) >> assign_drop "disp32" 32;
      assert (\g. ~(g "Mod" = [T;T]) /\  (g "R/M" = [F;F;T])) >> read_SIB]`;

val is_hex_add_def = Define `
  is_hex_add x = ((IMPLODE o DROP 2 o EXPLODE) x = "+rd")`;

val process_hex_add_def = Define `
  process_hex_add name =
    let n = (hex2num o IMPLODE o TAKE 2 o EXPLODE) name in
      option_try [drop_eq (n2bits 8 (n+0)) >> assign "reg" (n2bits 3 0);
                  drop_eq (n2bits 8 (n+1)) >> assign "reg" (n2bits 3 1);
                  drop_eq (n2bits 8 (n+2)) >> assign "reg" (n2bits 3 2);
                  drop_eq (n2bits 8 (n+3)) >> assign "reg" (n2bits 3 3);
                  drop_eq (n2bits 8 (n+4)) >> assign "reg" (n2bits 3 4);
                  drop_eq (n2bits 8 (n+5)) >> assign "reg" (n2bits 3 5);
                  drop_eq (n2bits 8 (n+6)) >> assign "reg" (n2bits 3 6);
                  drop_eq (n2bits 8 (n+7)) >> assign "reg" (n2bits 3 7)]`;

val assign_drop_cond_def = Define `
  assign_drop_cond name i1 i2 c (g,bits) =
    if c g then assign_drop name i1 (g,bits)
           else assign_drop name i2 (g,bits)`;

val x64_match_step_def = Define `
  x64_match_step name =
    if is_hex name /\ (STRLEN name = 2) then     (* opcode e.g. FE, 83 and 04 *)
      drop_eq (n2bits 8 (hex2num name))
    else if is_hex_add name then                 (* opcode + rd, e.g. F8+rd *)
      process_hex_add name
    else if name = "1" then                           (* constant 1 *)
      assign_drop name 0
    else if MEM name ["ib";"cb";"rel8";"imm8"] then   (* 8-bit immediate or address *)
      assign_drop name 8
    else if MEM name ["iw";"cw";"imm16"] then         (* 16-bit immediate or address *)
      assign_drop name 16
    else if MEM name ["id";"cd";"rel32";"imm32"] then (* 32-bit immediate or address *)
      assign_drop_cond name 16 32 (\g. g "16BIT" = [T])
    else if MEM name ["iq";"imm64"] then              (* 64-bit immediate *)
      assign_drop name 64
    else if name = "/r" then                     (* normal reg + reg/mem *)
      read_ModRM
    else if MEM name ["/0";"/1";"/2";"/3";"/4";"/5";"/6";"/7"] then (* opcode extension in ModRM *)
      read_ModRM >> check_opcode name
    else if name = "REX.W" then
      assert (\g. g "REX.W" = [T])
    else if name = "REX" then
      assert (\g. g "REX.W" = [F])
    else if name = "+" then
      assert (\g. T)
    else
      option_fail`;

(* syntax classes *)

val x64_binop_def = Define `x64_binop =
  [("ADC",Zadc); ("ADD",Zadd); ("AND",Zand); ("CMP",Zcmp);
   ("OR",Zor); ("SAR",Zsar); ("SHR",Zshr); ("SHL",Zshl);
   ("SBB",Zsbb); ("SUB",Zsub); ("TEST",Ztest); ("XOR",Zxor)]`;

val x64_monop_def = Define `x64_monop =
  [("DEC",Zdec); ("INC",Zinc); ("NOT",Znot); ("NEG",Zneg)]`;



(* x86 - decoder *)

val b2reg_def = Define `
  b2reg g rex_name name = (EL (bits2num (g name ++ g rex_name))
    [RAX;RCX;RDX;RBX;RSP;RBP;RSI;RDI;zR8;zR9;zR10;zR11;zR12;zR13;zR14;zR15]):Zreg`;

val decode_Zr32_def = Define `
  decode_Zr32 g name =
    if name = "RAX" then RAX else
      if g "reg" = [] then b2reg g "REX.R" "Reg/Opcode"  (* "Reg/Opcode" comes from ModRM *)
                      else b2reg g "REX.B" "reg"`;       (* "reg" comes from opcode byte, e.g. "rd" in B8+rd *)

val decode_SIB_def = Define `
  decode_SIB g =
    let scaled_index = (if b2reg g "REX.X" "Index" = RSP then NONE else SOME (b2w g "Scale",b2reg g "REX.X" "Index")) in
      if b2reg g "REX.B" "Base" = RBP then (* the special case indicated by "[*]" *)
        if g "Mod" = [F;F] then Zm scaled_index NONE (sw2sw ((b2w g "disp32"):word32)) else
        if g "Mod" = [T;F] then Zm scaled_index (SOME RBP) (sw2sw ((b2w g "disp8"):word8)) else
        (* g "Mod" = [F;T] *)   Zm scaled_index (SOME RBP) (sw2sw ((b2w g "disp32"):word32))
      else (* normal cases, just need to read off the correct displacement *)
        let disp = (if (g "Mod" = [T;F]) then sw2sw ((b2w g "disp8"):word8) else sw2sw ((b2w g "disp32"):word32)) in
        let disp = (if (g "Mod" = [F;F]) then 0w else disp) in
          Zm scaled_index (SOME (b2reg g "REX.B" "Base")) disp`;

val decode_Zrm32_def = Define `  (* sw2sw = sign-extension *)
  decode_Zrm32 g name =
    if name = "RAX" then Zr RAX else
      if  (g "Mod" = [F;F]) /\ (g "R/M" = [T;F;T]) then Zm NONE NONE (sw2sw:word32->word64 (b2w g "disp32")) else
      if ~(g "Mod" = [T;T]) /\ (g "R/M" = [F;F;T]) then decode_SIB g else
      if  (g "Mod" = [F;F]) then Zm NONE (SOME (b2reg g "REX.B" "R/M")) 0w else
      if  (g "Mod" = [T;F]) then Zm NONE (SOME (b2reg g "REX.B" "R/M")) (sw2sw:word8->word64 (b2w g "disp8")) else
      if  (g "Mod" = [F;T]) then Zm NONE (SOME (b2reg g "REX.B" "R/M")) (sw2sw:word32->word64 (b2w g "disp32")) else
      if  (g "Mod" = [T;T]) then Zr (b2reg g "REX.B" "R/M") else Zr (b2reg g "REX.B" "reg") `;

val decode_Zconst_def = Define `
  decode_Zconst name g =
   if name = "imm8"  then sw2sw:word8 ->word64 (b2w g "ib") else
   if name = "rel8"  then sw2sw:word8 ->word64 (b2w g "cb") else
   if name = "imm16" then sw2sw:word16->word64 (b2w g "iw") else
   if name = "imm32" then sw2sw:word32->word64 (b2w g "id") else
   if name = "rel32" then sw2sw:word32->word64 (b2w g "cd") else
   if name = "imm64" then b2w g "iq" else
   if name = "1"     then 1w else 0w`;

val decode_Zdest_src_def = Define `
  decode_Zdest_src g dest src =
    if MEM src ["r64";"r32";"r16";"r8"] then
      Zrm_r (decode_Zrm32 g dest) (decode_Zr32 g src)
    else if MEM src ["r/m64";"r/m32";"r/m16";"r/m8"] then
      Zr_rm (decode_Zr32 g dest)  (decode_Zrm32 g src)
    else if src = "m" then
      Zr_rm (decode_Zr32 g dest)  (decode_Zrm32 g src)
    else
      Zrm_i (decode_Zrm32 g dest) (decode_Zconst src g)`;

val decode_Zconst_or_zero_def = Define `
  decode_Zconst_or_zero ts g =
    if LENGTH ts < 2 then 0w else decode_Zconst (EL 1 ts) g`;

val decode_Zimm_rm_def = Define `
  decode_Zimm_rm ts g =
    if MEM (EL 1 ts) ["r/m32";"r32";"r/m8";"r8"]
    then Zi_rm (decode_Zrm32 g (EL 1 ts))
    else Zi (decode_Zconst (EL 1 ts) g)`;

val x64_select_op_def = Define `
  x64_select_op name list = SND (HD (FILTER (\x. FST x = name) list))`;

val x86_size_def = Define `
  x86_size g name =
    if MEM name ["r8";"m8";"r/m8";"AL"] then Z8 else
    if MEM name ["r16";"m16";"r/m16";"AX"] then Z16 else
    if MEM name ["r64";"m64";"r/m64";"RAX"] then Z64 else
    if g "REX.W" = [T] then Z64 else
    if g "16BIT" = [T] then Z16 else Z32`;

val Zsize_tm = ``(x86_size g (EL 1 ts))``

val x64_syntax_binop = ``
  Zbinop (x64_select_op (HD ts) x64_binop) ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))``;

val x64_syntax_monop = ``
  Zmonop (x64_select_op (HD ts) x64_monop) ^Zsize_tm (decode_Zrm32 g (EL 1 ts))``;

val Z_SOME_def = Define `Z_SOME f = SOME o (\(g,w). (f g,w))`;

val x64_syntax_def = Define `
  x64_syntax ts =
    if LENGTH ts = 0 then option_fail else
    if HD ts = "MOVZX" then Z_SOME (\g. Zmovzx ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts)) (if EL 2 ts = "r/m8" then Z8 else Z16)) else
    if MEM (HD ts) (MAP FST x64_binop) then Z_SOME (\g. ^x64_syntax_binop) else
    if MEM (HD ts) (MAP FST x64_monop) then Z_SOME (\g. ^x64_syntax_monop) else
    if HD ts = "POP"  then Z_SOME (\g. Zpop  (decode_Zrm32 g (EL 1 ts))) else
    if HD ts = "PUSH" then Z_SOME (\g. Zpush (decode_Zimm_rm ts g)) else
    if HD ts = "CMPXCHG" then Z_SOME (\g. Zcmpxchg ^Zsize_tm (decode_Zrm32 g (EL 1 ts)) (decode_Zr32 g (EL 2 ts))) else
    if HD ts = "XCHG"    then Z_SOME (\g. Zxchg ^Zsize_tm (decode_Zrm32 g (EL 1 ts)) (decode_Zr32 g (EL 2 ts))) else
    if HD ts = "XADD"    then Z_SOME (\g. Zxadd ^Zsize_tm (decode_Zrm32 g (EL 1 ts)) (decode_Zr32 g (EL 2 ts))) else
    if (HD ts = "JMP") /\ (TL ts = ["r/m32"]) then Z_SOME (\g. Zjmp (decode_Zrm32 g (EL 1 ts))) else
    if HD ts = "JMP"     then Z_SOME (\g. Zjcc Z_ALWAYS (decode_Zconst_or_zero ts g)) else
    if HD ts = "JE"      then Z_SOME (\g. Zjcc Z_E (decode_Zconst_or_zero ts g)) else
    if HD ts = "JNE"     then Z_SOME (\g. Zjcc Z_NE (decode_Zconst_or_zero ts g)) else
    if HD ts = "JS"      then Z_SOME (\g. Zjcc Z_S (decode_Zconst_or_zero ts g)) else
    if HD ts = "JNS"     then Z_SOME (\g. Zjcc Z_NS (decode_Zconst_or_zero ts g)) else
    if HD ts = "JA"      then Z_SOME (\g. Zjcc Z_A (decode_Zconst_or_zero ts g)) else
    if HD ts = "JNA"     then Z_SOME (\g. Zjcc Z_NA (decode_Zconst_or_zero ts g)) else
    if HD ts = "JB"      then Z_SOME (\g. Zjcc Z_B (decode_Zconst_or_zero ts g)) else
    if HD ts = "JNB"     then Z_SOME (\g. Zjcc Z_NB (decode_Zconst_or_zero ts g)) else
    if HD ts = "LEA"     then Z_SOME (\g. Zlea ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "LOOP"    then Z_SOME (\g. Zloop Z_ALWAYS (decode_Zconst_or_zero ts g)) else
    if HD ts = "LOOPE"   then Z_SOME (\g. Zloop Z_E (decode_Zconst_or_zero ts g)) else
    if HD ts = "LOOPNE"  then Z_SOME (\g. Zloop Z_NE (decode_Zconst_or_zero ts g)) else
    if HD ts = "MOV"     then Z_SOME (\g. Zmov Z_ALWAYS ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVE"   then Z_SOME (\g. Zmov Z_E ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNE"  then Z_SOME (\g. Zmov Z_NE ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVS"   then Z_SOME (\g. Zmov Z_S ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNS"  then Z_SOME (\g. Zmov Z_NS ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVA"   then Z_SOME (\g. Zmov Z_A ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNA"  then Z_SOME (\g. Zmov Z_NA ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVB"   then Z_SOME (\g. Zmov Z_B ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNB"  then Z_SOME (\g. Zmov Z_NB ^Zsize_tm (decode_Zdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "MUL"     then Z_SOME (\g. Zmul ^Zsize_tm (decode_Zrm32 g (EL 1 ts))) else
    if HD ts = "DIV"     then Z_SOME (\g. Zdiv ^Zsize_tm (decode_Zrm32 g (EL 1 ts))) else
    if HD ts = "CALL"    then Z_SOME (\g. Zcall (decode_Zimm_rm ts g)) else
    if HD ts = "CPUID"   then Z_SOME (\g. Zcpuid) else
    if HD ts = "RET"     then Z_SOME (\g. Zret (decode_Zconst_or_zero ts g)) else option_fail`;


(* a list of x64 instructions, ordered by the combination of addressing modes they support *)

(* Each line which produces an operation over size Z32 can be modified
   into a size Z64 by setting REX.W. The Intel manual explicitly
   lisits each such inferrable line, but we allow such lines to be
   inferred from the 32-bit lines. For example, the line:

    " 81 /0 id  | ADD r/m32, imm32  ";

   Immediately, represents three lines in the manual, namely:

    " 81 /0 iw          | ADD r/m16, imm16  ";
    " 81 /0 id          | ADD r/m32, imm32  ";
    " REX.W + 81 /0 id  | ADD r/m64, imm32  ";

   Note that the size of the immediate constant does not change for 64-bit. *)

val x64_syntax_list = `` [

    " 05 id     | ADD EAX, imm32    ";
    " 15 id     | ADC EAX, imm32    ";
    " 25 id     | AND EAX, imm32    ";
    " 35 id     | XOR EAX, imm32    ";
    " 0D id     | OR EAX, imm32     ";
    " 1D id     | SBB EAX, imm32    ";
    " 2D id     | SUB EAX, imm32    ";
    " 3D id     | CMP EAX, imm32    ";

    " 83 /0 ib  | ADD r/m32, imm8   ";
    " 83 /1 ib  | OR r/m32, imm8    ";
    " 83 /2 ib  | ADC r/m32, imm8   ";
    " 83 /3 ib  | SBB r/m32, imm8   ";
    " 83 /4 ib  | AND r/m32, imm8   ";
    " 83 /5 ib  | SUB r/m32, imm8   ";
    " 83 /6 ib  | XOR r/m32, imm8   ";
    " 83 /7 ib  | CMP r/m32, imm8   ";

    " 81 /0 id  | ADD r/m32, imm32  ";
    " 81 /1 id  | OR r/m32, imm32   ";
    " 81 /2 id  | ADC r/m32, imm32  ";
    " 81 /3 id  | SBB r/m32, imm32  ";
    " 81 /4 id  | AND r/m32, imm32  ";
    " 81 /5 id  | SUB r/m32, imm32  ";
    " 81 /6 id  | XOR r/m32, imm32  ";
    " 81 /7 id  | CMP r/m32, imm32  ";

    " 01 /r     | ADD r/m32, r32    ";
    " 11 /r     | ADC r/m32, r32    ";
    " 21 /r     | AND r/m32, r32    ";
    " 31 /r     | XOR r/m32, r32    ";
    " 09 /r     | OR r/m32, r32     ";
    " 19 /r     | SBB r/m32, r32    ";
    " 29 /r     | SUB r/m32, r32    ";
    " 39 /r     | CMP r/m32, r32    ";

    " 03 /r     | ADD r32, r/m32    ";
    " 13 /r     | ADC r32, r/m32    ";
    " 23 /r     | AND r32, r/m32    ";
    " 33 /r     | XOR r32, r/m32    ";
    " 0B /r     | OR r32, r/m32     ";
    " 1B /r     | SBB r32, r/m32    ";
    " 2B /r     | SUB r32, r/m32    ";
    " 3B /r     | CMP r32, r/m32    ";

    " A9 id     | TEST EAX, imm32   ";
    " F7 /0 id  | TEST r/m32, imm32 ";
    " 85 /r     | TEST r/m32, r32   ";

    " 38 /r     | CMP r/m8, r8      ";
    " 3A /r     | CMP r8, r/m8      ";
    " 80 /7 ib  | CMP r/m8, imm8    ";
    " FE /0     | INC r/m8          ";
    " FE /1     | DEC r/m8          ";

    " REX.W + B8+rd iq | MOV r64, imm64    ";  (* need to mention this explicitly due to imm64 *)
    " B8+rd id         | MOV r32, imm32    ";  (* REX.W variant must be above in the list *)
    " C7 /0 id         | MOV r/m32, imm32  ";
    " C6 /0 ib         | MOV r/m8, imm8    ";
    " 8B /r            | MOV r32,r/m32     ";
    " 8A /r            | MOV r8,r/m8       ";
    " 89 /r            | MOV r/m32,r32     ";
    " 88 /r            | MOV r/m8, r8      ";

    " 0F B6 /r  | MOVZX r32, r/m8   ";
    " 0F B7 /r  | MOVZX r32, r/m16  ";

    " 0F B1 /r  | CMPXCHG r/m32, r32";
    " 0F C1 /r  | XADD r/m32, r32   ";
    " 90+rd     | XCHG EAX, r32     ";
    " 87 /r     | XCHG r/m32, r32   ";

    " FF /1     | DEC r/m32         ";
    " FF /0     | INC r/m32         ";
    " F7 /3     | NEG r/m32         ";
    " F7 /2     | NOT r/m32         ";
    " 8F /0     | POP r/m32         ";
    " 58+rd     | POP r32           ";
    " FF /6     | PUSH r/m32        ";
    " 50+rd     | PUSH r32          ";

    " E8 cd     | CALL rel32        ";
    " FF /2     | CALL r/m32        ";

    " 8D /r     | LEA r32, m        ";
    " D1 /4     | SHL r/m32, 1      ";
    " C1 /4 ib  | SHL r/m32, imm8   ";
    " D1 /5     | SHR r/m32, 1      ";
    " C1 /5 ib  | SHR r/m32, imm8   ";
    " D1 /7     | SAR r/m32, 1      ";
    " C1 /7 ib  | SAR r/m32, imm8   ";

    " FF /4     | JMP r/m32         ";
    " EB cb     | JMP rel8          ";
    " E9 cd     | JMP rel32         ";
    " 74 cb     | JE rel8           ";
    " 75 cb     | JNE rel8          ";
    " 0F 84 cd  | JE rel32          ";
    " 0F 85 cd  | JNE rel32         ";
    " 78 cb     | JS rel8           ";
    " 79 cb     | JNS rel8          ";
    " 0F 88 cd  | JS rel32          ";
    " 0F 89 cd  | JNS rel32         ";
    " 77 cb     | JA rel8           ";
    " 76 cb     | JNA rel8          ";
    " 0F 87 cd  | JA rel32          ";
    " 0F 86 cd  | JNA rel32         ";
    " 72 cb     | JB rel8           ";
    " 73 cb     | JNB rel8          ";
    " 0F 82 cd  | JB rel32          ";
    " 0F 83 cd  | JNB rel32         ";

    " 0F 44 /r  | CMOVE r32, r/m32  ";
    " 0F 45 /r  | CMOVNE r32, r/m32 ";
    " 0F 48 /r  | CMOVS r32, r/m32  ";
    " 0F 49 /r  | CMOVNS r32, r/m32 ";
    " 0F 47 /r  | CMOVA r32, r/m32  ";
    " 0F 46 /r  | CMOVNA r32, r/m32 ";
    " 0F 42 /r  | CMOVB r32, r/m32  ";
    " 0F 43 /r  | CMOVNB r32, r/m32 ";

    " 0F A2     | CPUID             ";

    " C3        | RET               "; (* short for "RET 0" *)
    " C2 iw     | RET imm16         ";
    " E2 cb     | LOOP rel8         ";
    " E1 cb     | LOOPE rel8        ";
    " E0 cb     | LOOPNE rel8       ";

    " F7 /6     | DIV r/m32         ";
    " F7 /4     | MUL r/m32         "

  ]``;

val x64_decode_aux_def = zDefine `
  x64_decode_aux g =
    (match_list_raw g x64_match_step tokenise (x64_syntax o tokenise) o
    MAP (\s. let x = STR_SPLIT [#"|"] s in (EL 0 x, EL 1 x))) ^x64_syntax_list`;

val x64_decode_prefixes_def = tDefine "x64_decode_prefixes" `
  x64_decode_prefixes w =
    if LENGTH w < 8 then ([],w) else
      let b = n2w (bits2num (TAKE 8 w)):word8 in
        if ~(MEM b [0x2Ew;0x3Ew;0xF0w;0x66w]) then ([],w) else
          let (pres,v) = x64_decode_prefixes (DROP 8 w) in
          let pre = (if b = 0x2Ew then Zbranch_not_taken else
                     if b = 0x3Ew then Zbranch_taken else
                     if b = 0xF0w then Zlock else
                     if b = 0x66w then Zoperand_size_override else ARB) in
            (pre :: pres, v)`
 (WF_REL_TAC `measure LENGTH`
  THEN ASM_SIMP_TAC std_ss [LENGTH_DROP] THEN REPEAT STRIP_TAC THEN DECIDE_TAC);

val x64_decode_REX_def = Define `
  x64_decode_REX w =
    let g = (\n. []) in
      if LENGTH w < 8 then (g,w) else
        if ~(TAKE 4 (DROP 4 w) = [F;F;T;F]) then (g,w) else
          let g = ("REX.B" =+ [EL 0 w]) g in
          let g = ("REX.X" =+ [EL 1 w]) g in
          let g = ("REX.R" =+ [EL 2 w]) g in
          let g = ("REX.W" =+ [EL 3 w]) g in
          let w = DROP 8 w in
            (g,w)`;

val dest_accesses_memory_def = Define `
  (dest_accesses_memory (Zrm_i rm i) = Zrm_is_memory_access rm) /\
  (dest_accesses_memory (Zrm_r rm r) = Zrm_is_memory_access rm) /\
  (dest_accesses_memory (Zr_rm r rm) = F)`;

val x64_lock_ok_def = Define `
  (x64_lock_ok (Zbinop binop_name dsize ds) =
    MEM binop_name [Zadd;Zand;Zor;Zsub;Zxor] /\
    dest_accesses_memory ds) /\
  (x64_lock_ok (Zmonop monop_name dsize rm) =
    MEM monop_name [Zdec;Zinc;Zneg;Znot] /\
    Zrm_is_memory_access rm) /\
  (x64_lock_ok (Zxadd dsize rm r) = Zrm_is_memory_access rm) /\
  (x64_lock_ok (Zxchg dsize rm r) = Zrm_is_memory_access rm) /\
  (x64_lock_ok (Zcmpxchg dsize rm r) = Zrm_is_memory_access rm) /\
  (x64_lock_ok (Zpop rm) = F) /\
  (x64_lock_ok (Zlea dsize ds) = F) /\
  (x64_lock_ok (Zpush imm_rm) = F) /\
  (x64_lock_ok (Zcall imm_rm) = F) /\
  (x64_lock_ok (Zret imm) = F) /\
  (x64_lock_ok (Zmov c dsize ds) = F) /\
  (x64_lock_ok (Zjcc c imm) = F) /\
  (x64_lock_ok (Zjmp rm) = F) /\
  (x64_lock_ok (Zloop c imm) = F) /\
  (x64_lock_ok (Zpushad) = F) /\
  (x64_lock_ok (Zpopad) = F)`;

val x64_is_jcc_def = Define `
  (x64_is_jcc (Zjcc c imm) = T) /\
  (x64_is_jcc _ = F)`;

val byte_regs_in_rm_def = Define `
  (byte_regs_in_rm (Zr r) = [r]) /\
  (byte_regs_in_rm (Zm r1 r2 offset) = [])`;

val byte_regs_in_ds_def = Define `
  (byte_regs_in_ds (Zrm_i rm i) = byte_regs_in_rm rm) /\
  (byte_regs_in_ds (Zrm_r rm r) = r::byte_regs_in_rm rm) /\
  (byte_regs_in_ds (Zr_rm r rm) = r::byte_regs_in_rm rm)`;

val has_bad_byte_regs_def = Define `
  has_bad_byte_regs dsize xs =
    (dsize = Z8) /\ ~(FILTER (\x. MEM x [RSP;RBP;RSI;RDI]) xs = [])`;

val instr_accesses_bad_byte_reg_def = Define `
  (instr_accesses_bad_byte_reg (Zbinop binop_name dsize ds) = has_bad_byte_regs dsize (byte_regs_in_ds ds)) /\
  (instr_accesses_bad_byte_reg (Zmonop monop_name dsize rm) = has_bad_byte_regs dsize (byte_regs_in_rm rm)) /\
  (instr_accesses_bad_byte_reg (Zxadd dsize rm r) = has_bad_byte_regs dsize (r::byte_regs_in_rm rm)) /\
  (instr_accesses_bad_byte_reg (Zxchg dsize rm r) = has_bad_byte_regs dsize (r::byte_regs_in_rm rm)) /\
  (instr_accesses_bad_byte_reg (Zcmpxchg dsize rm r) = has_bad_byte_regs dsize (r::byte_regs_in_rm rm)) /\
  (instr_accesses_bad_byte_reg (Zpop rm) = F) /\
  (instr_accesses_bad_byte_reg (Zlea dsize ds) = has_bad_byte_regs dsize (byte_regs_in_ds ds)) /\
  (instr_accesses_bad_byte_reg (Zpush imm_rm) = F) /\
  (instr_accesses_bad_byte_reg (Zcall imm_rm) = F) /\
  (instr_accesses_bad_byte_reg (Zret imm) = F) /\
  (instr_accesses_bad_byte_reg (Zmov c dsize ds) = has_bad_byte_regs dsize (byte_regs_in_ds ds)) /\
  (instr_accesses_bad_byte_reg (Zjcc c imm) = F) /\
  (instr_accesses_bad_byte_reg (Zjmp rm) = F) /\
  (instr_accesses_bad_byte_reg (Zloop c imm) = F) /\
  (instr_accesses_bad_byte_reg (Zpushad) = F) /\
  (instr_accesses_bad_byte_reg (Zpopad) = F)`;

val Zprefixes_ok_def = Define `
  Zprefixes_ok pres i = ALL_DISTINCT (MAP Zprefix_group pres) /\
                        (MEM Zlock pres ==> x64_lock_ok i) /\
                        (MEM Zbranch_taken pres ==> x64_is_jcc i) /\
                        (MEM Zbranch_not_taken pres ==> x64_is_jcc i)`;

val x64_decode_def = Define `
  x64_decode w =
    let (pres,w) = x64_decode_prefixes w in
    let (g,w) = x64_decode_REX w in
    let g = (if MEM Zoperand_size_override pres then (("16BIT" =+ [T]) g) else g) in
    let result = x64_decode_aux g w in
      if result = NONE then NONE else
        let (i,w) = THE result in
          if (g "REX.W" = []) /\ instr_accesses_bad_byte_reg i then NONE else
          if (g "REX.W" = [T]) /\ (g "16BIT" = [T]) then NONE else
          if Zprefixes_ok pres i then SOME (Zfull_inst pres i, w) else NONE`;

val padbyte_def = Define `
  (padbyte [] = [F;F;F;F;F;F;F;F]) /\
  (padbyte [x0] = [x0;F;F;F;F;F;F;F]) /\
  (padbyte [x0;x1] = [x0;x1;F;F;F;F;F;F]) /\
  (padbyte [x0;x1;x2] = [x0;x1;x2;F;F;F;F;F]) /\
  (padbyte [x0;x1;x2;x3] = [x0;x1;x2;x3;F;F;F;F]) /\
  (padbyte [x0;x1;x2;x3;x4] = [x0;x1;x2;x3;x4;F;F;F]) /\
  (padbyte [x0;x1;x2;x3;x4;x5] = [x0;x1;x2;x3;x4;x5;F;F]) /\
  (padbyte [x0;x1;x2;x3;x4;x5;x6] = [x0;x1;x2;x3;x4;x5;x6;F]) /\
  (padbyte [x0;x1;x2;x3;x4;x5;x6;x7] = [x0;x1;x2;x3;x4;x5;x6;x7])`;

val word2byte_def = Define `
  word2byte (w:word8) = padbyte (MAP ($= 1) (word_to_bin_list w))`;

val x64_decode_bytes_def = Define `
  x64_decode_bytes b = x64_decode (FLAT (MAP word2byte b))`;


(* -- partially pre-evaluate x64_decode_aux -- *)

val Zreg_distinct = save_thm("Zreg_distinct",
  SIMP_RULE std_ss [GSYM CONJ_ASSOC,ALL_DISTINCT,MEM,REVERSE_DEF,APPEND]
    (CONJ ALL_DISTINCT_Zreg (ONCE_REWRITE_RULE [GSYM ALL_DISTINCT_REVERSE] ALL_DISTINCT_Zreg)));

val DTF_DTF = prove(
  ``(DTF p1 p2 ++ DTF q1 q2 = DTF (p1 ++ q1) (p2 ++ q2))``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,LET_DEF] THEN REPEAT STRIP_TAC
  THEN Cases_on `x` THEN Cases_on `r` THEN SIMP_TAC std_ss [DTF_def] THEN Cases_on `h`
  THEN SIMP_TAC std_ss [DTF_def,option_orelse_def,LET_DEF]);

val DTF_INTRO = prove(
  ``(DF >> f = DTF (\x.NONE) f) /\ (DT >> f = DTF f (\x.NONE))``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,LET_DEF] THEN REPEAT STRIP_TAC
  THEN Cases_on `x` THEN Cases_on `r` THEN SIMP_TAC std_ss [DTF_def,DF_def,DT_def]
  THEN Cases_on `h` THEN SIMP_TAC std_ss [DTF_def,option_orelse_def,LET_DEF,DF_def,DT_def]);

val ORELSE_NONE = prove(
  ``((\x.NONE) ++ f = f) /\ (f ++ (\x.NONE) = f) /\
    ((\x.NONE) >> f = (\x.NONE)) /\ (f >> (\x.NONE) = (\x.NONE))``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,option_then_def,LET_DEF] THEN METIS_TAC []);

val PUSH_assert_lemma = prove(
  ``(assert k >> (DTF p q >> t) = DTF (assert k >> p >> t) (assert k >> q >> t))``,
  SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases THEN Cases_on `r` THEN REPEAT (Cases_on `h`)
  THEN SIMP_TAC std_ss [assert_def,option_then_def,LET_DEF,DTF_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [] THEN REV_FULL_SIMP_TAC std_ss []);

val DTF_THEN = prove(
  ``DTF p q >> t = DTF (p >> t) (q >> t)``,
  SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases THEN Cases_on `r` THEN REPEAT (Cases_on `h`)
  THEN SIMP_TAC std_ss [assert_def,option_then_def,LET_DEF,DTF_def]);

val PUSH_assert = prove(
  ``(assert k >> (DF >> f) = DF >> (assert k >> f)) /\
    (assert k >> (DT >> f) = DT >> (assert k >> f)) /\
    (assert k >> (p ++ q) = (assert k >> p ++ assert k >> q)) /\
    (assert k >> DTF p q = DTF (assert k >> p) (assert k >> q))``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,option_orelse_def,LET_DEF,GSYM DTF_THM]
  THEN REPEAT STRIP_TAC THEN Cases_on `x` THEN Cases_on `r` THEN REPEAT (Cases_on `h`)
  THEN SIMP_TAC std_ss [assert_def,DF_def,DT_def] THEN
  BasicProvers.EVERY_CASE_TAC THEN REV_FULL_SIMP_TAC std_ss []);

val car = fst o dest_comb;
val cdr = snd o dest_comb;

val x64_decode_aux_thm = let
  fun eval_term_ss tm_name tm = conv_ss
    { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };
  val token_ss = eval_term_ss "tokenise" ``tokenise x``;
  val if_ss = conv_ss { name = "if", trace = 3,
    key = SOME ([],``if x then (y:'a) else z``),
    conv = K (K ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) };
  val hex_ss = eval_term_ss "hex" ``n2bits 8 (hex2num y)``;
  val hex_add_ss = eval_term_ss "hex" ``n2bits 8 ((hex2num y) + k)``;
  val n2bits_3_ss = eval_term_ss "n2bits_3" ``n2bits 3 y``;
  val select_op_ss = eval_term_ss "select_op" ``x64_select_op x (y:('a#'b)list)``;
  val EL_LEMMA = prove(
    ``!x y z t. (EL 0 (x::t) = x) /\ (EL 1 (x::y::t) = y) /\ (EL 2 (x:'a::y::z::t) = z)``,
    REPEAT STRIP_TAC THEN EVAL_TAC);
  val SOME_LEMMA = prove(``!(f :'a -> 'b option) (g :'c) (h :'d). (SOME >> f = f)``,
    SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,LET_DEF]);
  val DT_THEN = prove(
    ``((DT >> f) (g,T::w) = f (g,w)) /\ ((DF >> f) (g,F::w) = f (g,w))``,
    SIMP_TAC std_ss [option_then_def,DT_def,DF_def,LET_DEF]);
  val tm = ``x64_decode_aux g``
  val th1 = REWRITE_CONV [MAP,x64_decode_aux_def,combinTheory.o_DEF] tm
  val th2 = CONV_RULE (ONCE_DEPTH_CONV (BETA_CONV) THENC (RAND_CONV (RAND_CONV EVAL))) th1
  val th3 = REWRITE_RULE [match_list_raw_def,MAP] th2
  val th4 = SIMP_RULE (std_ss++token_ss) [match_def] th3
  val th5 = SIMP_RULE (bool_ss++if_ss) [MAP,x64_match_step_def] th4
  val th6 = SIMP_RULE (bool_ss++if_ss++select_op_ss) [x64_syntax_def,EL_LEMMA,HD] th5
  val th6a = SIMP_RULE (std_ss) [LET_DEF,process_hex_add_def] th6
  val th7 = SIMP_RULE (bool_ss++if_ss++hex_ss++hex_add_ss++n2bits_3_ss) [decode_Zdest_src_def,decode_Zconst_def] th6a
  val th8 = REWRITE_RULE [GSYM option_then_assoc,option_do_def,option_try_def,GSYM option_orelse_assoc] th7
  val th9 = SIMP_RULE std_ss [option_orelse_SOME,GSYM option_orelse_assoc,Z_SOME_def] th8
  val thA = REWRITE_RULE [GSYM option_then_assoc,EL_LEMMA,drop_eq_thm,SOME_LEMMA,option_do_def] th9
  val thB = thA |> REWRITE_RULE [assert_option_then_thm,option_then_assoc]
                |> REWRITE_RULE [assert_option_then_thm,GSYM option_then_assoc,SOME_LEMMA]
  val thC = REWRITE_RULE [option_try_def,GSYM option_orelse_assoc] thB
  val thD = REWRITE_RULE [option_then_OVER_orelse] thC
  val thE = REWRITE_RULE [option_orelse_assoc] thD
  val thX = REWRITE_RULE [DT_over_DF,option_then_assoc,option_orelse_assoc,option_then_OVER_orelse] thE
  val thZ = thX |> REWRITE_RULE [DTF_INTRO,DTF_DTF,DTF_THEN,ORELSE_NONE,PUSH_assert]
  (* find pre-evaulatable prefixes *)
  val DTF_tm = ``DTF p (q:'a # bool list -> 'b option)``
  fun dest_DTF tm = if can (match_term DTF_tm) tm then (cdr (car tm), cdr tm) else fail()
  val w_var = mk_var("w",``:bool list``)
  fun rec_dest_DTF tm = let
    val (x1,x2) = dest_DTF tm
    val xs1 = rec_dest_DTF x1
    val xs2 = rec_dest_DTF x2
    in (map (curry listSyntax.mk_cons T) xs1) @ (map (curry listSyntax.mk_cons F) xs2) end
    handle HOL_ERR _ => [w_var]
  val prefixes = thZ |> concl |> dest_eq |> snd |> cdr |> rec_dest_DTF
  (* evaluate the prefixes *)
  val LEMMA = prove(
    ``!g w. ((\w. SOME (g,w)) >> f) w = f (g,w)``,
    SIMP_TAC std_ss [LET_DEF,option_then_def]);
  val c = ONCE_REWRITE_CONV [thZ] THENC REWRITE_CONV [LEMMA,DTF_def]
  val decode_aux_tm = ``x64_decode_aux g``
  fun eval_for prefix = c (mk_comb(decode_aux_tm,prefix))
  val pre_evaluated_thm = LIST_CONJ (map eval_for prefixes)
  in pre_evaluated_thm end;

fun permanently_add_to_compset name thm = let
  val _ = Feedback.trace ("Theory.allow_rebinds", 1) save_thm(name,thm)
  val _ = computeLib.add_persistent_funs [name]
  in print ("Permanently added to compset: "^name^"\n") end;

val _ = permanently_add_to_compset "Zreg_distinct" Zreg_distinct;
val _ = permanently_add_to_compset "x64_decode_aux_thm" x64_decode_aux_thm;

(*
   EVAL ``x64_decode_bytes [0x48w; 0x01w; 0xD1w]``
*)


val _ = export_theory ();
