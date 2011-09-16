
open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib simpLib;
open decoderTheory bit_listTheory opmonTheory;

open x86_astTheory;

val _ = new_theory "x86_decoder";


(* ---------------------------------------------------------------------------------- *>

  A decoder for x86 instructions is defined and at the end pre-evaliuated for
  fast execution with EVAL.

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

val x86_match_step_def = Define `
  x86_match_step name =
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
      assign_drop name 32
    else if name = "/r" then                     (* normal reg + reg/mem *)
      read_ModRM
    else if MEM name ["/0";"/1";"/2";"/3";"/4";"/5";"/6";"/7"] then (* opcode extension in ModRM *)
      read_ModRM >> check_opcode name
    else
      option_fail`;

(* syntax classes *)

val x86_binop_def = Define `x86_binop =
  [("ADC",Xadc); ("ADD",Xadd); ("AND",Xand); ("CMP",Xcmp);
   ("OR",Xor); ("SAR",Xsar); ("SHR",Xshr); ("SHL",Xshl);
   ("SBB",Xsbb); ("SUB",Xsub); ("TEST",Xtest); ("XOR",Xxor)]`;

val x86_monop_def = Define `x86_monop =
  [("DEC",Xdec); ("INC",Xinc); ("NOT",Xnot); ("NEG",Xneg)]`;

(* x86 - decoder *)

val b2reg_def = Define `
  b2reg g name = (EL (bits2num (g name)) [EAX;ECX;EDX;EBX;ESP;EBP;ESI;EDI]):Xreg`;

val decode_Xr32_def = Define `
  decode_Xr32 g name =
    if name = "EAX" then EAX else
      if g "reg" = [] then b2reg g "Reg/Opcode" else b2reg g "reg"`;

val decode_SIB_def = Define `
  decode_SIB g =
    let scaled_index = (if g "Index" = [F;F;T] then NONE else SOME (b2w g "Scale",b2reg g "Index")) in
      if g "Base" = [T;F;T] then (* the special case indicated by "[*]" *)
        if g "Mod" = [F;F] then Xm scaled_index NONE (b2w g "disp32") else
        if g "Mod" = [T;F] then Xm scaled_index (SOME EBP) (b2w g "disp8") else
        (* g "Mod" = [F;T] *)   Xm scaled_index (SOME EBP) (b2w g "disp32")
      else (* normal cases, just need to read off the correct displacement *)
        let disp = (if (g "Mod" = [T;F]) then sw2sw ((b2w g "disp8"):word8) else b2w g "disp32") in
        let disp = (if (g "Mod" = [F;F]) then 0w else disp) in
          Xm scaled_index (SOME (b2reg g "Base")) disp`;

val decode_Xrm32_def = Define `  (* sw2sw = sign-extension *)
  decode_Xrm32 g name =
    if name = "EAX" then Xr EAX else
      if  (g "Mod" = [F;F]) /\ (g "R/M" = [T;F;T]) then Xm NONE NONE (b2w g "disp32") else
      if ~(g "Mod" = [T;T]) /\ (g "R/M" = [F;F;T]) then decode_SIB g else
      if  (g "Mod" = [F;F]) then Xm NONE (SOME (b2reg g "R/M")) 0w else
      if  (g "Mod" = [T;F]) then Xm NONE (SOME (b2reg g "R/M")) (sw2sw:word8->word32 (b2w g "disp8")) else
      if  (g "Mod" = [F;T]) then Xm NONE (SOME (b2reg g "R/M")) (b2w g "disp32") else
      if  (g "Mod" = [T;T]) then Xr (b2reg g "R/M") else Xr (b2reg g "reg") `;

val decode_Xconst_def = Define `
  decode_Xconst name g =
   if name = "imm8"  then sw2sw:word8 ->word32 (b2w g "ib") else
   if name = "rel8"  then sw2sw:word8 ->word32 (b2w g "cb") else
   if name = "imm16" then sw2sw:word16->word32 (b2w g "iw") else
   if name = "imm32" then b2w g "id" else
   if name = "rel32" then b2w g "cd" else
   if name = "1"     then 1w else 0w`;

val decode_Xdest_src_def = Define `
  decode_Xdest_src g dest src =
    if MEM src ["r32";"r8"] then
      Xrm_r (decode_Xrm32 g dest) (decode_Xr32 g src)
    else if MEM src ["r/m32";"r/m8"] then
      Xr_rm (decode_Xr32 g dest)  (decode_Xrm32 g src)
    else if src = "m" then
      Xr_rm (decode_Xr32 g dest)  (decode_Xrm32 g src)
    else
      Xrm_i (decode_Xrm32 g dest) (decode_Xconst src g)`;

val decode_Xconst_or_zero_def = Define `
  decode_Xconst_or_zero ts g =
    if LENGTH ts < 2 then 0w else decode_Xconst (EL 1 ts) g`;

val decode_Ximm_rm_def = Define `
  decode_Ximm_rm ts g =
    if MEM (EL 1 ts) ["r/m32";"r32";"r/m8";"r8"]
    then Xi_rm (decode_Xrm32 g (EL 1 ts))
    else Xi (decode_Xconst (EL 1 ts) g)`;

val x86_select_op_def = Define `
  x86_select_op name list = SND (HD (FILTER (\x. FST x = name) list))`;

val x86_syntax_binop = ``
  Xbinop (x86_select_op (HD ts) x86_binop) (decode_Xdest_src g (EL 1 ts) (EL 2 ts))``;

val x86_syntax_monop = ``
  Xmonop (x86_select_op (HD ts) x86_monop) (decode_Xrm32 g (EL 1 ts))``;

val X_SOME_def = Define `X_SOME f = SOME o (\(g,w). (f g,w))`;

val x86_syntax_def = Define `
  x86_syntax ts =
    if LENGTH ts = 0 then option_fail else
    if (HD ts = "CMP") /\ MEM "r/m8" ts then X_SOME (\g. Xcmp_byte (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if (HD ts = "MOV") /\ MEM "r/m8" ts then X_SOME (\g. Xmov_byte (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if (HD ts = "DEC") /\ MEM "r/m8" ts then X_SOME (\g. Xdec_byte (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "MOVZX" then X_SOME (\g. Xmovzx (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if MEM (HD ts) (MAP FST x86_binop) then X_SOME (\g. ^x86_syntax_binop) else
    if MEM (HD ts) (MAP FST x86_monop) then X_SOME (\g. ^x86_syntax_monop) else
    if HD ts = "POP"  then X_SOME (\g. Xpop  (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "PUSH" then X_SOME (\g. Xpush (decode_Ximm_rm ts g)) else
    if HD ts = "PUSHAD"  then X_SOME (\g. Xpushad) else
    if HD ts = "POPAD"   then X_SOME (\g. Xpopad)  else
    if HD ts = "CMPXCHG" then X_SOME (\g. Xcmpxchg (decode_Xrm32 g (EL 1 ts)) (decode_Xr32 g (EL 2 ts))) else
    if HD ts = "XCHG"    then X_SOME (\g. Xxchg (decode_Xrm32 g (EL 1 ts)) (decode_Xr32 g (EL 2 ts))) else
    if HD ts = "XADD"    then X_SOME (\g. Xxadd (decode_Xrm32 g (EL 1 ts)) (decode_Xr32 g (EL 2 ts))) else
    if (HD ts = "JMP") /\ (TL ts = ["r/m32"]) then X_SOME (\g. Xjmp (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "JMP"     then X_SOME (\g. Xjcc X_ALWAYS (decode_Xconst_or_zero ts g)) else
    if HD ts = "JE"      then X_SOME (\g. Xjcc X_E (decode_Xconst_or_zero ts g)) else
    if HD ts = "JNE"     then X_SOME (\g. Xjcc X_NE (decode_Xconst_or_zero ts g)) else
    if HD ts = "JS"      then X_SOME (\g. Xjcc X_S (decode_Xconst_or_zero ts g)) else
    if HD ts = "JNS"     then X_SOME (\g. Xjcc X_NS (decode_Xconst_or_zero ts g)) else
    if HD ts = "JA"      then X_SOME (\g. Xjcc X_A (decode_Xconst_or_zero ts g)) else
    if HD ts = "JNA"     then X_SOME (\g. Xjcc X_NA (decode_Xconst_or_zero ts g)) else
    if HD ts = "JB"      then X_SOME (\g. Xjcc X_B (decode_Xconst_or_zero ts g)) else
    if HD ts = "JNB"     then X_SOME (\g. Xjcc X_NB (decode_Xconst_or_zero ts g)) else
    if HD ts = "LEA"     then X_SOME (\g. Xlea (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "LOOP"    then X_SOME (\g. Xloop X_ALWAYS (decode_Xconst_or_zero ts g)) else
    if HD ts = "LOOPE"   then X_SOME (\g. Xloop X_E (decode_Xconst_or_zero ts g)) else
    if HD ts = "LOOPNE"  then X_SOME (\g. Xloop X_NE (decode_Xconst_or_zero ts g)) else
    if HD ts = "MOV"     then X_SOME (\g. Xmov X_ALWAYS (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVE"   then X_SOME (\g. Xmov X_E (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNE"  then X_SOME (\g. Xmov X_NE (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVS"   then X_SOME (\g. Xmov X_S (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNS"  then X_SOME (\g. Xmov X_NS (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVA"   then X_SOME (\g. Xmov X_A (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNA"  then X_SOME (\g. Xmov X_NA (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVB"   then X_SOME (\g. Xmov X_B (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNB"  then X_SOME (\g. Xmov X_NB (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "MUL"     then X_SOME (\g. Xmul  (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "DIV"     then X_SOME (\g. Xdiv  (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "CALL"    then X_SOME (\g. Xcall (decode_Ximm_rm ts g)) else
    if HD ts = "RET"     then X_SOME (\g. Xret (decode_Xconst_or_zero ts g)) else option_fail`;


(* a list of x86 instructions, ordered by the combination of addressing modes they support *)

val x86_syntax_list = `` [

    " 15 id     | ADC EAX, imm32    ";
    " 83 /2 ib  | ADC r/m32, imm8   ";
    " 81 /2 id  | ADC r/m32, imm32  ";
    " 11 /r     | ADC r/m32, r32    ";
    " 13 /r     | ADC r32, r/m32    ";
    " 05 id     | ADD EAX, imm32    ";
    " 83 /0 ib  | ADD r/m32, imm8   ";
    " 81 /0 id  | ADD r/m32, imm32  ";
    " 01 /r     | ADD r/m32, r32    ";
    " 03 /r     | ADD r32, r/m32    ";
    " 25 id     | AND EAX, imm32    ";
    " 81 /4 id  | AND r/m32, imm32  ";
    " 83 /4 ib  | AND r/m32, imm8   ";
    " 21 /r     | AND r/m32, r32    ";
    " 23 /r     | AND r32, r/m32    ";
    " 3D id     | CMP EAX, imm32    ";
    " 81 /7 id  | CMP r/m32, imm32  ";
    " 83 /7 ib  | CMP r/m32, imm8   ";
    " 39 /r     | CMP r/m32, r32    ";
    " 3B /r     | CMP r32, r/m32    ";
    " 89 /r     | MOV r/m32,r32     ";
    " 8B /r     | MOV r32,r/m32     ";
    " B8+rd id  | MOV r32, imm32    ";
    " C7 /0 id  | MOV r/m32, imm32  ";
    " 0D id     | OR EAX, imm32     ";
    " 81 /1 id  | OR r/m32, imm32   ";
    " 83 /1 ib  | OR r/m32, imm8    ";
    " 09 /r     | OR r/m32, r32     ";
    " 0B /r     | OR r32, r/m32     ";
    " 1D id     | SBB EAX, imm32    ";
    " 83 /3 ib  | SBB r/m32, imm8   ";
    " 81 /3 id  | SBB r/m32, imm32  ";
    " 19 /r     | SBB r/m32, r32    ";
    " 1B /r     | SBB r32, r/m32    ";
    " 2D id     | SUB EAX, imm32    ";
    " 83 /5 ib  | SUB r/m32, imm8   ";
    " 81 /5 id  | SUB r/m32, imm32  ";
    " 29 /r     | SUB r/m32, r32    ";
    " 2B /r     | SUB r32, r/m32    ";
    " A9 id     | TEST EAX, imm32   ";
    " F7 /0 id  | TEST r/m32, imm32 ";
    " 85 /r     | TEST r/m32, r32   ";
    " 35 id     | XOR EAX, imm32    ";
    " 81 /6 id  | XOR r/m32, imm32  ";
    " 31 /r     | XOR r/m32, r32    ";
    " 83 /6 ib  | XOR r/m32, imm8   ";
    " 33 /r     | XOR r32, r/m32    ";

    " 0F B1 /r  | CMPXCHG r/m32, r32";
    " 0F C1 /r  | XADD r/m32, r32   ";
    " 90+rd     | XCHG EAX, r32     ";
    " 87 /r     | XCHG r/m32, r32   ";

    " FF /1     | DEC r/m32         ";
    " 48+rd     | DEC r32           ";
    " FF /0     | INC r/m32         ";
    " 40+rd     | INC r32           ";
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

    " C3        | RET               "; (* short for "RET 0" *)
    " C2 iw     | RET imm16         ";
    " E2 cb     | LOOP rel8         ";
    " E1 cb     | LOOPE rel8        ";
    " E0 cb     | LOOPNE rel8       ";

    " 60        | PUSHAD            ";
    " 61        | POPAD             ";

    " F7 /6     | DIV r/m32         ";
    " F7 /4     | MUL r/m32         ";

    " C6 /0 ib  | MOV r/m8, imm8    ";
    " 88 /r     | MOV r/m8, r8      ";
    " 0F B6 /r  | MOVZX r32, r/m8   ";
    " 38 /r     | CMP r/m8, r8      ";
    " 3A /r     | CMP r8, r/m8      ";
    " 80 /7 ib  | CMP r/m8, imm8    ";
    " FE /1     | DEC r/m8          "

  ] ``;

val x86_decode_aux_def = Define `
  x86_decode_aux = (match_list x86_match_step tokenise (x86_syntax o tokenise) o
                     MAP (\s. let x = STR_SPLIT [#"|"] s in (EL 0 x, EL 1 x))) ^x86_syntax_list`;

val x86_decode_prefixes_def = Define `
  x86_decode_prefixes w =
    if LENGTH w < 16 then (Xg1_none,Xg2_none,w) else
      let bt1  = (TAKE 8 w = n2bits 8 (hex2num "2E")) in
      let bnt1 = (TAKE 8 w = n2bits 8 (hex2num "3E")) in
      let l1   = (TAKE 8 w = n2bits 8 (hex2num "F0")) in
      let bt2  = (TAKE 8 (DROP 8 w) = n2bits 8 (hex2num "2E")) /\ l1 in
      let bnt2 = (TAKE 8 (DROP 8 w) = n2bits 8 (hex2num "3E")) /\ l1 in
      let l2   = (TAKE 8 (DROP 8 w) = n2bits 8 (hex2num "F0")) /\ (bt1 \/ bnt1) in
      let g1   = if l1 \/ l2 then Xlock else Xg1_none in
      let g2   = if bt1 \/ bt2 then Xbranch_taken else Xg2_none in
      let g2   = if bnt1 \/ bnt2 then Xbranch_not_taken else g2 in
      let n    = if bt1 \/ bnt1 \/ l1 then (if bt2 \/ bnt2 \/ l2 then 16 else 8) else 0 in
        (g1,g2,DROP n w)`;

val dest_accesses_memory_def = Define `
  (dest_accesses_memory (Xrm_i rm i) = rm_is_memory_access rm) /\
  (dest_accesses_memory (Xrm_r rm r) = rm_is_memory_access rm) /\
  (dest_accesses_memory (Xr_rm r rm) = F)`;

val x86_lock_ok_def = Define `
  (x86_lock_ok (Xbinop binop_name ds) =
    MEM binop_name [Xadd;Xand;Xor;Xsub;Xxor] /\
    dest_accesses_memory ds) /\
  (x86_lock_ok (Xmonop monop_name rm) =
    MEM monop_name [Xdec;Xinc;Xneg;Xnot] /\
    rm_is_memory_access rm) /\
  (x86_lock_ok (Xxadd rm r) = rm_is_memory_access rm) /\
  (x86_lock_ok (Xxchg rm r) = rm_is_memory_access rm) /\
  (x86_lock_ok (Xcmpxchg rm r) = rm_is_memory_access rm) /\
  (x86_lock_ok (Xpop rm) = F) /\
  (x86_lock_ok (Xlea ds) = F) /\
  (x86_lock_ok (Xpush imm_rm) = F) /\
  (x86_lock_ok (Xcall imm_rm) = F) /\
  (x86_lock_ok (Xret imm) = F) /\
  (x86_lock_ok (Xmov c ds) = F) /\
  (x86_lock_ok (Xjcc c imm) = F) /\
  (x86_lock_ok (Xjmp rm) = F) /\
  (x86_lock_ok (Xloop c imm) = F) /\
  (x86_lock_ok (Xpushad) = F) /\
  (x86_lock_ok (Xpopad) = F)`;

val x86_decode_def = Define `
  x86_decode w =
    let (g1,g2,w) = x86_decode_prefixes w in
    let result = x86_decode_aux w in
      if result = NONE then NONE else
        let (i,w) = THE result in
          if ~(g1 = Xlock) \/ x86_lock_ok i then SOME (Xprefix g1 g2 i, w) else NONE`;

val x86_decode_bytes_def = Define `
  x86_decode_bytes b = x86_decode (FOLDR APPEND [] (MAP w2bits b))`;

val rm_args_ok_def = Define `
  (rm_args_ok (Xr r) = T) /\
  (rm_args_ok (Xm NONE NONE t3) = T) /\
  (rm_args_ok (Xm NONE (SOME br) t3) = T) /\
  (rm_args_ok (Xm (SOME (s,ir)) NONE t3) = ~(ir = ESP)) /\
  (rm_args_ok (Xm (SOME (s,ir)) (SOME br) t3) = ~(ir = ESP))`;

val dest_src_args_ok_def = Define `
  (dest_src_args_ok (Xrm_i rm i) = rm_args_ok rm) /\
  (dest_src_args_ok (Xrm_r rm r) = rm_args_ok rm ) /\
  (dest_src_args_ok (Xr_rm r rm) = rm_args_ok rm )`;

val imm_rm_args_ok_def = Define `
  (imm_rm_args_ok (Xi_rm rm) = rm_args_ok rm) /\
  (imm_rm_args_ok (Xi i) = T)`;

val x86_args_ok_def = Define `
  (x86_args_ok (Xbinop binop_name ds) = dest_src_args_ok ds) /\
  (x86_args_ok (Xmonop monop_name rm) = rm_args_ok rm) /\
  (x86_args_ok (Xxadd rm r) = rm_args_ok rm ) /\
  (x86_args_ok (Xxchg rm r) = rm_args_ok rm ) /\
  (x86_args_ok (Xcmpxchg rm r) = rm_args_ok rm ) /\
  (x86_args_ok (Xpop rm) = rm_args_ok rm) /\
  (x86_args_ok (Xpush imm_rm) = imm_rm_args_ok imm_rm) /\
  (x86_args_ok (Xcall imm_rm) = imm_rm_args_ok imm_rm) /\
  (x86_args_ok (Xret imm) = w2n imm < 2**16) /\
  (x86_args_ok (Xmov c ds) = dest_src_args_ok ds /\ MEM c [X_NE;X_E;X_ALWAYS]) /\ (* partial list *)
  (x86_args_ok (Xjcc c imm) = T) /\
  (x86_args_ok (Xjmp rm) = T) /\
  (x86_args_ok (Xloop c imm) = MEM c [X_NE;X_E;X_ALWAYS]) /\
  (x86_args_ok (Xpushad) = T) /\
  (x86_args_ok (Xpopad) = T)`;

val x86_well_formed_instruction_def = Define `
  (x86_well_formed_instruction (Xprefix Xlock g2 i) = x86_lock_ok i /\ x86_args_ok i) /\
  (x86_well_formed_instruction (Xprefix Xg1_none g2 i) = x86_args_ok i)`;



(* -- partially pre-evaluate x86_decode_aux -- *)

val x86_decode_aux_thm = let
  fun eval_term_ss tm_name tm = conv_ss
    { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };
  val token_ss = eval_term_ss "tokenise" ``tokenise x``;
  val if_ss = conv_ss { name = "if", trace = 3,
    key = SOME ([],``if x then (y:'a) else z``),
    conv = K (K ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) };
  val hex_ss = eval_term_ss "hex" ``n2bits 8 (hex2num y)``;
  val hex_add_ss = eval_term_ss "hex" ``n2bits 8 ((hex2num y) + k)``;
  val n2bits_3_ss = eval_term_ss "n2bits_3" ``n2bits 3 y``;
  val select_op_ss = eval_term_ss "select_op" ``x86_select_op x (y:('a#'b)list)``;
  val EL_LEMMA = prove(
    ``!x y z t. (EL 0 (x::t) = x) /\ (EL 1 (x::y::t) = y) /\ (EL 2 (x:'a::y::z::t) = z)``,
    REPEAT STRIP_TAC THEN EVAL_TAC);
  val SOME_LEMMA = prove(``!(f :'a -> 'b option) (g :'c) (h :'d). (SOME >> f = f)``,
    SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,LET_DEF]);
  val th1 = REWRITE_CONV [MAP,x86_decode_aux_def,combinTheory.o_DEF] ``x86_decode_aux``
  val th2 = CONV_RULE (ONCE_DEPTH_CONV (BETA_CONV) THENC (RAND_CONV (RAND_CONV EVAL))) th1
  val th3 = REWRITE_RULE [match_list_def,MAP] th2
  val th4 = SIMP_RULE (std_ss++token_ss) [match_def] th3
  val th5 = SIMP_RULE (bool_ss++if_ss) [MAP,x86_match_step_def] th4
  val th6 = SIMP_RULE (bool_ss++if_ss++select_op_ss) [x86_syntax_def,EL_LEMMA,HD] th5
  val th6a = SIMP_RULE (std_ss) [LET_DEF,process_hex_add_def] th6
  val th7 = SIMP_RULE (bool_ss++if_ss++hex_ss++hex_add_ss++n2bits_3_ss) [decode_Xdest_src_def,decode_Xconst_def] th6a
  val th8 = REWRITE_RULE [GSYM option_then_assoc,option_do_def,option_try_def,GSYM option_orelse_assoc] th7
  val th9 = SIMP_RULE std_ss [option_orelse_SOME,GSYM option_orelse_assoc,X_SOME_def] th8
  val thA = REWRITE_RULE [GSYM option_then_assoc,EL_LEMMA,drop_eq_thm,SOME_LEMMA,option_do_def] th9
  val thB = REWRITE_RULE [option_then_assoc,SOME_LEMMA] thA
  val thC = REWRITE_RULE [option_try_def,GSYM option_orelse_assoc] thB
  val thD = REWRITE_RULE [option_then_OVER_orelse] thC
  val thE = REWRITE_RULE [option_orelse_assoc] thD
  val thX = REWRITE_RULE [DT_over_DF,option_then_assoc,option_orelse_assoc,option_then_OVER_orelse] thE
  val thZ = REWRITE_RULE [DTF_THM] thX
  in thZ end;

fun permanently_add_to_compset name thm = let
  val _ = save_thm(name,thm)
  val _ = computeLib.add_funs [thm]
  val _ = adjoin_to_theory {sig_ps = NONE, struct_ps = SOME (fn ppstrm =>
    let val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) in
            S ("val _ = computeLib.add_funs ["^name^"];")
    end)}
  in print ("Permanently added to compset: "^name^"\n") end;

val _ = permanently_add_to_compset "x86_decode_aux_thm" x86_decode_aux_thm;


(* x86 examples/tests:

val _ = wordsLib.output_words_as_hex();

val th = EVAL ``x86_decode(bytebits "8D84B6EE711202")``;  (* lea eax, [esi + 4*esi + 34763246] *)
val th = EVAL ``x86_decode(bytebits "D1E1")``;            (* shl ecx, 1 *)
val th = EVAL ``x86_decode(bytebits "C1E108")``;          (* shl ecx, 8 *)
val th = EVAL ``x86_decode(bytebits "D1EB")``;            (* shr ebx, 1 *)
val th = EVAL ``x86_decode(bytebits "C1EB08")``;          (* shr ebx, 8 *)
val th = EVAL ``x86_decode(bytebits "D1F8")``;            (* sar eax, 1 *)
val th = EVAL ``x86_decode(bytebits "C1F808")``;          (* sar eax, 8 *)
val th = EVAL ``x86_decode(bytebits "0538000000")``;      (* add eax,56 *)
val th = EVAL ``x86_decode(bytebits "810037020000")``;    (* add dword [eax],567 *)
val th = EVAL ``x86_decode(bytebits "010B")``;            (* add [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "0119")``;            (* add [ecx], ebx *)
val th = EVAL ``x86_decode(bytebits "2538000000")``;      (* and eax,56 *)
val th = EVAL ``x86_decode(bytebits "812037020000")``;    (* and dword [eax],567 *)
val th = EVAL ``x86_decode(bytebits "210B")``;            (* and [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "2319")``;            (* and ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "0F44C1")``;          (* cmove eax, ecx *)
val th = EVAL ``x86_decode(bytebits "0F454104")``;        (* cmovne eax, [ecx+4] *)
val th = EVAL ``x86_decode(bytebits "81FE38000000")``;    (* cmp esi,56 *)
val th = EVAL ``x86_decode(bytebits "813B37020000")``;    (* cmp dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "390B")``;            (* cmp [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "3B19")``;            (* cmp ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "893E")``;            (* mov [esi],edi *)
val th = EVAL ``x86_decode(bytebits "8B3E")``;            (* mov edi,[esi] *)
val th = EVAL ``x86_decode(bytebits "BC37020000")``;      (* mov esp,567 *)
val th = EVAL ``x86_decode(bytebits "81CE38000000")``;    (* or  esi,56 *)
val th = EVAL ``x86_decode(bytebits "810B37020000")``;    (* or  dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "090B")``;            (* or  [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "0B19")``;            (* or  ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "81EE38000000")``;    (* sub esi,56 *)
val th = EVAL ``x86_decode(bytebits "812B37020000")``;    (* sub dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "290B")``;            (* sub [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "2B19")``;            (* sub ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "F7C638000000")``;    (* test esi,56 *)
val th = EVAL ``x86_decode(bytebits "F70337020000")``;    (* test dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "850B")``;            (* test [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "81F638000000")``;    (* xor esi,56 *)
val th = EVAL ``x86_decode(bytebits "813337020000")``;    (* xor dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "310B")``;            (* xor [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "3319")``;            (* xor ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "0FB110")``;          (* cmpxchg [eax],edx *)
val th = EVAL ``x86_decode(bytebits "0FC11E")``;          (* xadd [esi],ebx *)
val th = EVAL ``x86_decode(bytebits "FF4E3C")``;          (* dec dword [esi+60] *)
val th = EVAL ``x86_decode(bytebits "4C")``;              (* dec esp *)
val th = EVAL ``x86_decode(bytebits "FF80401F0000")``;    (* inc dword [eax+8000] *)
val th = EVAL ``x86_decode(bytebits "40")``;              (* inc eax *)
val th = EVAL ``x86_decode(bytebits "F750C8")``;          (* not dword [eax-56] *)
val th = EVAL ``x86_decode(bytebits "8F0590010000")``;    (* pop dword [400] *)
val th = EVAL ``x86_decode(bytebits "59")``;              (* pop ecx *)
val th = EVAL ``x86_decode(bytebits "FFB498C8010000")``;  (* push dword [eax + 4*ebx + 456] *)
val th = EVAL ``x86_decode(bytebits "FF749801")``;        (* push dword [eax + 4*ebx + 1] *)
val th = EVAL ``x86_decode(bytebits "FF74AD02")``;        (* push dword [ebp + 4*ebp + 2] *)
val th = EVAL ``x86_decode(bytebits "FF746D2D")``;        (* push dword [ebp + 2*ebp + 45] *)
val th = EVAL ``x86_decode(bytebits "FFB42DEA000000")``;  (* push dword [ebp + ebp + 234] *)
val th = EVAL ``x86_decode(bytebits "FFB4B6EE711202")``;  (* push dword [esi + 4*esi + 34763246] *)
val th = EVAL ``x86_decode(bytebits "50")``;              (* push eax *)
val th = EVAL ``x86_decode(bytebits "E8BDFFFFFF")``;      (* call l1 *)
val th = EVAL ``x86_decode(bytebits "FFD0")``;            (* call eax *)
val th = EVAL ``x86_decode(bytebits "EBB9")``;            (* jmp l1 *)
val th = EVAL ``x86_decode(bytebits "74B7")``;            (* je l1 *)
val th = EVAL ``x86_decode(bytebits "75B5")``;            (* jne l1 *)
val th = EVAL ``x86_decode(bytebits "C3")``;              (* ret *)
val th = EVAL ``x86_decode(bytebits "C20500")``;          (* ret 5 *)
val th = EVAL ``x86_decode(bytebits "E2AF")``;            (* loop l1 *)
val th = EVAL ``x86_decode(bytebits "E1AD")``;            (* loope l1 *)
val th = EVAL ``x86_decode(bytebits "E0AB")``;            (* loopne l1 *)
val th = EVAL ``x86_decode(bytebits "60")``;              (* pushad *)
val th = EVAL ``x86_decode(bytebits "61")``;              (* popad *)
val th = EVAL ``x86_decode(bytebits "0FAEF0")``;          (* mfence *)
val th = EVAL ``x86_decode(bytebits "0FAEF8")``;          (* sfence *)
val th = EVAL ``x86_decode(bytebits "0FAEE8")``;          (* lfence *)
val th = EVAL ``x86_decode(bytebits "93")``;              (* xchg eax, ebx *)
val th = EVAL ``x86_decode(bytebits "8731")``;            (* xchg [ecx], esi *)
val th = EVAL ``x86_decode(bytebits "F7583C")``;          (* neg dword [eax+60] *)
val th = EVAL ``x86_decode(bytebits "8325C49B040800")``;  (* and [8049BC4], 0 *)
val th = EVAL ``x86_decode(bytebits "8125C49B040800000000")``;  (* and [8049BC4], 0 *)
val th = EVAL ``x86_decode(bytebits "0FB1F8")``;          (* cmpxchg eax, edi *)
val th = EVAL ``x86_decode(bytebits "0FB1441500")``;      (* cmpxchg [ebp + edx], eax *)
val th = EVAL ``x86_decode(bytebits "56")``;
val th = EVAL ``x86_decode(bytebits "5B")``;

*)


val _ = export_theory ();
