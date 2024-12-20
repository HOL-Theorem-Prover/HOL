open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_inv";
val _ = ParseExtras.temp_loose_equality()


open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory;

open lisp_sexpTheory lisp_consTheory stop_and_copyTheory lisp_bytecodeTheory;


val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (sg q)
val wstd_ss = std_ss ++ SIZES_ss ++ rewrites [DECIDE ``n<256 ==> (n:num)<18446744073709551616``,stringTheory.ORD_BOUND];


(* I/O definition *)

val _ = Hol_datatype `
  io_streams = IO_STREAMS of string (* input *) => string (* output *)`;

val io_streams_11 = fetch "-" "io_streams_11"

(* symbol table definition *)

val one_byte_list_def = Define `
  (one_byte_list a [] = emp) /\
  (one_byte_list a (x::xs) = one (a:word64,x:word8) * one_byte_list (a + 1w) xs)`;

val one_byte_list_APPEND = store_thm("one_byte_list_APPEND",
  ``!a xs ys.
      one_byte_list a (xs++ys) = one_byte_list a xs * one_byte_list (a + n2w (LENGTH xs)) ys``,
  Induct_on `xs` \\ ASM_SIMP_TAC std_ss [one_byte_list_def,APPEND,SEP_CLAUSES,
    LENGTH,WORD_ADD_0,word_arith_lemma1,ADD1,AC ADD_COMM ADD_ASSOC]
  \\ SIMP_TAC (std_ss++star_ss) []);

val string_data_def = Define `
  string_data str = n2w (LENGTH str + 1) :: MAP ((n2w:num->word8) o ORD) str`;

val symbol_list_def = Define `
  (symbol_list [] = [0w]) /\
  (symbol_list (str::xs) = string_data str ++ symbol_list xs)`;

val one_symbol_list_def = Define `
  one_symbol_list a xs k =
    SEP_EXISTS ys.
      one_byte_list a (symbol_list xs ++ ys) *
      cond (EVERY (\x. LENGTH x < 255) xs /\ (LENGTH (symbol_list xs ++ ys) = k) /\
            ALL_DISTINCT xs /\ 520 <= LENGTH ys /\
            LENGTH xs < 536870912)`;

val symtable_inv_def = Define `
  symtable_inv (sa1:word64,sa2:word64,sa3:word64,dg,g) xs =
    (one_symbol_list sa1 xs (w2n sa3 - w2n sa1)) (fun2set (g,dg)) /\
    (sa2 = sa1 + n2w (LENGTH (symbol_list xs)))`;


(* top-level stack declaration *)

val ref_stack_space_above_def = Define `
  (ref_stack_space_above sp 0 = emp) /\
  (ref_stack_space_above sp (SUC n) =
     ref_stack_space_above (sp + 4w) n * SEP_EXISTS w. one (sp + 4w:word64,w:word32))`;

val ref_full_stack_def = Define `
  ref_full_stack sp wsp xs xs_rest ys n_rest =
    ref_stack (sp + 4w * wsp) (xs ++ xs_rest) *
    ref_stack_space (sp + 4w * wsp) (w2n wsp + 6) *
    ref_static (sp - 256w) ys *
    ref_stack_space_above (sp + 4w * wsp + n2w (4 * LENGTH (xs ++ xs_rest))) n_rest`;

(* definition of code heap *)

val IMMEDIATE32_def = Define `
  IMMEDIATE32 (w:word32) =
    [w2w w; w2w (w >>> 8); w2w (w >>> 16); w2w (w >>> 24)]:word8 list`;

val bc_ref_def = Define `
  (bc_ref (i,sym) iPOP =
    [0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw; 0xC3w]) /\
  (bc_ref (i,sym) (iCONST_NUM n) =
    [0x48w; 0x85w; 0xDBw; 0x3Ew; 0x48w; 0x75w; 0x9w; 0x8Bw; 0xD1w; 0x48w;
     0xFFw; 0xA7w; 0x38w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xCBw; 0x44w;
     0x89w; 0x4w; 0x9Fw; 0x41w; 0xB8w] ++
    IMMEDIATE32 (n2w (4 * n + 1))) /\
  (bc_ref (i,sym) (iCONST_SYM s) =
    [0x48w; 0x85w; 0xDBw; 0x3Ew; 0x48w; 0x75w; 0x9w; 0x8Bw; 0xD1w; 0x48w;
     0xFFw; 0xA7w; 0x38w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xCBw; 0x44w;
     0x89w; 0x4w; 0x9Fw; 0x41w; 0xB8w] ++
    IMMEDIATE32 (n2w (8 * THE (LIST_FIND 0 s sym) + 3))) /\
   (bc_ref (i,sym) iRETURN =
     [0x48w; 0xC3w]) /\
   (bc_ref (i,sym) (iPOPS n) =
     [0x48w; 0x81w; 0xC3w] ++ IMMEDIATE32 (n2w n)) /\
   (bc_ref (i,sym) (iLOAD pos) =
     [0x48w; 0x85w; 0xDBw; 0x3Ew; 0x48w; 0x75w; 0x9w; 0x8Bw; 0xD1w; 0x48w;
      0xFFw; 0xA7w; 0x38w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xCBw; 0x44w;
      0x89w; 0x4w; 0x9Fw; 0x44w; 0x8Bw; 0x84w; 0x9Fw] ++ IMMEDIATE32 (n2w (4 * pos))) /\
   (bc_ref (i,sym) (iSTORE pos) =
     [0x44w; 0x89w; 0x84w; 0x9Fw] ++ IMMEDIATE32 (n2w (4 * pos)) ++
     [0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw; 0xC3w]) /\
   (bc_ref (i,sym) iCOMPILE =
     [0x48w; 0x8Bw; 0x57w; 0x88w; 0x48w; 0xFFw; 0xD2w]) /\
   (bc_ref (i,sym) iFAIL =
     [0xBAw; 0x4w; 0x0w; 0x0w; 0x0w; 0x48w; 0xFFw; 0xA7w; 0x38w; 0xFFw;
      0xFFw; 0xFFw]) /\
   (bc_ref (i,sym) iPRINT =
     [0x48w; 0x8Bw; 0x97w; 0x78w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw;
      0xD2w; 0x48w; 0x8Bw; 0x8Fw; 0x40w; 0xFFw; 0xFFw; 0xFFw; 0x48w;
      0x8Bw; 0x87w; 0x28w; 0xFFw; 0xFFw; 0xFFw; 0xC6w; 0x0w; 0xAw;
      0xC6w; 0x40w; 0x1w; 0x0w; 0x48w; 0xFFw; 0xD1w; 0xB8w; 0x3w;
      0x0w; 0x0w; 0x0w; 0xB9w; 0x1w; 0x0w; 0x0w; 0x0w]) /\
   (bc_ref (i,sym) (iJUMP pos) =
     [0x48w; 0xE9w] ++ IMMEDIATE32 (n2w pos - n2w i - 6w)) /\
   (bc_ref (i,sym) (iCALL pos) =
     [0x48w; 0xE8w] ++ IMMEDIATE32 (n2w pos - n2w i - 6w)) /\
   (bc_ref (i,sym) (iJNIL pos) =
     [0x4Dw; 0x8Bw; 0xC8w; 0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw; 0xC3w;
      0x49w; 0x83w; 0xF9w; 0x3w; 0x48w; 0x0Fw; 0x84w] ++ IMMEDIATE32 (n2w pos - n2w i - 21w)) /\
   (bc_ref (i,sym) (iDATA opCAR) =
     [0x49w; 0xF7w; 0xC0w; 0x1w; 0x0w; 0x0w; 0x0w; 0x4Cw; 0xFw; 0x45w;
      0xC0w; 0x48w; 0x75w; 0x4w; 0x46w; 0x8Bw; 0x4w; 0x86w]) /\
   (bc_ref (i,sym) (iDATA opCDR) =
     [0x49w; 0xF7w; 0xC0w; 0x1w; 0x0w; 0x0w; 0x0w; 0x4Cw; 0xFw; 0x45w;
      0xC0w; 0x48w; 0x75w; 0x5w; 0x46w; 0x8Bw; 0x44w; 0x86w; 0x4w]) /\
   (bc_ref (i,sym) (iDATA opCONSP) =
     [0x49w; 0xF7w; 0xC0w; 0x1w; 0x0w; 0x0w; 0x0w; 0xBAw; 0xBw; 0x0w;
      0x0w; 0x0w; 0x4Cw; 0xFw; 0x44w; 0xC2w; 0x44w; 0xFw; 0x45w; 0xC0w]) /\
   (bc_ref (i,sym) (iDATA opNATP) =
     [0x49w; 0x8Bw; 0xD0w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w; 0xD1w;
      0xBAw; 0xBw; 0x0w; 0x0w; 0x0w; 0x4Cw; 0xFw; 0x44w; 0xC2w; 0x44w;
      0xFw; 0x45w; 0xC0w]) /\
   (bc_ref (i,sym) (iDATA opSYMBOLP) =
     [0x49w; 0x8Bw; 0xD0w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w; 0xD0w;
      0xBAw; 0xBw; 0x0w; 0x0w; 0x0w; 0x4Cw; 0xFw; 0x44w; 0xC2w; 0x44w;
      0xFw; 0x45w; 0xC0w]) /\
   (bc_ref (i,sym) (iDATA opADD) =
     [0x44w; 0x8Bw; 0xCw; 0x9Fw; 0x48w; 0xFFw; 0xC3w; 0x49w; 0x8Bw;
      0xD0w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w; 0xD1w; 0x44w; 0xFw;
      0x45w; 0xC1w; 0x49w; 0x8Bw; 0xD1w; 0x48w; 0x21w; 0xC2w; 0x48w;
      0x39w; 0xD1w; 0x44w; 0xFw; 0x45w; 0xC9w; 0x41w; 0xFFw; 0xC8w;
      0x45w; 0x1w; 0xC8w; 0x48w; 0x73w; 0xFw; 0x4Cw; 0x8Bw; 0xC1w; 0xBAw;
      0x2w; 0x0w; 0x0w; 0x0w; 0x48w; 0xFFw; 0xA7w; 0x38w; 0xFFw; 0xFFw;
      0xFFw]) /\
   (bc_ref (i,sym) (iDATA opCONS) =
     [0x4Dw; 0x87w; 0xC8w; 0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw;
      0xC3w; 0x4Dw; 0x39w; 0xFEw; 0x3Ew; 0x48w; 0x75w; 0xAw; 0x48w;
      0x8Bw; 0x97w; 0x68w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xD2w;
      0x46w; 0x89w; 0x4Cw; 0xB6w; 0x4w; 0x46w; 0x89w; 0x4w; 0xB6w;
      0x45w; 0x8Bw; 0xC6w; 0x49w; 0x83w; 0xC6w; 0x2w]) /\
   (bc_ref (i,sym) (iDATA opLESS) =
     [0x4Dw; 0x87w; 0xC8w; 0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw;
      0xC3w; 0x49w; 0x8Bw; 0xD0w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w;
      0xD1w; 0x44w; 0xFw; 0x45w; 0xC1w; 0x49w; 0x8Bw; 0xD1w; 0x48w;
      0x21w; 0xC2w; 0x48w; 0x39w; 0xD1w; 0x44w; 0xFw; 0x45w; 0xC9w;
      0x4Dw; 0x39w; 0xC8w; 0xBAw; 0xBw; 0x0w; 0x0w; 0x0w; 0x4Cw; 0xFw;
      0x42w; 0xC2w; 0x44w; 0xFw; 0x43w; 0xC0w]) /\
   (bc_ref (i,sym) (iDATA opSUB) =
     [0x4Dw; 0x87w; 0xC8w; 0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw;
      0xC3w; 0x49w; 0x8Bw; 0xD0w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w;
      0xD1w; 0x44w; 0xFw; 0x45w; 0xC1w; 0x49w; 0x8Bw; 0xD1w; 0x48w;
      0x21w; 0xC2w; 0x48w; 0x39w; 0xD1w; 0x44w; 0xFw; 0x45w; 0xC9w;
      0x41w; 0xFFw; 0xC0w; 0x45w; 0x29w; 0xC8w; 0x44w; 0xFw; 0x42w;
      0xC1w]) /\
   (bc_ref (i,sym) (iDATA opSYMBOL_LESS) =
     [0x4Dw; 0x87w; 0xC8w; 0x44w; 0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw;
      0xC3w; 0x49w; 0x8Bw; 0xD0w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w;
      0xD0w; 0x44w; 0xFw; 0x45w; 0xC0w; 0x49w; 0x8Bw; 0xD1w; 0x48w;
      0x21w; 0xC2w; 0x48w; 0x39w; 0xD0w; 0x44w; 0xFw; 0x45w; 0xC8w;
      0x4Cw; 0x8Bw; 0x9Fw; 0x20w; 0xFFw; 0xFFw; 0xFFw; 0x49w; 0xC1w;
      0xE8w; 0x3w; 0x4Dw; 0x8Bw; 0xD0w; 0x4Dw; 0x85w; 0xD2w; 0x48w;
      0x74w; 0xDw; 0x49w; 0xFw; 0xB6w; 0x3w; 0x49w; 0x1w; 0xC3w; 0x49w;
      0xFFw; 0xCAw; 0x48w; 0xEBw; 0xEDw; 0x4Dw; 0x8Bw; 0xC3w; 0x49w;
      0xC1w; 0xE9w; 0x3w; 0x4Dw; 0x8Bw; 0xD1w; 0x4Cw; 0x8Bw; 0x9Fw;
      0x20w; 0xFFw; 0xFFw; 0xFFw; 0x4Dw; 0x85w; 0xD2w; 0x48w; 0x74w;
      0xDw; 0x49w; 0xFw; 0xB6w; 0x3w; 0x49w; 0x1w; 0xC3w; 0x49w; 0xFFw;
      0xCAw; 0x48w; 0xEBw; 0xEDw; 0x4Dw; 0x8Bw; 0xCBw; 0x4Dw; 0xFw;
      0xB6w; 0x10w; 0x4Dw; 0xFw; 0xB6w; 0x19w; 0x49w; 0xFFw; 0xCAw;
      0x49w; 0xFFw; 0xCBw; 0x49w; 0xFFw; 0xC0w; 0x49w; 0xFFw; 0xC1w;
      0x49w; 0x83w; 0xFBw; 0x0w; 0x48w; 0x74w; 0x23w; 0x49w; 0x83w;
      0xFAw; 0x0w; 0x48w; 0x74w; 0x24w; 0x49w; 0xFw; 0xB6w; 0x0w; 0x41w;
      0x3Aw; 0x1w; 0x48w; 0x72w; 0x1Aw; 0x48w; 0x77w; 0xFw; 0x49w; 0xFFw;
      0xC0w; 0x49w; 0xFFw; 0xC1w; 0x49w; 0xFFw; 0xCAw; 0x49w; 0xFFw;
      0xCBw; 0x48w; 0xEBw; 0xD6w; 0xB8w; 0x3w; 0x0w; 0x0w; 0x0w; 0x48w;
      0xEBw; 0x5w; 0xB8w; 0xBw; 0x0w; 0x0w; 0x0w; 0x4Cw; 0x8Bw; 0xC0w;
      0xB8w; 0x3w; 0x0w; 0x0w; 0x0w; 0x4Cw; 0x8Bw; 0xC8w; 0x4Cw; 0x8Bw;
      0xD0w; 0x4Cw; 0x8Bw; 0xD8w]) /\
   (bc_ref (i,sym) (iDATA opEQUAL) =
     [0x44w; 0x8Bw; 0xCw; 0x9Fw; 0x48w; 0xFFw; 0xC3w; 0x48w; 0x8Bw;
      0x97w; 0x70w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xD2w]) /\
   (bc_ref (i,sym) (iCONST_LOOKUP) =
     [0x48w; 0x8Bw; 0x57w; 0xC0w; 0x46w; 0x8Bw; 0x4w; 0x2w]) /\
   (bc_ref (i,sym) iJUMP_SYM =
     [0x46w; 0x8Bw; 0x4Cw; 0xAEw; 0x4w; 0x4Dw; 0x8Bw; 0xD0w; 0x44w;
      0x8Bw; 0x1Cw; 0x9Fw; 0x48w; 0xFFw; 0xC3w; 0x49w; 0xF7w; 0xC1w;
      0x1w; 0x0w; 0x0w; 0x0w; 0x48w; 0x75w; 0x30w; 0x46w; 0x8Bw; 0x4w;
      0x8Ew; 0x46w; 0x8Bw; 0x4Cw; 0x8Ew; 0x4w; 0x4Dw; 0x39w; 0xD0w;
      0x48w; 0x74w; 0x8w; 0x46w; 0x8Bw; 0x4Cw; 0x8Ew; 0x4w; 0x48w;
      0xEBw; 0xDFw; 0x46w; 0x8Bw; 0xCw; 0x8Ew; 0x46w; 0x8Bw; 0x44w;
      0x8Ew; 0x4w; 0x46w; 0x8Bw; 0xCw; 0x8Ew; 0x4Dw; 0x39w; 0xD8w;
      0x48w; 0x74w; 0x6w; 0x41w; 0xB9w; 0x3w; 0x0w; 0x0w; 0x0w; 0x44w;
      0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw; 0xC3w; 0x4Dw; 0x8Bw; 0xD1w;
      0x49w; 0x8Bw; 0xD1w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w; 0xD1w;
      0x48w; 0x74w; 0x3Bw; 0x4Dw; 0x8Bw; 0xC2w; 0x48w; 0x8Bw; 0x97w;
      0x78w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xD2w; 0x48w; 0x8Bw;
      0x8Fw; 0x40w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0x8Bw; 0x87w; 0x28w;
      0xFFw; 0xFFw; 0xFFw; 0xC6w; 0x0w; 0xAw; 0xC6w; 0x40w; 0x1w;
      0x0w; 0x48w; 0xFFw; 0xD1w; 0xB8w; 0x3w; 0x0w; 0x0w; 0x0w; 0xB9w;
      0x1w; 0x0w; 0x0w; 0x0w; 0xBAw; 0xBw; 0x0w; 0x0w; 0x0w; 0x48w;
      0xFFw; 0xA7w; 0x38w; 0xFFw; 0xFFw; 0xFFw; 0x49w; 0x8Bw; 0xD2w;
      0x48w; 0xC1w; 0xEAw; 0x2w; 0x48w; 0x3w; 0x97w; 0x60w; 0xFFw;
      0xFFw; 0xFFw; 0x48w; 0xFFw; 0xE2w]) /\
   (bc_ref (i,sym) iCALL_SYM =
     [0x46w; 0x8Bw; 0x4Cw; 0xAEw; 0x4w; 0x4Dw; 0x8Bw; 0xD0w; 0x44w;
      0x8Bw; 0x1Cw; 0x9Fw; 0x48w; 0xFFw; 0xC3w; 0x49w; 0xF7w; 0xC1w;
      0x1w; 0x0w; 0x0w; 0x0w; 0x48w; 0x75w; 0x30w; 0x46w; 0x8Bw; 0x4w;
      0x8Ew; 0x46w; 0x8Bw; 0x4Cw; 0x8Ew; 0x4w; 0x4Dw; 0x39w; 0xD0w;
      0x48w; 0x74w; 0x8w; 0x46w; 0x8Bw; 0x4Cw; 0x8Ew; 0x4w; 0x48w;
      0xEBw; 0xDFw; 0x46w; 0x8Bw; 0xCw; 0x8Ew; 0x46w; 0x8Bw; 0x44w;
      0x8Ew; 0x4w; 0x46w; 0x8Bw; 0xCw; 0x8Ew; 0x4Dw; 0x39w; 0xD8w;
      0x48w; 0x74w; 0x6w; 0x41w; 0xB9w; 0x3w; 0x0w; 0x0w; 0x0w; 0x44w;
      0x8Bw; 0x4w; 0x9Fw; 0x48w; 0xFFw; 0xC3w; 0x4Dw; 0x8Bw; 0xD1w;
      0x49w; 0x8Bw; 0xD1w; 0x48w; 0x21w; 0xC2w; 0x48w; 0x39w; 0xD1w;
      0x48w; 0x74w; 0x3Bw; 0x4Dw; 0x8Bw; 0xC2w; 0x48w; 0x8Bw; 0x97w;
      0x78w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0xFFw; 0xD2w; 0x48w; 0x8Bw;
      0x8Fw; 0x40w; 0xFFw; 0xFFw; 0xFFw; 0x48w; 0x8Bw; 0x87w; 0x28w;
      0xFFw; 0xFFw; 0xFFw; 0xC6w; 0x0w; 0xAw; 0xC6w; 0x40w; 0x1w;
      0x0w; 0x48w; 0xFFw; 0xD1w; 0xB8w; 0x3w; 0x0w; 0x0w; 0x0w; 0xB9w;
      0x1w; 0x0w; 0x0w; 0x0w; 0xBAw; 0xBw; 0x0w; 0x0w; 0x0w; 0x48w;
      0xFFw; 0xA7w; 0x38w; 0xFFw; 0xFFw; 0xFFw; 0x49w; 0x8Bw; 0xD2w;
      0x48w; 0xC1w; 0xEAw; 0x2w; 0x48w; 0x3w; 0x97w; 0x60w; 0xFFw;
      0xFFw; 0xFFw; 0x48w; 0xFFw; 0xD2w])`;

val bc_length_def = Define `
  bc_length x = LENGTH (bc_ref (0,[]) x)`;

val bs2bytes_def = Define `
  (bs2bytes (i,sym) [] = []) /\
  (bs2bytes (i,sym) (x::xs) = bc_ref (i,sym) x ++ bs2bytes (i+bc_length x,sym) xs)`;

val _ = Hol_datatype `
  code_type = BC_CODE of (num -> bc_inst_type option) # num`;

val WRITE_CODE_def = Define `
  (WRITE_CODE (BC_CODE (code,ptr)) [] = BC_CODE (code,ptr)) /\
  (WRITE_CODE (BC_CODE (code,ptr)) (c::cs) =
     WRITE_CODE (BC_CODE ((ptr =+ SOME c) code,ptr+bc_length c)) cs)`;

val bc_symbols_ok_def = Define `
  (bc_symbols_ok sym [] = T) /\
  (bc_symbols_ok sym (iCONST_NUM i::xs) = i < 2**30 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iCONST_SYM s::xs) = MEM s sym /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iJUMP i::xs) = i < 2**30 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iJNIL i::xs) = i < 2**30 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iCALL i::xs) = i < 2**30 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iSTORE i::xs) = i < 2**29 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iLOAD i::xs) = i < 2**29 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (iPOPS i::xs) = i < 2**30 /\ bc_symbols_ok sym xs) /\
  (bc_symbols_ok sym (_::xs) = bc_symbols_ok sym xs)`;

val code_ptr_def = Define `code_ptr (BC_CODE (_,p)) = p`;
val code_mem_def = Define `code_mem (BC_CODE (m,_)) = m`;

val code_heap_def = Define `
  code_heap code (sym,base_ptr,curr_ptr,space_left,dh,h) =
    ?bs hs.
      (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs = code) /\
      (curr_ptr = base_ptr + n2w (code_ptr code)) /\
      (one_byte_list base_ptr (bs2bytes (0,sym) bs ++ hs)) (fun2set (h,dh)) /\
      code_ptr code + w2n space_left < 2**30 /\ (LENGTH hs = w2n (space_left:word64)) /\
      bc_symbols_ok sym bs`;


(* definition of main invariant *)

val INIT_SYMBOLS_def = Define `
  INIT_SYMBOLS = ["NIL";"T";"QUOTE";"CONS";"CAR";"CDR";"EQUAL";"<";"SYMBOL-<";
                  "+";"-";"ATOMP";"CONSP";"NATP";"SYMBOLP";"DEFINE";"IF";
                  "LAMBDA";"FUNCALL";"ERROR";"PRINT";"LET";"LET*";"COND";"OR";
                  "AND";"FIRST";"SECOND";"THIRD";"FOURTH";"FIFTH";"LIST";"DEFUN"]`;

val IS_TRUE_def = Define `IS_TRUE ok = (ok = T)`;

val lisp_inv_def = Define `
  lisp_inv (* pointers and bounds that are constant throughout execution *)
           (a1,a2,sl,sl1,e,ex,cs,ok)
           (* high-level data that is held in the heap *)
           (x0,x1,x2,x3,x4,x5,xs,xs1,io:io_streams,xbp:num,qs:word64 list,code,amnt)
           (* implementation level equivalents *)
           (w0,w1,w2,w3,w4,w5,df,f,dg,g,bp,bp2,wsp,wi:word64,we:word64,tw0:word64,tw1:word64,tw2:word64,sp,ds,sa1,sa2,sa3,dd,d) =
    ?s0 s1 s2 s3 s4 s5 m i ss ss1 sym b.
      (LENGTH xs = LENGTH ss) /\ (LENGTH xs1 = LENGTH ss1) /\
      (LENGTH ss + w2n wsp = sl) /\ IS_TRUE ok /\
      (wi = n2w (2 * i)) /\ (we = n2w (2 * e)) /\ (tw0 = 3w) /\ (tw1 = 1w) /\
      ok_split_heap ([s0;s1;s2;s3;s4;s5]++ss++ss1,m,i,e) /\ i <= e /\ e < 2147483648 /\
      EVERY (lisp_x (m,INIT_SYMBOLS++sym))
        ((s0,x0)::(s1,x1)::(s2,x2)::(s3,x3)::(s4,x4)::(s5,x5)::ZIP(ss++ss1,xs++xs1)) /\
      (MAP ref_heap_addr [s0;s1;s2;s3;s4;s5] = [w0;w1;w2;w3;w4;w5]) /\
      ((bp,bp2) = if b then (a1,a2) else (a2,a1)) /\ sl < 2**64 /\ sl1 < 2**30 /\
      (LENGTH cs = 10) /\ (LENGTH ds = 10) /\ (amnt < 2**30) /\
      (bp && 0x3w = 0x0w) /\ (bp2 && 0x3w = 0x0w) /\ (sp && 0x3w = 0x0w) /\
      (EL 1 ds = sp + n2w (4 * sl) - n2w (4 * xbp) - 1w) /\ xbp <= sl /\
      (EL 6 ds = sp + n2w (4 * sl) - 1w) /\
      (EL 7 ds = n2w (sl1 - LENGTH ss1)) /\ LENGTH ss1 <= sl1 /\
      (EL 8 ds = n2w (LENGTH ss1)) /\ (w2n (EL 5 ds) <= e) /\
      (n2w amnt = EL 9 ds) /\
      (ref_mem bp m 0 e * ref_mem bp2 (\x.H_EMP) 0 e *
       ref_full_stack sp wsp ss ss1
         ([a1;a2;n2w e;bp2;sa1;sa2;sa3;ex] ++ cs ++ ds) (sl1 - LENGTH ss1)) (fun2set (f,df)) /\
      symtable_inv (sa1:word64,sa2:word64,sa3:word64,dg,g) (INIT_SYMBOLS++sym) /\
      code_heap code (INIT_SYMBOLS++sym,EL 4 cs,EL 2 ds,EL 3 ds,dd,d)`;

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst

(* swap *)

val w2n_lt30 = SIMP_RULE (srw_ss()) [] (INST_TYPE [``:'a``|->``:30``] w2n_lt)
val w2n_lt29 = SIMP_RULE (srw_ss()) [] (INST_TYPE [``:'a``|->``:29``] w2n_lt)

val SWAP_TAC =
  Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [];

val lisp_inv_swap0 = METIS_PROVE [] ``^LISP ==> ^LISP``;

val lisp_inv_swap1 = prove(
  ``^LISP ==>
    let (x0,x1) = (x1,x0) in
    let (w0,w1) = (w1,w0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s1`,`s0`,`s2`,`s3`,`s4`,`s5`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_swap2 = prove(
  ``^LISP ==>
    let (x0,x2) = (x2,x0) in
    let (w0,w2) = (w2,w0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s2`,`s1`,`s0`,`s3`,`s4`,`s5`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_swap3 = prove(
  ``^LISP ==>
    let (x0,x3) = (x3,x0) in
    let (w0,w3) = (w3,w0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s3`,`s1`,`s2`,`s0`,`s4`,`s5`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_swap4 = prove(
  ``^LISP ==>
    let (x0,x4) = (x4,x0) in
    let (w0,w4) = (w4,w0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s4`,`s1`,`s2`,`s3`,`s0`,`s5`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_swap5 = prove(
  ``^LISP ==>
    let (x0,x5) = (x5,x0) in
    let (w0,w5) = (w5,w0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s5`,`s1`,`s2`,`s3`,`s4`,`s0`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_swap0",lisp_inv_swap0);
val _ = save_thm("lisp_inv_swap1",lisp_inv_swap1);
val _ = save_thm("lisp_inv_swap2",lisp_inv_swap2);
val _ = save_thm("lisp_inv_swap3",lisp_inv_swap3);
val _ = save_thm("lisp_inv_swap4",lisp_inv_swap4);
val _ = save_thm("lisp_inv_swap5",lisp_inv_swap5);


(* copy *)

val lisp_inv_copy = prove(
  ``^LISP ==> let (x1,w1) = (x0,w0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s0`,`s0`,`s2`,`s3`,`s4`,`s5`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_copy",lisp_inv_copy);


(* assign const *)

val lisp_inv_Val = prove(
  ``!w. ^LISP ==> let (x0,w0) = (Val (w2n w), w2w (w:word30) << 2 !! 1w) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `H_DATA (INL w)`
  \\ Q.LIST_EXISTS_TAC [`s1`,`s2`,`s3`,`s4`,`s5`] \\ SWAP_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_Val",lisp_inv_Val);

val BLAST_LEMMA = prove(``w << 2 !! 1w = w << 2 + 1w:word32``,blastLib.BBLAST_TAC);
val lisp_inv_Val_n2w = Q.SPEC `n2w n` lisp_inv_Val
  |> DISCH ``n < dimword (:30)`` |> SIMP_RULE std_ss [w2n_n2w,AND_IMP_INTRO,BLAST_LEMMA]
  |> SIMP_RULE (std_ss++SIZES_ss) [w2w_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w,w2n_n2w]
  |> Q.GEN `n`

val _ = save_thm("lisp_inv_Val_n2w",lisp_inv_Val_n2w);

val LIST_FIND_APPEND = prove(
  ``!xs x k d. (LIST_FIND k x xs = SOME d) ==> (LIST_FIND k (x:'a) (xs++ys) = SOME d)``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def,APPEND] \\ REPEAT STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss []);

val LIST_FIND_NEQ = prove(
  ``!xs k d. (LIST_FIND k x xs = SOME d) /\ ~(x = y) ==>
             ~(LIST_FIND k (y:'a) (xs++ys) = SOME d)``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def,APPEND] \\ REPEAT STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`~(y = h)` by ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC LIST_FIND_LESS_EQ \\ DECIDE_TAC)
  \\ Cases_on `y = h` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ IMP_RES_TAC LIST_FIND_LESS_EQ \\ DECIDE_TAC);

val EXISTS_OVER_CONJ = METIS_PROVE [] ``(?x. P x) /\ Q = ?x. P x /\ Q``;

val lisp_inv_Sym_w2w_lemma = prove(
  ``!w v. (w2w (w:29 word) << 3 !! 3w = w2w v << 3 !! 3w:word32) = (w = v)``,
  blastLib.BBLAST_TAC)

val lisp_inv_Sym_blast = prove(
  ``(w:word32 << 3 !! 0x3w = 8w * w + 3w) /\
    (v:word64 << 3 !! 0x3w = 8w * v + 3w)``,
  blastLib.BBLAST_TAC)

val lisp_inv_Sym_lemma = prove(
  ``!w s. (LIST_FIND 0 s INIT_SYMBOLS = SOME (w2n w)) ==> ^LISP ==>
      (let (x0,w0) = (Sym s, w2w (w:29 word) << 3 !! 3w) in ^LISP) /\
      (((w2w w0):word64 = w2w (w:29 word) << 3 !! 3w) = (x0 = Sym s))``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `H_DATA (INR w)`
  \\ Q.LIST_EXISTS_TAC [`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (Cases_on `x0` \\ FULL_SIMP_TAC (srw_ss()) [lisp_x_def]
    \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [ref_heap_addr_def] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM MP_TAC THEN1 blastLib.BBLAST_TAC THEN1 blastLib.BBLAST_TAC
    \\ REPEAT STRIP_TAC \\ Cases_on `s = s'` THEN1
     (`SOME (w2n w) = SOME k` by METIS_TAC [LIST_FIND_APPEND]
      \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,lisp_inv_Sym_blast]
      \\ `(8 * k + 3) < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w])
    \\ `~(w2n w = k)` by METIS_TAC [LIST_FIND_NEQ]
    \\ ASM_SIMP_TAC std_ss [lisp_inv_Sym_w2w_lemma]
    \\ Cases_on `w` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,w2n_n2w]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,lisp_inv_Sym_blast]
    \\ `(8 * k + 3) < 4294967296` by DECIDE_TAC
    \\ `(8 * n + 3) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ IMP_RES_TAC (DECIDE ``n<4294967296 ==> n<18446744073709551616:num``)
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC)
  THEN1
    (Q.EXISTS_TAC `w2n w`
     \\ ASM_SIMP_TAC std_ss [n2w_w2n,w2n_lt29,LIST_FIND_APPEND])
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [LET_DEF] |> Q.SPEC `n2w n` |> GEN ``n:num``;

val lisp_inv_Sym = let
  fun zip_index i [] = []
    | zip_index i (x::xs) = (numSyntax.term_of_int i,x) :: zip_index (i+1) xs
  in INIT_SYMBOLS_def
    |> concl |> dest_eq |> snd |> listSyntax.dest_list |> fst |> zip_index 0
    |> map (fn (x,y) => SPECL [x,y] lisp_inv_Sym_lemma)
    |> map (CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL))
    |> map (SIMP_RULE (srw_ss()) [w2w_n2w,bitTheory.BITS_THM,
              WORD_MUL_LSL,word_mul_n2w,word_or_n2w])
    |> LIST_CONJ
  end ;

val _ = save_thm("lisp_inv_Sym",lisp_inv_Sym);

val lisp_inv_nil = prove(
  ``^LISP ==> let (x0,w0) = (Sym "NIL",w2w tw0) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF]
  \\ STRIP_TAC \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_n2w,BITS_THM]
  \\ IMP_RES_TAC (hd (CONJUNCTS lisp_inv_Sym))) |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_zero = prove(
  ``^LISP ==> let (x0,w0) = (Val 0,w2w tw1) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF]
  \\ STRIP_TAC \\ `tw1 = 1w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_n2w,BITS_THM]
  \\ MATCH_MP_TAC (SIMP_RULE std_ss [] (Q.SPEC `0` lisp_inv_Val_n2w))
  \\ ASM_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_nil",lisp_inv_nil);
val _ = save_thm("lisp_inv_zero",lisp_inv_zero);


(* car and cdr *)

val RANGE_TAC = FULL_SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC

val ADDR_SET = SIMP_RULE std_ss [EXTENSION,GSPECIFICATION] ADDR_SET_def |>
               SIMP_RULE std_ss [IN_DEF, SimpLHS];

val lisp_inv_car = prove(
  ``isDot x0 ==> ^LISP ==>
    (let (x0,w0) = (CAR x0,f (bp + 4w * w2w w0)) in ^LISP) /\
    (bp + 4w * w2w w0) IN df /\ (w0 && 1w = 0w) /\ ((bp + 4w * w2w w0) && 3w = 0w)``,
  SIMP_TAC std_ss [isDot_thm] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF,CAR_def]
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,lisp_x_def]
  \\ Q.LIST_EXISTS_TAC [`ax`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b'`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `xx = w0` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,CONJ_ASSOC]
  \\ REVERSE STRIP_TAC
  THEN1 (Q.PAT_X_ASSUM `bp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ REVERSE STRIP_TAC
  THEN1 (Q.PAT_X_ASSUM `bp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ `k < i` by
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,RANGE_def] \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [NOT_LESS] \\ RES_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ `RANGE(0,e)k /\ k < 2147483648` by RANGE_TAC
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`m`,`bp`])
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [ref_aux_def] \\ STRIP_TAC
  \\ `2 * k < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [MULT_ASSOC,HD,TL,STAR_ASSOC]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET]
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30]
  \\ REPEAT STRIP_TAC THEN1
   (Q.PAT_X_ASSUM `!x. x IN D1 m ==> x IN D0 m` MATCH_MP_TAC
    \\ SIMP_TAC std_ss [D1_def,IN_DEF] \\ Q.EXISTS_TAC `k`
    \\ ASM_SIMP_TAC (srw_ss()) [ADDR_SET])
  \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_cdr = prove(
  ``isDot x0 ==> ^LISP ==>
    (let (x0,w0) = (CDR x0,f (bp + 4w * w2w w0 + 4w)) in ^LISP) /\
    (bp + 4w * w2w w0 + 4w) IN df /\ (w0 && 1w = 0w) /\ ((bp + 4w * w2w w0 + 4w) && 3w = 0w)``,
  SIMP_TAC std_ss [isDot_thm] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF,CDR_def]
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,lisp_x_def]
  \\ Q.LIST_EXISTS_TAC [`ay`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b'`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `xx = w0` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,CONJ_ASSOC]
  \\ REVERSE STRIP_TAC
  THEN1 (Q.PAT_X_ASSUM `bp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ REVERSE STRIP_TAC
  THEN1 (Q.PAT_X_ASSUM `bp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ `k < i` by
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,RANGE_def] \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [NOT_LESS] \\ RES_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ `RANGE(0,e)k /\ k < 2147483648` by RANGE_TAC
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`m`,`bp`])
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [ref_aux_def] \\ STRIP_TAC
  \\ `2 * k < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [MULT_ASSOC,HD,TL]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET]
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30]
  \\ REPEAT STRIP_TAC THEN1
   (Q.PAT_X_ASSUM `!x. x IN D1 m ==> x IN D0 m` MATCH_MP_TAC
    \\ SIMP_TAC std_ss [D1_def,IN_DEF] \\ Q.EXISTS_TAC `k`
    \\ ASM_SIMP_TAC (srw_ss()) [ADDR_SET])
  \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_car",lisp_inv_car);
val _ = save_thm("lisp_inv_cdr",lisp_inv_cdr);


(* cons *)



val lisp_x_UPDATE = prove(
  ``!m s i x.
      (m i = H_EMP) ==>
      !y p. lisp_x (m,s) (p,y) ==> lisp_x ((i =+ x) m,s) (p,y)``,
  NTAC 5 STRIP_TAC \\ Induct \\ FULL_SIMP_TAC std_ss [lisp_x_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC (srw_ss()) []
  \\ Cases_on `i = k` \\ FULL_SIMP_TAC (srw_ss()) [APPLY_UPDATE_THM]);

val lisp_inv_cons_blast = blastLib.BBLAST_PROVE
  ``(bp && 3w = 0w:word64) ==>
    (bp + 4w * wi && 3w = 0w) /\  (bp + 4w * wi + 4w && 3w = 0w)``;

val IN_D0 = SIMP_CONV bool_ss [IN_DEF, D0_def] ``x IN D0 m``
val IN_D1 = (REWRITE_CONV [IN_DEF] THENC SIMP_CONV bool_ss [D1_def])
                ``x IN D1 m``


val lisp_inv_cons = prove(
  ``~(wi = we) ==> ^LISP ==>
    (let (x0,w0,wi,f) = (Dot x0 x1,w2w wi,wi+2w,
       (bp + 4w * wi =+ w0) ((bp + 4w * wi + 4w =+ w1) f)) in ^LISP) /\
    (bp + 4w * wi) IN df /\ (bp + 4w * wi + 4w) IN df /\
    (bp + 4w * wi && 3w = 0w) /\  (bp + 4w * wi + 4w && 3w = 0w)``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [lisp_inv_cons_blast]
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`H_ADDR i`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`(i =+ H_BLOCK ([s0;s1],0,())) m`,`i+1`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,word_add_n2w,ref_heap_addr_def,
       LEFT_ADD_DISTRIB,WORD_MUL_LSL,word_mul_n2w]
  \\ `2 * i < 18446744073709551616 /\ 2 * e < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,n2w_11]
  \\ `i+1<=e` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ Q.ABBREV_TAC `ss2 = ss ++ ss1`
  \\ Q.ABBREV_TAC `xs2 = xs ++ xs1`
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def] \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (`~(i = k) /\ i <= k` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM])
    THEN1 (FULL_SIMP_TAC std_ss [FUN_EQ_THM,EMPTY_DEF,R0_def,APPLY_UPDATE_THM]
           \\ SRW_TAC [] [])
    THEN1 (FULL_SIMP_TAC std_ss [memory_ok_def,APPLY_UPDATE_THM] \\ STRIP_TAC
           \\ Cases_on `i = i'` \\ ASM_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
    \\ `D0 ((i =+ H_BLOCK ([s0; s1],0,())) m) = i INSERT D0 m` by
      (SIMP_TAC std_ss [EXTENSION,IN_INSERT]
       \\ SIMP_TAC std_ss [IN_DEF,D0_def,APPLY_UPDATE_THM] \\ STRIP_TAC
       \\ Cases_on `i = x` \\ ASM_SIMP_TAC (srw_ss()) [])
    \\ `D1 ((i =+ H_BLOCK ([s0; s1],0,())) m) =
        ADDR_SET [s0;s1] UNION D1 m` by
      (SIMP_TAC std_ss [EXTENSION,IN_UNION,ADDR_SET_def,GSPECIFICATION]
       \\ SIMP_TAC std_ss [IN_D1,IN_D0,APPLY_UPDATE_THM] \\ STRIP_TAC
       \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
        (Cases_on `i = k` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
          (Q.PAT_X_ASSUM `[s0; s1] = x'` (ASSUME_TAC o GSYM)
           \\ FULL_SIMP_TAC std_ss [ADDR_SET_def,MEM,GSPECIFICATION])
         \\ METIS_TAC [])
       THEN1 (SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC [ADDR_SET])
       \\ Q.EXISTS_TAC `k` \\ Cases_on `i = k` \\ ASM_SIMP_TAC (srw_ss()) []
       \\ `m k = H_EMP` by METIS_TAC [LESS_EQ_REFL]
       \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_UNION,IN_INSERT]
    \\ FULL_SIMP_TAC (srw_ss()) [ADDR_SET_def]
    \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [EVERY_DEF,CONS_11,lisp_x_def,APPLY_UPDATE_THM]
    \\ `m i = H_EMP` by FULL_SIMP_TAC std_ss [ok_split_heap_def]
    \\ ASM_SIMP_TAC std_ss [lisp_x_UPDATE]
    \\ Q.PAT_X_ASSUM `EVERY (lisp_x (m,INIT_SYMBOLS ++ sym)) (ZIP (ss2,xs2))` MP_TAC
    \\ Q.SPEC_TAC (`ZIP (ss2,xs2)`,`ys`)
    \\ Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF]
    \\ Cases \\ ASM_SIMP_TAC std_ss [lisp_x_UPDATE])
  \\ `RANGE(0,e)i` by RANGE_TAC
  \\ IMP_RES_TAC ref_mem_UPDATE \\ ASM_SIMP_TAC std_ss [ref_aux_def,STAR_ASSOC,HD,TL]
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`m`,`bp`])
  \\ `m i = H_EMP` by METIS_TAC [LESS_EQ_REFL,ok_split_heap_def]
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ FULL_SIMP_TAC std_ss [MULT_ASSOC] \\ SEP_R_TAC \\ SEP_W_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_cons",lisp_inv_cons);


(* top, pop and push *)

val lisp_inv_top = prove(
  ``~(xs = []) ==> ^LISP ==>
    (let (x0,w0) = (HD xs,f (sp + 4w * wsp)) in ^LISP) /\
    (sp + 4w * wsp) IN df /\ (sp + 4w * wsp && 3w = 0w)``,
  Cases_on `xs` \\ SIMP_TAC std_ss [NOT_CONS_NIL,LET_DEF,TL,HD]
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `ss` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF]
  \\ Q.LIST_EXISTS_TAC [`h'`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`h'::t'`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF,LENGTH,ADD1,ZIP,EVERY_DEF,APPEND]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_stack_def,APPEND] \\ SEP_R_TAC
  \\ SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `sp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val SPLIT_LIST_LESS_EQ = store_thm("SPLIT_LIST_LESS_EQ",
  ``!xs j. j <= LENGTH xs ==>
           ?xs1 xs2. (xs = xs1 ++ xs2) /\
                     (LENGTH xs1 = j)``,
  Induct \\ SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC
  THEN1 (Q.LIST_EXISTS_TAC [`[]`,`[]`] \\ ASM_SIMP_TAC std_ss [LENGTH,APPEND])
  \\ Cases_on `j` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH_NIL,APPEND,CONS_11]
  \\ RES_TAC \\ Q.EXISTS_TAC `h::xs1`
  \\ ASM_SIMP_TAC std_ss [LENGTH,APPEND_11,APPEND,CONS_11]
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,APPEND,CONS_11,ADD1]);

val ZIP_APPEND = store_thm("ZIP_APPEND",
  ``!xs1 ys1 xs2 ys2.
      (LENGTH ys1 = LENGTH xs1) ==>
      (ZIP (xs1 ++ xs2, ys1 ++ ys2) = ZIP (xs1,ys1) ++ ZIP (xs2,ys2))``,
  Induct \\ SIMP_TAC std_ss [LENGTH,LENGTH_NIL,ZIP,APPEND]
  \\ Cases_on `ys1` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH,ZIP,APPEND]);

val ref_stack_APPEND = store_thm("ref_stack_APPEND",
  ``!xs ys a.
      ref_stack a (xs ++ ys) =
      SEP_ARRAY (\a x. one (a,ref_heap_addr x)) 4w a xs *
      ref_stack (a + n2w (4 * LENGTH xs)) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,ref_stack_def,LENGTH,SEP_ARRAY_def,
    SEP_CLAUSES,WORD_ADD_0,STAR_ASSOC,MULT_CLAUSES,GSYM word_add_n2w,WORD_ADD_ASSOC]);

val ref_stack_space_LEMMA = prove(
  ``!k n p.
      p * ref_stack_space (sp + n2w (4 * n + 4 * k)) (n + k + 6) =
      SEP_EXISTS zs. SEP_ARRAY (\a x. one(a,x)) 4w (sp + n2w (4 * n)) zs *
                     p * ref_stack_space (sp + n2w (4 * n)) (n + 6) *
                     cond (LENGTH zs = k)``,
  Induct THEN1 SIMP_TAC std_ss [FUN_EQ_THM,cond_STAR,SEP_EXISTS_THM,LENGTH_NIL,
                 SEP_ARRAY_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [GSYM LEFT_ADD_DISTRIB,DECIDE ``n + SUC k = SUC n + k``]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [ADD_CLAUSES,ref_stack_space_def,
       SEP_CLAUSES,STAR_ASSOC,FUN_EQ_THM,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `w::zs` \\ FULL_SIMP_TAC std_ss [LENGTH,SEP_ARRAY_def,ADD1,
      LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Q.EXISTS_TAC `t` \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `h`
  \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_def,LEFT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [LENGTH,SEP_ARRAY_def,ADD1,
        LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val lisp_inv_pops_lemma = prove(
  ``n <= LENGTH xs ==> ^LISP ==> let (xs,wsp) = (DROP n xs,wsp + n2w n) in ^LISP``,
  STRIP_TAC \\ IMP_RES_TAC SPLIT_LIST_LESS_EQ \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LET_DEF]
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`DROP n ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF,LENGTH_APPEND]
  \\ `LENGTH xs1' <= LENGTH ss` by DECIDE_TAC
  \\ IMP_RES_TAC SPLIT_LIST_LESS_EQ
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.BUTFIRSTN_LENGTH_APPEND]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ STRIP_TAC THEN1
   (Q.PAT_X_ASSUM `xx = sl` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
    \\ Cases_on `wsp` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,w2n_n2w]
    \\ `(n' + LENGTH xs1'') < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,EVERY_APPEND,GSYM APPEND_ASSOC]
  \\ REPEAT STRIP_TAC
  THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_stack_def,word_mul_n2w]
  \\ Cases_on `wsp` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,w2n_n2w]
  \\ `(n' + LENGTH xs1'') < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [ref_stack_APPEND,word_mul_n2w,word_arith_lemma1,LEFT_ADD_DISTRIB]
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` MP_TAC
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ ASM_SIMP_TAC std_ss [ref_stack_space_LEMMA]
  \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `MAP ref_heap_addr xs1''`
  \\ ASM_SIMP_TAC std_ss [LENGTH_MAP]
  \\ `SEP_ARRAY (\a x. one (a,x)) 0x4w (sp + n2w (4 * n'))
       (MAP ref_heap_addr xs1'') =
      SEP_ARRAY (\a x. one (a,ref_heap_addr x)) 0x4w
          (sp + n2w (4 * n')) xs1''` by
    (Q.SPEC_TAC (`(sp + n2w (4 * n'))`,`w`) \\ Q.SPEC_TAC (`xs1''`,`ws`)
     \\ Induct \\ ASM_SIMP_TAC std_ss [MAP,SEP_ARRAY_def,SEP_CLAUSES])
  \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_APPEND,LENGTH_APPEND,LEFT_ADD_DISTRIB,
       ADD_ASSOC,word_arith_lemma1,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,AC ADD_COMM ADD_ASSOC])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_pops = prove(
  ``w2n (j:word30) <= LENGTH xs ==> ^LISP ==> let (xs,wsp) = (DROP (w2n j) xs,wsp + w2w j) in ^LISP``,
  Cases_on `j` \\ ASM_SIMP_TAC std_ss [w2n_n2w,w2w_def,LET_DEF] \\ STRIP_TAC
  \\ METIS_TAC [lisp_inv_pops_lemma]);

val lisp_inv_pop = prove(
  ``~(xs = []) ==> ^LISP ==> let (xs,wsp) = (TL xs,wsp+1w) in ^LISP``,
  Cases_on `xs` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,TL] \\ STRIP_TAC
  \\ `w2n (1w:word30) <= LENGTH (h::t)` by
       SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LENGTH,ADD1]
  \\ IMP_RES_TAC (Q.INST [`j`|->`1w`] lisp_inv_pops)
  \\ FULL_SIMP_TAC std_ss [EVAL ``w2n (1w:word30)``,DROP_def,DROP_0]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,EVAL ``(w2w (1w:word30)):word64``])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_push = prove(
  ``~(wsp = 0w) ==> ^LISP ==>
    (let (xs,wsp,f) = (x0::xs,wsp-1w,(sp + 4w * (wsp-1w) =+ w0) f) in ^LISP) /\
    (sp + 4w * (wsp-1w)) IN df /\ (sp + 4w * (wsp-1w) && 3w = 0w)``,
  STRIP_TAC \\ STRIP_TAC
  \\ `(sp + 4w * (wsp-1w) && 3w = 0w)` by (FULL_SIMP_TAC std_ss [lisp_inv_def,lisp_inv_cons_blast])
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ Cases_on `wsp` \\ ASM_SIMP_TAC std_ss [n2w_11,LET_DEF,ZERO_LT_dimword]
  \\ Cases_on `n` \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`s0::ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ `n' < dimword (:64)` by DECIDE_TAC
  \\ Q.PAT_X_ASSUM `xxx = sl` MP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,w2n_n2w,word_add_n2w,APPEND]
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
  THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `n' + 1 < dimword (:64)` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_stack_def,word_mul_n2w,w2n_n2w,APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,LENGTH,LEFT_ADD_DISTRIB,ADD1]
  \\ `n' + 1 + 6 = SUC (n' + 6)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [ref_stack_space_def,SEP_CLAUSES,STAR_ASSOC,SEP_EXISTS_THM]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ SEP_W_TAC \\ SEP_R_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_top",lisp_inv_top);
val _ = save_thm("lisp_inv_pop",lisp_inv_pop);
val _ = save_thm("lisp_inv_push",lisp_inv_push);
val _ = save_thm("lisp_inv_pops",lisp_inv_pops);
val _ = save_thm("lisp_inv_pops_lemma",lisp_inv_pops_lemma);


(* store and load from stack *)

val SPLIT_LIST = store_thm("SPLIT_LIST",
  ``!xs j. j < LENGTH xs ==>
           ?xs1 x xs2. (xs = xs1 ++ x::xs2) /\
                       (LENGTH xs1 = j)``,
  Induct \\ SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `j` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH_NIL,APPEND,CONS_11]
  \\ RES_TAC \\ Q.EXISTS_TAC `h::xs1`
  \\ ASM_SIMP_TAC std_ss [LENGTH,APPEND_11,APPEND,CONS_11]
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,APPEND,CONS_11,ADD1]);

val lisp_inv_load_blast = prove(
  ``(w + 4w * x && 3w = 0w) = (w && 3w = 0w:word64)``,
  blastLib.BBLAST_TAC);

val lisp_inv_load_lemma = prove(
  ``n < LENGTH xs ==> ^LISP ==>
    (let (x0,w0) = (EL n xs,f (sp + 4w * wsp + 4w * n2w n)) in ^LISP) /\
    (sp + 4w * wsp + 4w * n2w n) IN df /\ (sp + 4w * wsp + 4w * n2w n && 3w = 0w)``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF]
  \\ Q.LIST_EXISTS_TAC [`EL n ss`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF,LENGTH,ADD1,ZIP,EVERY_DEF]
  \\ `?ss1 s ss2. (ss = ss1 ++ s::ss2) /\ (LENGTH ss1 = n)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ `?xs1 x xs2. (xs = xs1 ++ x::xs2) /\ (LENGTH xs1 = n)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,ZIP,EVERY_DEF,EVERY_APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ZIP,APPEND,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,LENGTH_APPEND,LENGTH,EL,HD]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ref_stack_def,Once ref_stack_APPEND,APPEND]
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
  \\ SEP_R_TAC \\ SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_load_blast])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_load = prove(
  ``w2n (j:29 word) < LENGTH xs ==> ^LISP ==>
    (let (x0,w0) = (EL (w2n j) xs,f (sp + 4w * wsp + 4w * w2w j)) in ^LISP) /\
    (sp + 4w * wsp + 4w * w2w j) IN df /\ (sp + 4w * wsp + 4w * w2w j && 3w = 0w)``,
  Cases_on `j` \\ FULL_SIMP_TAC std_ss [w2n_n2w,w2w_def,LET_DEF]
  \\ METIS_TAC [lisp_inv_load_lemma]) |> SIMP_RULE std_ss [LET_DEF];

val LENGTH_UPDATE_NTH = store_thm("LENGTH_UPDATE_NTH",
  ``!xs n x. (LENGTH (UPDATE_NTH n x xs) = LENGTH xs)``,
  Induct \\ Cases_on `n` \\ ASM_SIMP_TAC std_ss [UPDATE_NTH_def,LENGTH]);

val UPDATE_NTH_APPEND = prove(
  ``!xs ys zs y x n.
      (LENGTH xs = n) ==>
      (UPDATE_NTH n x (xs ++ y::ys) ++ zs = xs ++ x::ys ++ zs)``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,UPDATE_NTH_def,CONS_11]);

val lisp_inv_store_lemma = prove(
  ``n < LENGTH xs ==> ^LISP ==>
    (let (xs,f) = (UPDATE_NTH n x0 xs,((sp + 4w * wsp + 4w * n2w n) =+ w0) f) in ^LISP) /\
    (sp + 4w * wsp + 4w * n2w n) IN df /\ (sp + 4w * wsp + 4w * n2w n && 3w = 0w)``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`UPDATE_NTH n s0 ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [LENGTH_UPDATE_NTH]
  \\ `?ss1 s ss2. (ss = ss1 ++ s::ss2) /\ (LENGTH ss1 = n)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ `?xs1 x xs2. (xs = xs1 ++ x::xs2) /\ (LENGTH xs1 = n)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,ZIP,EVERY_DEF,EVERY_APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ZIP,APPEND,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,ZIP,EVERY_DEF,EVERY_APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [APPEND,ZIP,EVERY_DEF]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,UPDATE_NTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_stack_def,ref_stack_APPEND]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_load_blast]
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_W_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [MAP,CONS_11]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,LENGTH_APPEND,LENGTH] \\ METIS_TAC [])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_store = prove(
  ``w2n (j:29 word) < LENGTH xs ==> ^LISP ==>
    (let (xs,f) = (UPDATE_NTH (w2n j) x0 xs,((sp + 4w * wsp + 4w * w2w j) =+ w0) f) in ^LISP) /\
    (sp + 4w * wsp + 4w * w2w j) IN df /\ (sp + 4w * wsp + 4w * w2w j && 3w = 0w)``,
  Cases_on `j` \\ FULL_SIMP_TAC std_ss [w2n_n2w,w2w_def,LET_DEF]
  \\ METIS_TAC [lisp_inv_store_lemma]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_load",lisp_inv_load);
val _ = save_thm("lisp_inv_load_lemma",lisp_inv_load_lemma);
val _ = save_thm("lisp_inv_store",lisp_inv_store);
val _ = save_thm("lisp_inv_store_lemma",lisp_inv_store_lemma);


(* test for Dot and Sym and pointer equality *)

val lisp_inv_type = prove(
  ``^LISP ==>
    ((w0 && 1w = 0w) = isDot x0) /\
    ((w0 && 3w = 1w) = isVal x0) /\
    ((w0 && 3w = 3w) = isSym x0)``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `xxx = w0` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ Cases_on `x0` \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def,
       isDot_def,isSym_def,isVal_def] \\ blastLib.BBLAST_TAC);

val _ = save_thm("lisp_inv_type",lisp_inv_type);

val lisp_inv_ignore_tw2 = prove(
  ``^LISP ==> let tw2 = temp in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_ignore_tw2",lisp_inv_ignore_tw2);

val lisp_inv_ignore_ret_stack = prove(
  ``^LISP ==> let qs = temp in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_ignore_ret_stack",lisp_inv_ignore_ret_stack);

val lisp_inv_isSym = prove(
  ``^LISP ==>
    ((w2w w0 && tw0 = tw0) = isSym x0) /\
    let tw2 = w2w w0 && tw0 in ^LISP``,
  REVERSE (REPEAT STRIP_TAC) \\ IMP_RES_TAC (GSYM lisp_inv_type)
  THEN1 (ASM_SIMP_TAC std_ss [LET_DEF] \\ METIS_TAC [lisp_inv_ignore_tw2])
  \\ ASM_SIMP_TAC std_ss []
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `tw1 = 1w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [] THEN1 blastLib.BBLAST_TAC) |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_isVal = prove(
  ``^LISP ==>
    ((w2w w0 && tw0 = tw1) = isVal x0) /\
    let tw2 = w2w w0 && tw0 in ^LISP``,
  REVERSE (REPEAT STRIP_TAC) \\ IMP_RES_TAC (GSYM lisp_inv_type)
  THEN1 (ASM_SIMP_TAC std_ss [LET_DEF] \\ METIS_TAC [lisp_inv_ignore_tw2])
  \\ ASM_SIMP_TAC std_ss []
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `tw1 = 1w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [] THEN1 blastLib.BBLAST_TAC) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_isVal",lisp_inv_isVal);
val _ = save_thm("lisp_inv_isSym",lisp_inv_isSym);

val WORD_OR_EQ_WORD_ADD_LEMMA = prove(
  ``!w. (w << 2 !! 1w = w << 2 + 1w:word32) /\
        (w << 3 !! 3w = w << 3 + 3w:word32)``,
  blastLib.BBLAST_TAC);

val LIST_FIND_LEMMA = prove(
  ``!xs k. ~(s1 = s2) /\
           (LIST_FIND k s1 xs = SOME n) ==>
           (LIST_FIND k s2 xs = SOME m) ==> ~(m = n)``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `s1 = h` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `s2 = h` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ IMP_RES_TAC LIST_FIND_LESS_EQ \\ DECIDE_TAC);

val lisp_inv_eq_lemma = prove(
  ``~isDot x0 ==> ^LISP ==>
    ((w0 = w1) = (x0 = x1))``,
  Cases_on `x0` \\ Cases_on `x1` \\ SIMP_TAC (srw_ss()) [isDot_def]
  \\ SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,lisp_x_def,ref_heap_addr_def]
  THEN1 blastLib.BBLAST_TAC
  THEN1
   (REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_OR_EQ_WORD_ADD_LEMMA,w2w_def,w2n_n2w]
    \\ `(4 * n' + 1) < 4294967296` by DECIDE_TAC
    \\ `(4 * n + 1) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,n2w_11]
    \\ DECIDE_TAC)
  THEN1 blastLib.BBLAST_TAC
  THEN1 blastLib.BBLAST_TAC
  THEN1 blastLib.BBLAST_TAC
  THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_OR_EQ_WORD_ADD_LEMMA,w2w_def,w2n_n2w]
    \\ `(8 * k' + 3) < 4294967296` by DECIDE_TAC
    \\ `(8 * k + 3) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,n2w_11]
    \\ Cases_on `s = s'` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC LIST_FIND_LEMMA \\ DECIDE_TAC));

val lisp_inv_eq = prove(
  ``~isDot x0 \/ ~isDot x1 ==> ^LISP ==> ((w0 = w1) = (x0 = x1))``,
  METIS_TAC [lisp_inv_eq_lemma,lisp_inv_swap1]);

val lisp_inv_eq_zero = store_thm("lisp_inv_eq_zero",
  ``^LISP ==> ((tw1 = w2w w0) = (x0 = Val 0))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC lisp_inv_swap1
  \\ IMP_RES_TAC (Q.SPEC `0w` lisp_inv_Val)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ IMP_RES_TAC lisp_inv_swap1
  \\ IMP_RES_TAC (RW [isDot_def] (Q.INST [`x1`|->`Val 0`] lisp_inv_eq))
  \\ FULL_SIMP_TAC std_ss [EVAL ``(w2w (0w:word30):word32) << 2 !! 1w``]
  \\ `tw1 = 1w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx = (x0 = Val 0)` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ blastLib.BBLAST_TAC);

val lisp_inv_eq_lucky = prove(
  ``!x0 x1 w0 w1. (w0 = w1) /\ ^LISP ==> (x0 = x1)``,
  REVERSE Induct \\ SIMP_TAC std_ss []
  THEN1 METIS_TAC [lisp_inv_eq,isDot_def]
  THEN1 METIS_TAC [lisp_inv_eq,isDot_def]
  \\ REVERSE Cases \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 METIS_TAC [lisp_inv_eq,isDot_def]
  THEN1 METIS_TAC [lisp_inv_eq,isDot_def]
  \\ REPEAT STRIP_TAC THEN1
   (`isDot (Dot x0 x0')` by ASM_SIMP_TAC std_ss [isDot_def]
    \\ IMP_RES_TAC lisp_inv_car \\ FULL_SIMP_TAC std_ss [CAR_def]
    \\ IMP_RES_TAC lisp_inv_swap1
    \\ `isDot (Dot S' S0)` by ASM_SIMP_TAC std_ss [isDot_def]
    \\ IMP_RES_TAC lisp_inv_car \\ FULL_SIMP_TAC std_ss [CAR_def]
    \\ IMP_RES_TAC lisp_inv_swap1 \\ RES_TAC)
  THEN1
   (`isDot (Dot x0 x0')` by ASM_SIMP_TAC std_ss [isDot_def]
    \\ IMP_RES_TAC lisp_inv_cdr \\ FULL_SIMP_TAC std_ss [CDR_def]
    \\ IMP_RES_TAC lisp_inv_swap1
    \\ `isDot (Dot S' S0)` by ASM_SIMP_TAC std_ss [isDot_def]
    \\ IMP_RES_TAC lisp_inv_cdr \\ FULL_SIMP_TAC std_ss [CDR_def]
    \\ IMP_RES_TAC lisp_inv_swap1 \\ RES_TAC));

val _ = save_thm("lisp_inv_eq",lisp_inv_eq);
val _ = save_thm("lisp_inv_eq_lucky",lisp_inv_eq_lucky);


(* add, sub and < *)

val lisp_inv_limit_blast = blastLib.BBLAST_PROVE
  ``w << 2 !! 1w = 4w * w + 1w:word32``;

val lisp_inv_limit = prove(
  ``isVal x0 /\ isVal x1 ==> ^LISP ==>
    (getVal x0 + getVal x1 < 2**30 = w2n (w0 - 1w) + w2n w1 < 2**32)``,
  SIMP_TAC std_ss [isVal_thm] \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `x0 = xxx` (ASSUME_TAC)
  \\ Q.PAT_X_ASSUM `x1 = xxx` (ASSUME_TAC)
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def,lisp_inv_limit_blast]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_n2w,BITS_THM,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
  \\ `(4 * a) < 4294967296` by DECIDE_TAC
  \\ `(4 * a' + 1) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val lisp_inv_add_lemma = prove(
  ``w2n (w0 - 1w) + w2n w1 < 2**32 ==> ^LISP ==>
    isVal x0 /\ isVal x1 ==>
    let (x0,w0) = (LISP_ADD x0 x1,w0-1w+w1) in ^LISP``,
  SIMP_TAC std_ss [isVal_thm,LISP_ADD_def] \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a + a')))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,WORD_OR_EQ_WORD_ADD_LEMMA]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,WORD_MUL_LSL]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,ADD_ASSOC]
  \\ `4 * a < 4294967296 /\ 4 * a' + 1 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ `(a+a') < 1073741824` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,LEFT_ADD_DISTRIB]);

val lisp_inv_add = prove(
  ``^LISP ==>
    isVal x0 /\ isVal x1 /\ getVal x0 + getVal x1 < 2**30 ==>
    (let (x0,w0) = (LISP_ADD x0 x1,w0-1w+w1) in ^LISP) /\
    w2n (w0 - 1w) + w2n w1 < 2**32``,
  REPEAT STRIP_TAC \\ METIS_TAC [lisp_inv_add_lemma,lisp_inv_limit])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_add_nop = prove(
  ``^LISP ==>
    isVal x0 /\ isVal x1 /\ ~(getVal x0 + getVal x1 < 2**30) ==>
    (let (x0,w0,tw2) = (Val 0,w2w tw1,2w) in ^LISP) /\
    2**32 <= w2n (w0 - 1w) + w2n w1 /\
    ((31 -- 0) tw1 = tw1)``,
  REVERSE (REPEAT STRIP_TAC) \\ SIMP_TAC bool_ss [GSYM NOT_LESS]
  THEN1 (FULL_SIMP_TAC std_ss [lisp_inv_def] \\ EVAL_TAC)
  THEN1 METIS_TAC [lisp_inv_limit] \\ SIMP_TAC std_ss [LET_DEF]
  \\ MATCH_MP_TAC lisp_inv_zero
  \\ MATCH_MP_TAC lisp_inv_ignore_tw2 \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_limit1 = prove(
  ``isVal x0 ==> ^LISP ==>
    (getVal x0 + 1 < 2**30 = w2n w0 + 4 < 2**32)``,
  SIMP_TAC std_ss [isVal_thm] \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `x0 = xxx` (ASSUME_TAC)
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def,lisp_inv_limit_blast]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_n2w,BITS_THM,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
  \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val lisp_inv_add1_lemma = prove(
  ``isVal x0 /\ w2n w0 + 4 < 2**32 ==> ^LISP ==>
    (let (x0,w0) = (Val (getVal x0 + 1),w0+4w) in ^LISP)``,
  SIMP_TAC std_ss [isVal_thm] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a + 1)))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,WORD_OR_EQ_WORD_ADD_LEMMA]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,WORD_MUL_LSL]
  \\ `4 * a + 1 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ `a+1 < 1073741824` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  \\ AP_TERM_TAC \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];
val lisp_inv_sub = prove(
  ``isVal x0 /\ isVal x1 ==> ^LISP ==>
    let (x0,w0) = (Val (getVal x0 - getVal x1),if w1 <=+ w0 then (w0-w1)+1w else 1w) in ^LISP``,
  SIMP_TAC std_ss [isVal_thm] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a - a')))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,WORD_OR_EQ_WORD_ADD_LEMMA]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,WORD_MUL_LSL]
  \\ `4 * a + 1 < 4294967296 /\ 4 * a' + 1 < 4294967296` by DECIDE_TAC
  \\ `(a-a') < 1073741824` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,word_ls_n2w]
  \\ REVERSE (Cases_on `a' <= a`) \\ ASM_SIMP_TAC std_ss []
  THEN1 (`a - a' = 0` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ `~(a < a')` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w]
  \\ AP_TERM_TAC \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];
val lisp_inv_sub = prove(
  ``isVal x0 /\ isVal x1 ==> ^LISP ==>
    let (x0,w0) = (Val (getVal x0 - getVal x1),if w1 <=+ w0 then (w0-w1)+1w else 1w) in ^LISP``,
  SIMP_TAC std_ss [isVal_thm] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a - a')))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,WORD_OR_EQ_WORD_ADD_LEMMA]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,WORD_MUL_LSL]
  \\ `4 * a + 1 < 4294967296 /\ 4 * a' + 1 < 4294967296` by DECIDE_TAC
  \\ `(a-a') < 1073741824` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,word_ls_n2w]
  \\ REVERSE (Cases_on `a' <= a`) \\ ASM_SIMP_TAC std_ss []
  THEN1 (`a - a' = 0` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ `~(a < a')` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w]
  \\ AP_TERM_TAC \\ DECIDE_TAC);

val lisp_inv_add1 = prove(
  ``^LISP ==>
    isVal x0 /\ getVal x0 + 1 < 2**30 ==>
    (let (x0,w0) = (LISP_ADD x0 (Val 1),w0+4w) in ^LISP) /\
    w2n w0 + 4 < 2**32``,
  SIMP_TAC std_ss [LET_DEF,LISP_ADD_def,getVal_def]
  \\ METIS_TAC [SIMP_RULE std_ss [LET_DEF] lisp_inv_add1_lemma,
                SIMP_RULE std_ss [LET_DEF] lisp_inv_limit1])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_add1_nop = prove(
  ``^LISP ==>
    isVal x0 /\ ~(getVal x0 + 1 < 2**30) ==>
    (let (x0,w0,tw2) = (Val 0,w2w tw1,2w) in ^LISP) /\
    2**32 <= w2n w0 + 4 /\
    ((31 -- 0) tw1 = tw1)``,
  REVERSE (REPEAT STRIP_TAC) \\ SIMP_TAC bool_ss [GSYM NOT_LESS]
  THEN1 (FULL_SIMP_TAC std_ss [lisp_inv_def] \\ EVAL_TAC)
  THEN1 METIS_TAC [lisp_inv_limit1] \\ SIMP_TAC std_ss [LET_DEF]
  \\ MATCH_MP_TAC lisp_inv_zero
  \\ MATCH_MP_TAC lisp_inv_ignore_tw2 \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_sub = prove(
  ``isVal x0 /\ isVal x1 ==> ^LISP ==>
    let (x0,w0) = (LISP_SUB x0 x1,if w0 + 0x1w <+ w1 then w2w tw1 else w0 + 0x1w - w1) in ^LISP``,
  SIMP_TAC std_ss [isVal_thm,LISP_SUB_def] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a - a')))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,WORD_OR_EQ_WORD_ADD_LEMMA]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,WORD_MUL_LSL]
  \\ `4 * a + 1 + 1 < 4294967296 /\ 4 * a' + 1 < 4294967296` by DECIDE_TAC
  \\ `(a-a') < 1073741824` by DECIDE_TAC
  \\ `4 * (a-a') < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w]
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ Cases_on `4 * a + 1 < 4 * a'` \\ ASM_SIMP_TAC std_ss []
  \\ AP_TERM_TAC THEN1 DECIDE_TAC
  \\ `a' <= a` by DECIDE_TAC \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_sub1 = prove(
  ``isVal x0 /\ ~(x0 = Val 0) ==> ^LISP ==>
    let (x0,w0) = (LISP_SUB x0 (Val 1),w0-4w) in ^LISP``,
  SIMP_TAC std_ss [isVal_thm,LISP_SUB_def,getVal_def] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a - 1)))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,WORD_OR_EQ_WORD_ADD_LEMMA]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,WORD_MUL_LSL]
  \\ Q.PAT_X_ASSUM `x0 = Val a` (fn th => FULL_SIMP_TAC std_ss [th,SExp_11])
  \\ `(a - 1) < 1073741824 /\ a < 1073741825 /\ ~(4 * a + 1 < 4)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2]
  \\ AP_TERM_TAC \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_less_lemma = prove(
  ``!w v:word32. ((w << 2 !! 1w) <+ (v << 2 !! 1w)) = ((w << 2) <+ (v << 2))``,
  REPEAT STRIP_TAC \\ blastLib.BBLAST_TAC);

val lisp_inv_less = prove(
  ``isVal x0 /\ isVal x1 ==> ^LISP ==> (w0 <+ w1 = getVal x0 < getVal x1)``,
  SIMP_TAC std_ss [isVal_thm] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [getVal_def]
  \\ ASM_SIMP_TAC std_ss [lisp_inv_def,EVERY_DEF,lisp_x_def,MAP,CONS_11,
       ref_heap_addr_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ ASM_SIMP_TAC std_ss [lisp_inv_less_lemma]
  \\ `(4 * a) < 4294967296 /\ (4 * a') < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,word_lo_n2w]);

val lisp_inv_even = prove(
  ``isVal x0 ==> ^LISP ==> ((w2w w0 && 4w = 0w:word64) = EVEN (getVal x0))``,
  SIMP_TAC std_ss [isVal_thm] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [getVal_def]
  \\ ASM_SIMP_TAC std_ss [lisp_inv_def,EVERY_DEF,lisp_x_def,MAP,CONS_11,
       ref_heap_addr_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `w0 = dfgdf` (fn th => SIMP_TAC std_ss [th])
  \\ `!w:word30. (w2w (w2w w << 2 !! 0x1w:word32) && 0x4w = 0x0w:word64) = (w && 1w = 0w)` by blastLib.BBLAST_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `n2w a`) \\ SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [n2w_and_1] \\ SIMP_TAC wstd_ss [n2w_11]
  \\ `a MOD 2 < 2` by METIS_TAC [MOD_LESS,DECIDE ``0<2:num``]
  \\ `a MOD 2 < 1073741824` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [EVEN_MOD2]);

val ref_heap_addr_alt = prove(
  ``(ref_heap_addr (H_ADDR a) = n2w a << 1) /\
    (ref_heap_addr (H_DATA (INL w)) = w2w w << 2 + 0x1w) /\
    (ref_heap_addr (H_DATA (INR v)) = w2w v << 3 + 0x3w)``,
  SIMP_TAC std_ss [ref_heap_addr_def] \\ blastLib.BBLAST_TAC);

val lisp_inv_div2 = prove(
  ``isVal x0 ==> ^LISP ==>
    let (x0,w0) = (Val (getVal x0 DIV 2),(w0 >>> 3) << 2 + 1w) in ^LISP``,
  SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,TL,ZIP,EVERY_DEF,getVal_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INL (n2w (a DIV 2)))`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n,w2n_lt30] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ SIMP_TAC wstd_ss [DIV_LT_X,w2n_n2w]
  \\ Q.PAT_X_ASSUM `xxx = w0` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def]
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ SUBGOAL `n2w (a DIV 2) = (n2w a >>> 1):word30`
  \\ ASM_SIMP_TAC std_ss []
  THEN1 (Q.SPEC_TAC (`(n2w a):word30`,`ww`) \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr]
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,DIV_LT_X] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_add",lisp_inv_add);
val _ = save_thm("lisp_inv_add_nop",lisp_inv_add_nop);
val _ = save_thm("lisp_inv_sub",lisp_inv_sub);
val _ = save_thm("lisp_inv_add1",lisp_inv_add1);
val _ = save_thm("lisp_inv_add1_nop",lisp_inv_add1_nop);
val _ = save_thm("lisp_inv_sub1",lisp_inv_sub1);
val _ = save_thm("lisp_inv_less",lisp_inv_less);
val _ = save_thm("lisp_inv_even",lisp_inv_even);
val _ = save_thm("lisp_inv_div2",lisp_inv_div2);


(* depth limit *)

val addr_path_def = Define `
  (addr_path s [] sym m = ~isDot s) /\
  (addr_path s (a::xs) sym m =
     lisp_x (m,sym) (H_ADDR a,s) /\ (LDEPTH s = SUC (LENGTH xs)) /\
     (addr_path (CAR s) xs sym m \/ addr_path (CDR s) xs sym m))`;

val lisp_x_IMP_addr_path = prove(
  ``!s a. lisp_x (m,sym) (a,s) ==>
          ?xs. addr_path s xs sym m /\ (LDEPTH s = LENGTH xs)``,
  REVERSE (Induct) \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [isDot_def,addr_path_def,LDEPTH_def,LENGTH]
  THEN1 METIS_TAC [isDot_def,addr_path_def,LDEPTH_def,LENGTH]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,LDEPTH_def,MAX_DEF]
  \\ RES_TAC \\ Q.EXISTS_TAC `k::if LDEPTH s < LDEPTH s' then xs else xs'`
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ REVERSE STRIP_TAC THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [addr_path_def,CAR_def,CDR_def,LDEPTH_def,MAX_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) [lisp_x_def] \\ METIS_TAC []);

val addr_path_APPEND = prove(
  ``!xs t. addr_path t (xs ++ y::ys) sym m ==> ?s2. addr_path s2 (y::ys) sym m``,
  Induct \\ SIMP_TAC std_ss [APPEND] THEN1 METIS_TAC []
  \\ SIMP_TAC std_ss [Once addr_path_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ METIS_TAC []);

val lisp_x11 = prove(
  ``!s1 s2 a. lisp_x (m,sym) (a,s1) /\ lisp_x (m,sym) (a,s2) ==> (s1 = s2)``,
  REVERSE Induct THEN1
   (SIMP_TAC std_ss [lisp_x_def] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ Cases_on `s2` \\ FULL_SIMP_TAC (srw_ss()) [lisp_x_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [LIST_FIND_LEMMA])
  THEN1
   (SIMP_TAC std_ss [lisp_x_def] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ Cases_on `s2` \\ FULL_SIMP_TAC (srw_ss()) [lisp_x_def])
  \\ SIMP_TAC std_ss [lisp_x_def] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ Cases_on `s2` \\ FULL_SIMP_TAC (srw_ss()) [lisp_x_def]
  \\ STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val addr_path_ALL_DISTINCT = prove(
  ``!xs s sym m. addr_path s xs sym m ==> ALL_DISTINCT xs``,
  Induct \\ SIMP_TAC std_ss [ALL_DISTINCT] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC [addr_path_def]
  \\ FULL_SIMP_TAC std_ss [MEM_SPLIT]
  \\ FULL_SIMP_TAC std_ss [] \\ Q.PAT_X_ASSUM `!s.bbb` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [addr_path_def]
  \\ IMP_RES_TAC addr_path_APPEND
  \\ FULL_SIMP_TAC std_ss [addr_path_def]
  \\ `s = s2` by METIS_TAC [lisp_x11]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC);

val addr_path_MEM = prove(
  ``!xs s. addr_path s xs sym m /\ MEM x xs ==> ~(m x = H_EMP)``,
  Induct \\ ASM_SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [addr_path_def] \\ POP_ASSUM MP_TAC
    \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [lisp_x_def])
  \\ FULL_SIMP_TAC std_ss [addr_path_def] \\ METIS_TAC []);

val ALL_DISTINCT_MAP_SUC = prove(
  ``!xs. ALL_DISTINCT xs ==> ALL_DISTINCT (MAP SUC xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [ALL_DISTINCT,MAP,MEM_MAP]);

val RANGE_LEMMA = prove(
  ``(RANGE (0,0) = {}) /\
    (RANGE (0,SUC i) = i INSERT RANGE (0,i))``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC);

val FINITE_RANGE = prove(
  ``!i. FINITE (RANGE(0,i))``,
  Induct \\ ASM_SIMP_TAC std_ss [RANGE_LEMMA,FINITE_EMPTY,FINITE_INSERT]);

val CARD_RANGE = prove(
  ``!i. CARD (RANGE(0,i)) = i``,
  Induct \\ ASM_SIMP_TAC std_ss [RANGE_LEMMA,CARD_EMPTY,CARD_INSERT,FINITE_RANGE]
  \\ RANGE_TAC);

val PIGEONHOLE_LEMMA = prove(
  ``!k xs. ALL_DISTINCT xs ==> k < LENGTH xs ==> ?i. MEM i xs /\ k <= i``,
  REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `?f. INJ f (LIST_TO_SET xs) (RANGE(0,k))` by
   (Q.EXISTS_TAC `I` \\ SIMP_TAC std_ss [INJ_DEF]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def,GSYM NOT_LESS] \\ METIS_TAC [])
  \\ `FINITE (RANGE (0,k))` by ASM_SIMP_TAC std_ss [FINITE_RANGE]
  \\ IMP_RES_TAC INJ_CARD
  \\ `CARD (LIST_TO_SET xs) = LENGTH xs` by ASM_SIMP_TAC std_ss [ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ FULL_SIMP_TAC std_ss [CARD_RANGE] \\ DECIDE_TAC);

val lisp_x_LDEPTH = prove(
  ``lisp_x (m,sym) (a,s) /\ (!i. k <= i ==> (m i = H_EMP)) ==> LDEPTH s <= k``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC lisp_x_IMP_addr_path
  \\ IMP_RES_TAC addr_path_ALL_DISTINCT
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SUBGOAL `?i. MEM i xs /\ k <= i` THEN1 METIS_TAC [addr_path_MEM]
  \\ METIS_TAC [PIGEONHOLE_LEMMA]);

val lisp_inv_LDEPTH = prove(
  ``^LISP ==> LDEPTH x0 <= e``,
  STRIP_TAC \\ MATCH_MP_TAC (GEN_ALL lisp_x_LDEPTH)
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,EVERY_DEF,lisp_x_def,MAP,CONS_11,
         ref_heap_addr_def] \\ Q.LIST_EXISTS_TAC [`INIT_SYMBOLS ++ sym`,`m`,`s0`]
  \\ FULL_SIMP_TAC std_ss [ok_split_heap_def] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!k. bbb` MATCH_MP_TAC \\ DECIDE_TAC);

val _ = save_thm("lisp_inv_LDEPTH",lisp_inv_LDEPTH);


(* ignore write to other heap half *)

val lisp_inv_ignore_write1 = prove(
  ``RANGE(0,e)j ==> ^LISP ==>
    (let f = (bp2 + n2w (8 * j) =+ w) f in ^LISP) /\ (bp2 + n2w (8 * j)) IN df``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`(\x.H_EMP)`,`bp2`])
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM,STAR_ASSOC]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`w`,`y`]
  \\ SEP_W_TAC);

val lisp_inv_ignore_write2 = prove(
  ``RANGE(0,e)j ==> ^LISP ==>
    (let f = (bp2 + n2w (8 * j) + 4w =+ w) f in ^LISP) /\ (bp2 + n2w (8 * j) + 4w) IN df``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [LET_DEF,lisp_inv_def,EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`(\x.H_EMP)`,`bp2`])
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM,STAR_ASSOC]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`x`,`w`]
  \\ SEP_W_TAC);

val _ = save_thm("lisp_inv_ignore_write1",lisp_inv_ignore_write1);
val _ = save_thm("lisp_inv_ignore_write2",lisp_inv_ignore_write2);


(* error *)

val gc_w2w_lemma = prove(
  ``!w. ((w2w:word64->word32) ((w2w:word32->word64) w) = w) /\
        ((31 -- 0) ((w2w:word32->word64) w) = w2w w) /\
        ((31 >< 0) bp = (w2w bp):word32) /\
        ((63 >< 32) bp = (w2w (bp >>> 32)):word32) /\
        (w2w ((w2w (bp >>> 32)):word32) << 32 !! w2w ((w2w bp):word32) = bp:word64)``,
  blastLib.BBLAST_TAC);

val lisp_inv_error = store_thm("lisp_inv_error",
  ``^LISP ==>
    (w2w (f (sp - 0xC4w)) << 32 !! w2w (f (sp - 0xC8w)) = ex) /\
    {sp - 0xC4w; sp - 0xC8w} SUBSET df /\
    (sp - 0xC4w && 0x3w = 0x0w) /\ (sp - 0xC8w && 0x3w = 0x0w)``,
  SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,APPEND]
  \\ NTAC 8 (ONCE_REWRITE_TAC [ref_static_def]) \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3,INSERT_SUBSET,EMPTY_SUBSET]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [gc_w2w_lemma]
  \\ Q.PAT_X_ASSUM `sp && 0x3w = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC);


(* I/O *)

val lisp_inv_ignore_io = prove(
  ``!temp. ^LISP ==> let io = temp in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_inv_def]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_ignore_io",lisp_inv_ignore_io);


(* read cs and ds, writing ds *)

val expand_list = store_thm("expand_list",
  ``!cs. (LENGTH cs = 10) ==>
         ?c0 c1 c2 c3 c4 c5 c6 c7 c8 c9. cs = [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9]``,
  Cases \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11,NOT_CONS_NIL]
  \\ DECIDE_TAC);

val EL_CONS = store_thm("EL_CONS",
  ``!n x xs. (EL n (x::xs)) = if n = 0 then x else EL (n-1) xs``,
  Cases \\ SIMP_TAC std_ss [EL,HD,TL,ADD1]);

val lisp_inv_cs_read_blast = blastLib.BBLAST_PROVE
  ``(w2w (w1:word32) << 32 !! w2w (w2:word32) = w:word64) =
    (w1 = w2w (w >>> 32)) /\ (w2 = w2w w)``;

val one_fun2set_IMP = prove(
  ``(one (a,x)) (fun2set (f,df)) ==> (f a = x) /\ a IN df``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (REWRITE_RULE [SEP_CLAUSES] (Q.SPECL [`a`,`x`,`emp`] one_fun2set)));

val lisp_inv_cs_read = prove(
  ``^LISP ==>
    (w2w (f (sp - n2w (252 - 8 * 2))) << 32 !! w2w (f (sp - n2w (256 - 8 * 2))) = (n2w e):word64) /\
    (sp - n2w (252 - 8 * 2)) IN df /\ (sp - n2w (256 - 8 * 2)) IN df /\
    (w2w (f (sp - n2w (252 - 8 * 4))) << 32 !! w2w (f (sp - n2w (256 - 8 * 4))) = sa1) /\
    (sp - n2w (252 - 8 * 4)) IN df /\ (sp - n2w (256 - 8 * 4)) IN df /\
    (w2w (f (sp - n2w (252 - 8 * 5))) << 32 !! w2w (f (sp - n2w (256 - 8 * 5))) = sa2) /\
    (sp - n2w (252 - 8 * 5)) IN df /\ (sp - n2w (256 - 8 * 5)) IN df /\
    (w2w (f (sp - n2w (252 - 8 * 6))) << 32 !! w2w (f (sp - n2w (256 - 8 * 6))) = sa3) /\
    (sp - n2w (252 - 8 * 6)) IN df /\ (sp - n2w (256 - 8 * 6)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 0))) << 32 !! w2w (f (sp - n2w (192 - 8 * 0))) = EL 0 cs) /\
    (sp - n2w (188 - 8 * 0)) IN df /\ (sp - n2w (192 - 8 * 0)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 1))) << 32 !! w2w (f (sp - n2w (192 - 8 * 1))) = EL 1 cs) /\
    (sp - n2w (188 - 8 * 1)) IN df /\ (sp - n2w (192 - 8 * 1)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 2))) << 32 !! w2w (f (sp - n2w (192 - 8 * 2))) = EL 2 cs) /\
    (sp - n2w (188 - 8 * 2)) IN df /\ (sp - n2w (192 - 8 * 2)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 3))) << 32 !! w2w (f (sp - n2w (192 - 8 * 3))) = EL 3 cs) /\
    (sp - n2w (188 - 8 * 3)) IN df /\ (sp - n2w (192 - 8 * 3)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 4))) << 32 !! w2w (f (sp - n2w (192 - 8 * 4))) = EL 4 cs) /\
    (sp - n2w (188 - 8 * 4)) IN df /\ (sp - n2w (192 - 8 * 4)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 5))) << 32 !! w2w (f (sp - n2w (192 - 8 * 5))) = EL 5 cs) /\
    (sp - n2w (188 - 8 * 5)) IN df /\ (sp - n2w (192 - 8 * 5)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 6))) << 32 !! w2w (f (sp - n2w (192 - 8 * 6))) = EL 6 cs) /\
    (sp - n2w (188 - 8 * 6)) IN df /\ (sp - n2w (192 - 8 * 6)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 7))) << 32 !! w2w (f (sp - n2w (192 - 8 * 7))) = EL 7 cs) /\
    (sp - n2w (188 - 8 * 7)) IN df /\ (sp - n2w (192 - 8 * 7)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 8))) << 32 !! w2w (f (sp - n2w (192 - 8 * 8))) = EL 8 cs) /\
    (sp - n2w (188 - 8 * 8)) IN df /\ (sp - n2w (192 - 8 * 8)) IN df /\
    (w2w (f (sp - n2w (188 - 8 * 9))) << 32 !! w2w (f (sp - n2w (192 - 8 * 9))) = EL 9 cs) /\
    (sp - n2w (188 - 8 * 9)) IN df /\ (sp - n2w (192 - 8 * 9)) IN df``,
  SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,APPEND] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH ds = 10` (K ALL_TAC)
  \\ IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [APPEND,EL,HD,TL,EL_CONS]
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF,ref_static_def]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3,INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_cs_read_blast]
  \\ REPEAT (Q.PAT_X_ASSUM `(p_p * q_q) (fun2set (f_f,df_df))`
       (STRIP_ASSUME_TAC o MATCH_MP fun2set_STAR_IMP))
    \\ IMP_RES_TAC one_fun2set_IMP \\ FULL_SIMP_TAC std_ss [DIFF_UNION]
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]) |> SIMP_RULE std_ss [];

val ref_static_APPEND = store_thm("ref_static_APPEND",
  ``!xs ys a.
      ref_static a (xs ++ ys) =
      ref_static a xs * ref_static (a + n2w (8 * LENGTH xs)) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,ref_static_def,SEP_CLAUSES,LENGTH,
    WORD_ADD_0,word64_3232_def,LET_DEF,word_arith_lemma1,MULT_CLAUSES,STAR_ASSOC]);

val UPDATE_NTH_CONS = store_thm("UPDATE_NTH_CONS",
  ``UPDATE_NTH n x (y::ys) = if n = 0 then x::ys else y::UPDATE_NTH (n-1) x ys``,
  Cases_on `n` \\ SIMP_TAC std_ss [UPDATE_NTH_def,ADD1]);

val lisp_inv_cs_write = prove(
  ``^LISP ==>
   (let f = ((sp - n2w (192 - 8 * 9)) =+ w2w (w:word64))
              (((sp - n2w (188 - 8 * 9)) =+ w2w (w >>> 32)) f) in
    let cs = UPDATE_NTH 9 w cs in ^LISP) /\
   (let f = ((sp - n2w (192 - 8 * 8)) =+ w2w (w:word64))
              (((sp - n2w (188 - 8 * 8)) =+ w2w (w >>> 32)) f) in
    let cs = UPDATE_NTH 8 w cs in ^LISP) /\
   (let f = ((sp - n2w (192 - 8 * 7)) =+ w2w (w:word64))
              (((sp - n2w (188 - 8 * 7)) =+ w2w (w >>> 32)) f) in
    let cs = UPDATE_NTH 7 w cs in ^LISP) /\
   (let f = ((sp - n2w (192 - 8 * 6)) =+ w2w (w:word64))
              (((sp - n2w (188 - 8 * 6)) =+ w2w (w >>> 32)) f) in
    let cs = UPDATE_NTH 6 w cs in ^LISP) /\
   (let f = ((sp - n2w (192 - 8 * 5)) =+ w2w (w:word64))
              (((sp - n2w (188 - 8 * 5)) =+ w2w (w >>> 32)) f) in
    let cs = UPDATE_NTH 5 w cs in ^LISP) /\
   (let f = ((sp - n2w (192 - 8 * 3)) =+ w2w (w:word64))
              (((sp - n2w (188 - 8 * 3)) =+ w2w (w >>> 32)) f) in
    let cs = UPDATE_NTH 3 w cs in ^LISP)``,
  SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,APPEND] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH ds = 10` MP_TAC
  \\ IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [APPEND,EL,HD,TL,EL_CONS]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_CONS,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF,
        ref_static_def,ref_static_APPEND]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3,INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,EL_CONS]
  \\ SEP_WRITE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_ds_read = prove(
  ``^LISP ==>
    (w2w (f (sp - n2w (108 - 8 * 0))) << 32 !! w2w (f (sp - n2w (112 - 8 * 0))) = EL 0 ds) /\
    (sp - n2w (108 - 8 * 0)) IN df /\ (sp - n2w (112 - 8 * 0)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 1))) << 32 !! w2w (f (sp - n2w (112 - 8 * 1))) = EL 1 ds) /\
    (sp - n2w (108 - 8 * 1)) IN df /\ (sp - n2w (112 - 8 * 1)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 2))) << 32 !! w2w (f (sp - n2w (112 - 8 * 2))) = EL 2 ds) /\
    (sp - n2w (108 - 8 * 2)) IN df /\ (sp - n2w (112 - 8 * 2)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 3))) << 32 !! w2w (f (sp - n2w (112 - 8 * 3))) = EL 3 ds) /\
    (sp - n2w (108 - 8 * 3)) IN df /\ (sp - n2w (112 - 8 * 3)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 4))) << 32 !! w2w (f (sp - n2w (112 - 8 * 4))) = EL 4 ds) /\
    (sp - n2w (108 - 8 * 4)) IN df /\ (sp - n2w (112 - 8 * 4)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 5))) << 32 !! w2w (f (sp - n2w (112 - 8 * 5))) = EL 5 ds) /\
    (sp - n2w (108 - 8 * 5)) IN df /\ (sp - n2w (112 - 8 * 5)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 6))) << 32 !! w2w (f (sp - n2w (112 - 8 * 6))) = EL 6 ds) /\
    (sp - n2w (108 - 8 * 6)) IN df /\ (sp - n2w (112 - 8 * 6)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 7))) << 32 !! w2w (f (sp - n2w (112 - 8 * 7))) = EL 7 ds) /\
    (sp - n2w (108 - 8 * 7)) IN df /\ (sp - n2w (112 - 8 * 7)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 8))) << 32 !! w2w (f (sp - n2w (112 - 8 * 8))) = EL 8 ds) /\
    (sp - n2w (108 - 8 * 8)) IN df /\ (sp - n2w (112 - 8 * 8)) IN df /\
    (w2w (f (sp - n2w (108 - 8 * 9))) << 32 !! w2w (f (sp - n2w (112 - 8 * 9))) = EL 9 ds) /\
    (sp - n2w (108 - 8 * 9)) IN df /\ (sp - n2w (112 - 8 * 9)) IN df``,
  SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,APPEND] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH cs = 10` MP_TAC
  \\ IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [APPEND,EL,HD,TL,EL_CONS]
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF,
        ref_static_def,ref_static_APPEND] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3,INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_cs_read_blast]
  \\ Q.PAT_X_ASSUM `c1 = xxx` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `n2w amnt = c9` (K ALL_TAC)
  \\ REPEAT (Q.PAT_X_ASSUM `(p_p * q_q) (fun2set (f_f,df_df))`
       (STRIP_ASSUME_TAC o MATCH_MP fun2set_STAR_IMP))
    \\ IMP_RES_TAC one_fun2set_IMP \\ FULL_SIMP_TAC std_ss [DIFF_UNION]
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]) |> SIMP_RULE std_ss [];

val EL_LEMMA = prove(
  ``!x0 x1 x2 x3 x4 zs.
      (EL 1 (x0::x1::zs) = x1) /\
      (EL 2 (x0::x1::x2::zs) = x2) /\
      (EL 3 (x0::x1::x2::x3::zs) = x3) /\
      (EL 4 (x0::x1::x2::x3::x4::zs) = x4)``,
  EVAL_TAC \\ SIMP_TAC std_ss []);

val lisp_inv_ds_write = prove(
  ``^LISP ==>
   (let f = ((sp - n2w (112 - 8 * 0)) =+ w2w (w:word64))
              (((sp - n2w (108 - 8 * 0)) =+ w2w (w >>> 32)) f) in
    let ds = UPDATE_NTH 0 w ds in ^LISP) /\
   (let f = ((sp - n2w (108 - 8 * 0)) =+ w2w (w >>> 32))
              (((sp - n2w (112 - 8 * 0)) =+ w2w (w:word64)) f) in
    let ds = UPDATE_NTH 0 w ds in ^LISP)``,
  SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,APPEND] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH cs = 10` MP_TAC
  \\ IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [APPEND,EL,HD,TL,EL_CONS]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_CONS,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF,
        ref_static_def,ref_static_APPEND]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3,INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,EL_LEMMA,EL_CONS]
  \\ NTAC 7 (POP_ASSUM MP_TAC) \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ SEP_WRITE_TAC)
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_cs_read",lisp_inv_cs_read);
val _ = save_thm("lisp_inv_ds_read",lisp_inv_ds_read);
val _ = save_thm("lisp_inv_cs_write",lisp_inv_cs_write);
val _ = save_thm("lisp_inv_ds_write",lisp_inv_ds_write);




(* gc is a no-op *)

val memory_ok_EMP = prove(
  ``memory_ok (\x. H_EMP)``,
  SIMP_TAC (srw_ss()) [memory_ok_def]);

val gc_addr_lemma1 = prove(
  ``!w. ((w2w ((w:word64) && 3w) = 0w:word32) = (w && 3w = 0w)) /\
        ((w - 4w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 8w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 12w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 16w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 20w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 24w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 0x34w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 0x38w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 0x3Cw && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 0x40w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 232w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 236w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 228w && 3w = 0w) = (w && 3w = 0w)) /\
        ((w - 240w && 3w = 0w) = (w && 3w = 0w)) /\
        (((v + 4w * w) && 3w = 0w) = (v && 3w = 0w))``,
  REPEAT STRIP_TAC \\ blastLib.BBLAST_TAC);

val gc_addr_lemma = prove(
  ``((sp + 0x4w * wsp - 0x18w && 0x3w = 0x0w:word64)) = (sp && 3w = 0w)``,
  SIMP_TAC std_ss [gc_addr_lemma1]);

val LENGTH_ADDR_MAP = prove(
  ``!xs. LENGTH (ADDR_MAP f xs) = LENGTH xs``,
  Induct \\ REPEAT Cases \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def,LENGTH]);

val EVERY_IMP_EVERY = prove(
  ``(LENGTH xs = LENGTH ys) /\ (LENGTH zs = LENGTH xs) /\ (LENGTH zs = LENGTH ys) /\
    (!k. k < LENGTH xs ==> P (EL k xs,EL k zs) ==> Q (EL k ys,EL k zs)) ==>
    ((EVERY P (ZIP(xs,zs))) ==> (EVERY Q (ZIP(ys,zs))))``,
  FULL_SIMP_TAC std_ss [EVERY_EL,LENGTH_ZIP,EL_ZIP]);

val lisp_inv_gc_blast = prove(
  ``!w v. (w2w w = (w2w v):word64) = (w = v:word32)``,
  blastLib.BBLAST_TAC);

val STATIC = find_term (can (match_term ``ref_static x y``))
  (concl (RW [ref_full_stack_def] lisp_inv_def))

val STATIC2 = subst [``bp2:word64``|->``bp:word64``] STATIC;

val lisp_inv_gc = prove(
  ``^LISP ==>
    ?wsp' w0' w1' w2' w3' w4' w5' wi' we' f'.
      mc_full_gc_pre (wsp,bp,sp,w2w w0,w2w w1,w2w w2,w2w w3,w2w w4,w2w w5,wi,df,f) /\
      (mc_full_gc (wsp,bp,sp,w2w w0,w2w w1,w2w w2,w2w w3,w2w w4,w2w w5,wi,df,f) =
                  (wsp',bp2,sp,w2w w0',w2w w1',w2w w2',w2w w3',w2w w4',w2w w5',wi',we',df,f')) /\
      let (wsp,bp,w0,w1,w2,w3,w4,w5,wi,we,f,bp2) =
          (wsp',bp2,w0',w1',w2',w3',w4',w5',wi',we',f',bp) in
        ^LISP``,
  STRIP_TAC
  \\ SIMP_TAC std_ss [mc_full_gc_def,mc_full_gc_pre_def,gc_w2w_lemma]
  \\ POP_ASSUM (MP_TAC o RW [lisp_inv_def,ref_full_stack_def]) \\ STRIP_TAC
  \\ `w2w (f (sp - 228w)) << 32 !! w2w (f (sp - 232w)) = bp2` by
   (NTAC 3 (POP_ASSUM MP_TAC) \\ SIMP_TAC std_ss [APPEND]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def]) \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3]
    \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma])
  \\ ASM_SIMP_TAC std_ss [LET_DEF,word_arith_lemma3]
  \\ Q.ABBREV_TAC `f5 = (0x4w * wsp + sp - 0x4w =+ w5)
           ((0x4w * wsp + sp - 0x8w =+ w4)
              ((0x4w * wsp + sp - 0xCw =+ w3)
                 ((0x4w * wsp + sp - 0x10w =+ w2)
                    ((0x4w * wsp + sp - 0x14w =+ w1)
                       ((0x4w * wsp + sp - 0x18w =+ w0) f)))))`
  \\ SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,GSYM CONJ_ASSOC]
  \\ `(ref_mem bp m 0 e * ref_mem bp2 (\x. H_EMP) 0 e *
       ref_stack (sp + 0x4w * wsp - 0x18w) (s0::s1::s2::s3::s4::s5::ss++ss1) *
       ref_stack_space (sp + 0x4w * wsp - 0x18w) (w2n wsp) *
       ref_stack_space_above (sp + 4w * wsp + n2w (4 * LENGTH (ss ++ ss1)))
           (sl1 - LENGTH ss1) * ^STATIC) (fun2set (f5,df)) /\
       0x4w * wsp + sp - 0x18w IN df /\
       0x4w * wsp + sp - 0x14w IN df /\
       0x4w * wsp + sp - 0x10w IN df /\
       0x4w * wsp + sp - 0xCw IN df /\
       0x4w * wsp + sp - 0x8w IN df /\
       0x4w * wsp + sp - 0x4w IN df` by
   (Q.PAT_X_ASSUM `MAP ref_heap_addr xxx = yyy` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,ref_stack_def,word_arith_lemma1,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,STAR_ASSOC]
    \\ Q.UNABBREV_TAC `f5`
    \\ FULL_SIMP_TAC bool_ss [DECIDE ``n+6 = SUC (SUC (SUC (SUC (SUC (SUC n)))))``]
    \\ FULL_SIMP_TAC std_ss [ref_stack_space_def,word_arith_lemma1,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_EXISTS_THM,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL mc_gc_thm)
  \\ SEP_I_TAC "mc_gc"
  \\ FULL_SIMP_TAC std_ss [ok_split_heap]
  \\ IMP_RES_TAC split_gc_thm
  \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Q.PAT_X_ASSUM `split_gc xxx = yyy` MP_TAC
  \\ SEP_I_TAC "split_gc"
  \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `!xs2. bbb` MP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `XX = ref_stack_space_above (sp + 4w * wsp + n2w (4 * LENGTH (ss ++ ss1))) (sl1 - LENGTH ss1)`
  \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `^STATIC * ref_stack_space (sp + 0x4w * wsp - 0x18w) (w2n wsp) * XX`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_ASSOC WORD_ADD_COMM,memory_ok_EMP,APPEND]
  \\ FULL_SIMP_TAC std_ss [gc_addr_lemma] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ SIMP_TAC std_ss [gc_w2w_lemma]
  \\ Q.ABBREV_TAC `fj = (sp - 228w =+ w2w (bp >>> 32)) ((sp - 232w =+ w2w bp) fi)`
  \\ `(ref_mem bp2 m2 0 e * ref_mem bp (\x. H_EMP) 0 e *
       ref_stack (sp + 0x4w * wsp - 0x18w) roots2 *
       ref_stack_space (sp + 0x4w * wsp - 0x18w) (w2n wsp) * XX *
       ^STATIC2) (fun2set (fj,df))` by
   (FULL_SIMP_TAC std_ss [ref_static_def,word64_3232_def,LET_DEF,STAR_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,SEP_CLAUSES]
    \\ Q.UNABBREV_TAC `fj` \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [lisp_inv_gc_blast]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
   (Q.PAT_X_ASSUM `xxx (fun2set (f5,df))` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `xxx (fun2set (fi,df))` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` (K ALL_TAC)
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def])
    \\ FULL_SIMP_TAC std_ss [word64_3232_def,LET_DEF,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3] \\ STRIP_TAC \\ SEP_R_TAC
    \\ ASM_SIMP_TAC std_ss [gc_addr_lemma1])
  \\ `w2w (fj (sp - 236w)) << 32 !! w2w (fj (sp - 240w)) = (n2w e):word64` by
   (Q.PAT_X_ASSUM `xxx (fun2set (f5,df))` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `xxx (fun2set (fi,df))` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` (K ALL_TAC)
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def])
    \\ FULL_SIMP_TAC std_ss [word64_3232_def,LET_DEF,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3] \\ STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma])
  \\ ASM_SIMP_TAC std_ss []
  \\ `LENGTH roots2 = LENGTH (s0::s1::s2::s3::s4::s5::(ss++ss1))` by
    (FULL_SIMP_TAC std_ss [gc_exec_def,gc_copy_def,gc_filter_def,LENGTH_ADDR_MAP])
  \\ `?r0 r1 r2 r3 r4 r5 rs. roots2 = r0::r1::r2::r3::r4::r5::rs` by
    (Cases_on `roots2` THEN1 FULL_SIMP_TAC std_ss [LENGTH,ADD1]
     \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ FULL_SIMP_TAC std_ss [CONS_11])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f5,df))` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `xxx (fun2set (fi,df))` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `Abbrev (xxx = (zz =+ yy) ff)` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `Abbrev (xxx = (zz =+ yy) ff)` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [ref_stack_def,word_arith_lemma3,STAR_ASSOC]
  \\ `fj (sp + 0x4w * wsp - 0x18w) = ref_heap_addr r0` by SEP_READ_TAC
  \\ `fj (sp + 0x4w * wsp - 0x14w) = ref_heap_addr r1` by SEP_READ_TAC
  \\ `fj (sp + 0x4w * wsp - 0x10w) = ref_heap_addr r2` by SEP_READ_TAC
  \\ `fj (sp + 0x4w * wsp - 0xCw) = ref_heap_addr r3` by SEP_READ_TAC
  \\ `fj (sp + 0x4w * wsp - 0x8w) = ref_heap_addr r4` by SEP_READ_TAC
  \\ `fj (sp + 0x4w * wsp - 0x4w) = ref_heap_addr r5` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ `(ref_mem bp2 m2 0 e * ref_mem bp (\x. H_EMP) 0 e *
       ref_stack (sp + 0x4w * wsp) rs *
       ref_stack_space (sp + 0x4w * wsp) (w2n wsp + 6) * XX *
       ^STATIC2) (fun2set (fj,df))` by
   (FULL_SIMP_TAC bool_ss [DECIDE ``n+6 = SUC (SUC (SUC (SUC (SUC (SUC n)))))``]
    \\ FULL_SIMP_TAC std_ss [ref_stack_space_def,word_arith_lemma1,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_EXISTS_THM,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`ref_heap_addr r5`,`ref_heap_addr r4`,`ref_heap_addr r3`,
                          `ref_heap_addr r2`,`ref_heap_addr r1`,`ref_heap_addr r0`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ SIMP_TAC std_ss [lisp_inv_def]
  \\ Q.LIST_EXISTS_TAC [`r0`,`r1`,`r2`,`r3`,`r4`,`r5`]
  \\ Q.LIST_EXISTS_TAC [`m2`,`i2`,`TAKE (LENGTH ss) rs`,`DROP (LENGTH ss) rs`,`sym`,`~b`]
  \\ ASM_SIMP_TAC std_ss [MAP,APPEND,ref_full_stack_def,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH,TAKE_DROP]
  \\ `ok_split_heap (r0::r1::r2::r3::r4::r5::rs,m2,i2,e)` by
    (FULL_SIMP_TAC std_ss [ok_split_heap] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH_APPEND]
  \\ `LENGTH ss <= LENGTH rs` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_TAKE,LENGTH_DROP]
  \\ Q.UNABBREV_TAC `XX` \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ REVERSE STRIP_TAC
  THEN1 (Cases_on `b` \\ FULL_SIMP_TAC std_ss [])
  \\ `i2 <= e` by (FULL_SIMP_TAC std_ss [ok_split_heap_def])
  \\ ASM_SIMP_TAC std_ss [word_add_n2w,DECIDE ``2*n = n+n:num``]
  \\ Q.PAT_X_ASSUM `EVERY xxx yyy` MP_TAC
  \\ SIMP_TAC std_ss [GSYM ZIP]
  \\ MATCH_MP_TAC EVERY_IMP_EVERY
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
  \\ NTAC 2 STRIP_TAC
  \\ MATCH_MP_TAC (Q.INST [`c2`|->`T`] lisp_x_gc_thm)
  \\ ASM_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [LET_DEF];

(* -- generational version

val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64)) /\
                       ((a + w && 3w = 0w) = (w && 3w = 0w:word64))``

val lisp_inv_gc = prove(
  ``^LISP ==>
    ?wsp' w0' w1' w2' w3' w4' w5' wi' we' f'.
      mc_full_gc_pre (tw0,wsp,bp,sp,w2w w0,w2w w1,w2w w2,w2w w3,w2w w4,w2w w5,wi,df,f) /\
      (mc_full_gc (tw0,wsp,bp,sp,w2w w0,w2w w1,w2w w2,w2w w3,w2w w4,w2w w5,wi,df,f) =
                  (tw0,wsp',bp,sp,w2w w0',w2w w1',w2w w2',w2w w3',w2w w4',w2w w5',wi',we',df,f')) /\
      let (wsp,w0,w1,w2,w3,w4,w5,wi,we,f) =
          (wsp',w0',w1',w2',w3',w4',w5',wi',we',f') in
        ^LISP``,
  STRIP_TAC
  \\ STRIP_ASSUME_TAC (split_after (3*5) (CONJUNCTS (UNDISCH lisp_inv_ds_read)) |> snd |>
              split_after 3 |> fst |> LIST_CONJ)
  \\ SIMP_TAC std_ss [mc_full_gc_def,mc_full_gc_pre_def,gc_w2w_lemma]
  \\ NTAC 3 (POP_ASSUM MP_TAC)
  \\ POP_ASSUM (MP_TAC o RW [lisp_inv_def,ref_full_stack_def]) \\ STRIP_TAC
  \\ `w2w (f (sp - 228w)) << 32 !! w2w (f (sp - 232w)) = bp2` by
   (NTAC 3 (POP_ASSUM MP_TAC) \\ SIMP_TAC std_ss [APPEND]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def]) \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,word64_3232_def,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma3]
    \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma])
  \\ ASM_SIMP_TAC std_ss [LET_DEF,word_arith_lemma3]
  \\ Q.ABBREV_TAC `f5 = (0x4w * wsp + sp - 0x4w =+ w5)
           ((0x4w * wsp + sp - 0x8w =+ w4)
              ((0x4w * wsp + sp - 0xCw =+ w3)
                 ((0x4w * wsp + sp - 0x10w =+ w2)
                    ((0x4w * wsp + sp - 0x14w =+ w1)
                       ((0x4w * wsp + sp - 0x18w =+ w0) f)))))`
  \\ SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,GSYM CONJ_ASSOC]
  \\ `(ref_mem bp m 0 e * ref_mem bp2 (\x. H_EMP) 0 e *
       ref_stack (sp + 0x4w * wsp - 0x18w) (s0::s1::s2::s3::s4::s5::ss++ss1) *
       ref_stack_space (sp + 0x4w * wsp - 0x18w) (w2n wsp) *
       ref_stack_space_above (sp + 4w * wsp + n2w (4 * LENGTH (ss ++ ss1)))
           (sl1 - LENGTH ss1) * ^STATIC) (fun2set (f5,df)) /\
       0x4w * wsp + sp - 0x18w IN df /\
       0x4w * wsp + sp - 0x14w IN df /\
       0x4w * wsp + sp - 0x10w IN df /\
       0x4w * wsp + sp - 0xCw IN df /\
       0x4w * wsp + sp - 0x8w IN df /\
       0x4w * wsp + sp - 0x4w IN df` by
   (Q.PAT_X_ASSUM `MAP ref_heap_addr xxx = yyy` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,ref_stack_def,word_arith_lemma1,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,STAR_ASSOC]
    \\ Q.UNABBREV_TAC `f5`
    \\ FULL_SIMP_TAC bool_ss [DECIDE ``n+6 = SUC (SUC (SUC (SUC (SUC (SUC n)))))``]
    \\ FULL_SIMP_TAC std_ss [ref_stack_space_def,word_arith_lemma1,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_EXISTS_THM,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL mc_gen_gc_thm)
  \\ `?l. (EL 5 ds = n2w l) /\ l <= e` by
       (Cases_on `EL 5 ds` \\ FULL_SIMP_TAC wstd_ss [w2n_n2w] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,DECIDE ``l+l=2*l:num``]
  \\ SEP_I_TAC "mc_gen_gc"
  \\ FULL_SIMP_TAC std_ss [ok_split_heap]
  \\ IMP_RES_TAC gen_gc_thm
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `l`)
  \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Q.PAT_X_ASSUM `gen_gc xxx = yyy` MP_TAC
  \\ SEP_I_TAC "gen_gc"
  \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `!xs2. bbb` MP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `XX = ref_stack_space_above (sp + 4w * wsp + n2w (4 * LENGTH (ss ++ ss1))) (sl1 - LENGTH ss1)`
  \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `^STATIC * ref_stack_space (sp + 0x4w * wsp - 0x18w) (w2n wsp) * XX`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_ASSOC WORD_ADD_COMM,memory_ok_EMP,APPEND]
  \\ FULL_SIMP_TAC std_ss [gc_addr_lemma] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ SIMP_TAC std_ss [gc_w2w_lemma]
  \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [lisp_inv_gc_blast]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
   (Q.PAT_X_ASSUM `xxx (fun2set (f5,df))` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` (K ALL_TAC)
    \\ NTAC 4 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def])
    \\ FULL_SIMP_TAC std_ss [word64_3232_def,LET_DEF,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3] \\ NTAC 4 STRIP_TAC \\ SEP_R_TAC
    \\ ASM_SIMP_TAC std_ss [gc_addr_lemma1,align_blast]
    \\ ASM_SIMP_TAC std_ss [n2w_and_3])
  \\ `w2w (fi (sp - 236w)) << 32 !! w2w (fi (sp - 240w)) = (n2w e):word64` by
   (Q.PAT_X_ASSUM `xxx (fun2set (f5,df))` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` (K ALL_TAC)
    \\ NTAC 4 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def])
    \\ FULL_SIMP_TAC std_ss [word64_3232_def,LET_DEF,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3] \\ STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma])
  \\ ASM_SIMP_TAC std_ss []
  \\ `LENGTH roots2 = LENGTH (s0::s1::s2::s3::s4::s5::(ss++ss1))` by
    (FULL_SIMP_TAC std_ss [weak_gc_exec_def] \\ Cases_on `z`
     \\ FULL_SIMP_TAC std_ss [weak_gc_copy_def,weak_gc_filter_def,LENGTH_ADDR_MAP])
  \\ `?r0 r1 r2 r3 r4 r5 rs. roots2 = r0::r1::r2::r3::r4::r5::rs` by
    (Cases_on `roots2` THEN1 FULL_SIMP_TAC std_ss [LENGTH,ADD1]
     \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
     \\ FULL_SIMP_TAC std_ss [CONS_11])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f5,df))` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `Abbrev (xxx = (zz =+ yy) ff)` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [ref_stack_def,word_arith_lemma3,STAR_ASSOC]
  \\ `fi (sp + 0x4w * wsp - 0x18w) = ref_heap_addr r0` by SEP_READ_TAC
  \\ `fi (sp + 0x4w * wsp - 0x14w) = ref_heap_addr r1` by SEP_READ_TAC
  \\ `fi (sp + 0x4w * wsp - 0x10w) = ref_heap_addr r2` by SEP_READ_TAC
  \\ `fi (sp + 0x4w * wsp - 0xCw) = ref_heap_addr r3` by SEP_READ_TAC
  \\ `fi (sp + 0x4w * wsp - 0x8w) = ref_heap_addr r4` by SEP_READ_TAC
  \\ `fi (sp + 0x4w * wsp - 0x4w) = ref_heap_addr r5` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ `(ref_mem bp m2 0 e * ref_mem bp2 (\x. H_EMP) 0 e *
       ref_stack (sp + 0x4w * wsp) rs *
       ref_stack_space (sp + 0x4w * wsp) (w2n wsp + 6) * XX *
       ^STATIC) (fun2set (fi,df))` by
   (FULL_SIMP_TAC bool_ss [DECIDE ``n+6 = SUC (SUC (SUC (SUC (SUC (SUC n)))))``]
    \\ FULL_SIMP_TAC std_ss [ref_stack_space_def,word_arith_lemma1,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_EXISTS_THM,WORD_ADD_0]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`ref_heap_addr r5`,`ref_heap_addr r4`,`ref_heap_addr r3`,
                          `ref_heap_addr r2`,`ref_heap_addr r1`,`ref_heap_addr r0`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [APPEND])
  \\ SIMP_TAC std_ss [lisp_inv_def]
  \\ Q.LIST_EXISTS_TAC [`r0`,`r1`,`r2`,`r3`,`r4`,`r5`]
  \\ Q.LIST_EXISTS_TAC [`m2`,`i2`,`TAKE (LENGTH ss) rs`,`DROP (LENGTH ss) rs`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [MAP,APPEND,ref_full_stack_def,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH,TAKE_DROP]
  \\ `ok_split_heap (r0::r1::r2::r3::r4::r5::rs,m2,i2,e)` by
    (FULL_SIMP_TAC std_ss [ok_split_heap] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH_APPEND]
  \\ `LENGTH ss <= LENGTH rs` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_TAKE,LENGTH_DROP]
  \\ Q.UNABBREV_TAC `XX` \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ `i2 <= e` by (FULL_SIMP_TAC std_ss [ok_split_heap_def])
  \\ ASM_SIMP_TAC std_ss [word_add_n2w,DECIDE ``2*n = n+n:num``]
  \\ Q.PAT_X_ASSUM `EVERY xxx yyy` MP_TAC
  \\ SIMP_TAC std_ss [GSYM ZIP]
  \\ MATCH_MP_TAC EVERY_IMP_EVERY
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
  \\ NTAC 2 STRIP_TAC
  \\ MATCH_MP_TAC (Q.INST [`c2`|->`T`] lisp_x_gc_thm)
  \\ ASM_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [LET_DEF];

*)


val _ = save_thm("lisp_inv_gc",lisp_inv_gc);


(* temp string *)

val lisp_inv_temp_string = prove(
  ``!n str2.
        ^LISP ==> n <= 520 ==>
        ?str p. (LENGTH str = n) /\
                ((one_byte_list sa2 str * p) (fun2set (g,dg))) /\
                !g2. ((one_byte_list sa2 str2 * p) (fun2set (g2,dg))) /\
                     (LENGTH str2 = n) ==> let g = g2 in ^LISP``,
  STRIP_TAC \\ STRIP_TAC
  \\ SIMP_TAC std_ss [lisp_inv_def,symtable_inv_def,one_symbol_list_def,
    SEP_EXISTS_THM,cond_STAR] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND]
  \\ `n <= LENGTH ys` by DECIDE_TAC
  \\ MP_TAC (Q.SPEC `n` (Q.ISPEC `ys:word8 list` SPLIT_LIST_LESS_EQ))
  \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND]
  \\ Q.EXISTS_TAC `xs1'` \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `one_byte_list sa1 (symbol_list (INIT_SYMBOLS ++ sym)) *
        one_byte_list
           (sa1 + n2w (LENGTH (symbol_list (INIT_SYMBOLS ++ sym))) +
            n2w n) xs2`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `str2 ++ xs2`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LET_DEF,one_byte_list_APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_temp_string",lisp_inv_temp_string);


(* load value of amnt *)

val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64))``

val lisp_inv_amnt_read = prove(
  ``^LISP ==>
    (let (x0,w0) = (Val amnt, w2w (4w * (w2w (f (sp - 0x24w)) << 32 !! (w2w:word32->word64) (f (sp - 0x28w))) + 1w)) in ^LISP) /\
    (sp - 0x24w) IN df /\ (sp - 0x28w) IN df /\
    (sp - 0x24w && 3w = 0w) /\ (sp - 0x28w && 3w = 0w)``,
  SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC \\ IMP_RES_TAC lisp_inv_ds_read
  \\ `sp && 3w = 0w`by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ `(EL 9 ds = n2w amnt) /\ amnt < 2**30` by (FULL_SIMP_TAC std_ss [lisp_inv_def])
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [w2w_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ `(4 * amnt + 1) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ MATCH_MP_TAC lisp_inv_Val_n2w \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_amnt_read",lisp_inv_amnt_read);


(* load based on xbp *)

val BLAST_LEMMA = prove(``w << 2 !! 1w = w << 2 + 1w:word32``,blastLib.BBLAST_TAC);

val lisp_inv_xbp_load = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 < xbp /\ xbp <= LENGTH xs ==>
    let wa = (w2w (f (sp - n2w (108 - 8 * 1))) << 32 !! w2w (f (sp - n2w (112 - 8 * 1)))) in
    let wb = wa + w2w w1 in
    (let (x4,w4,tw2) = (EL ((LENGTH xs + getVal x1) - xbp) xs,f wb,wa) in ^LISP) /\
    wb IN df /\ (wb && 0x3w = 0x0w) /\
    (sp - n2w (108 - 8 * 1)) IN df /\ ((sp - n2w (108 - 8 * 1) && 3w = 0w)) /\
    (sp - n2w (112 - 8 * 1)) IN df /\ ((sp - n2w (112 - 8 * 1) && 3w = 0w))``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `lisp_inv xxx yyy zzz` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC
  \\ Q.ABBREV_TAC `n = LENGTH xs + a - xbp`
  \\ `EL 1 ds + w2w w1 = sp + 0x4w * wsp + 0x4w * n2w n` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
    \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,BLAST_LEMMA]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL]
    \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_ADD,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma3]
    \\ Q.PAT_X_ASSUM `LENGTH ss + w2n wsp = sl` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`wsp`,`w`)
    \\ Cases \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,w2n_n2w]
    \\ `~(4 * (LENGTH ss + n') < 4 * xbp - 4 * a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < LENGTH xs` by (Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ IMP_RES_TAC lisp_inv_swap4
  \\ IMP_RES_TAC (RW[AND_IMP_INTRO]lisp_inv_load_lemma)
  \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC lisp_inv_swap4
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];


(* store based on xbp *)

val lisp_inv_xbp_store = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 < xbp /\ xbp <= LENGTH xs ==>
    let wa = (w2w (f (sp - n2w (108 - 8 * 1))) << 32 !! w2w (f (sp - n2w (112 - 8 * 1)))) in
    let wb = wa + w2w w1 in
    (let (xs,f,tw2) = (UPDATE_NTH ((LENGTH xs + getVal x1) - xbp) x0 xs,(wb =+ w0) f,wa) in ^LISP) /\
    wb IN df /\ (wb && 0x3w = 0x0w) /\
    (sp - n2w (108 - 8 * 1)) IN df /\ ((sp - n2w (108 - 8 * 1) && 3w = 0w)) /\
    (sp - n2w (112 - 8 * 1)) IN df /\ ((sp - n2w (112 - 8 * 1) && 3w = 0w))``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `lisp_inv xxx yyy zzz` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC
  \\ Q.ABBREV_TAC `n = LENGTH xs + a - xbp`
  \\ `EL 1 ds + w2w w1 = sp + 0x4w * wsp + 0x4w * n2w n` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
    \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,BLAST_LEMMA]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL]
    \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_ADD,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma3]
    \\ Q.PAT_X_ASSUM `LENGTH ss + w2n wsp = sl` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`wsp`,`w`)
    \\ Cases \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,w2n_n2w]
    \\ `~(4 * (LENGTH ss + n') < 4 * xbp - 4 * a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < LENGTH xs` by (Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ IMP_RES_TAC (RW[AND_IMP_INTRO]lisp_inv_store_lemma)
  \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];


(* code heap add symbol *)

val MEM_LIST_FIND_LEMMA = prove(
  ``!sym s k x. MEM s sym ==> (LIST_FIND k s (sym ++ [x]) = LIST_FIND k s sym)``,
  Induct \\ SIMP_TAC std_ss [MEM,APPEND,LIST_FIND_def] \\ METIS_TAC []);

val bc_symbols_ok_IMP = prove(
  ``!bs sym s k.
       bc_symbols_ok sym bs ==>
       bc_symbols_ok (sym ++ [s]) bs /\
       (bs2bytes (k,sym ++ [s]) bs = bs2bytes (k,sym) bs)``,
  Induct \\ SIMP_TAC std_ss [bc_symbols_ok_def,bs2bytes_def] \\ Cases_on `h`
  \\ REPEAT (Cases_on `l`)
  \\ ASM_SIMP_TAC std_ss [bc_symbols_ok_def,bs2bytes_def,bc_ref_def,
       MEM_LIST_FIND_LEMMA,MEM_APPEND]);

val code_heap_add_symbol = store_thm("code_heap_add_symbol",
  ``code_heap code (sym,base_ptr,curr_ptr,space_left,dh,h) ==>
    code_heap code (sym ++ [s],base_ptr,curr_ptr,space_left,dh,h)``,
  Cases_on `code` \\ SIMP_TAC std_ss [code_heap_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`bs`,`hs`] \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_symbols_ok_IMP \\ ASM_SIMP_TAC std_ss []);


val _ = export_theory();
