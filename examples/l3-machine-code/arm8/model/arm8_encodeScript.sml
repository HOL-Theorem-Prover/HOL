open HolKernel boolLib bossLib
open arm8AssemblerLib
open sptreeTheory arm8Theory

val () = new_theory "arm8_encode"

(* ----------------------------------------------------------------------- *)

(*

val () = Globals.max_print_depth := 10

*)

val () = sptreeSyntax.temp_add_sptree_printer()

val sptree_mask32_def = zDefine `sptree_mask32 = ^m32`
val sptree_mask64_def = zDefine `sptree_mask64 = ^m64`

val EncodeBitMask_def = zDefine`
   (EncodeBitMask (Imm32 i) = sptree$lookup (w2n i) sptree_mask32) /\
   (EncodeBitMask (Imm64 i) = sptree$lookup (w2n i) sptree_mask64)`

val InstructionEncode_def = Define`
   InstructionEncode ast = arm8$Encode (EncodeBitMask, ast)`

val () = export_theory ()

(* ----------------------------------------------------------------------- *)

(* Testing

open sptreeSyntax wordsLib arm8_encodeTheory

val EncodeBitMask_CONV = PURE_REWRITE_CONV [EncodeBitMask_def] THENC lookup_CONV
val () = computeLib.add_convs [(``EncodeBitMask``, 1, EncodeBitMask_CONV)]

Count.apply EVAL ``EncodeBitMask (Imm32 0xFFw)``
Count.apply EVAL ``EncodeBitMask (Imm64 0xFFw)``

val () = Globals.max_print_depth := ~1

open MutableMap arm8AssemblerLib

EVAL ``size ^(arm8AssemblerLib.m32)`` (* 1302 *)
EVAL ``size ^(arm8AssemblerLib.m64)`` (* 5334 *)

*)
