structure m0_decompLib :> m0_decompLib =
struct

open HolKernel Parse boolLib bossLib
open decompilerLib m0_progLib m0_progTheory m0_decompTheory

val () = m0_progLib.set_newline ""

local
   fun get_length th =
      if sumSyntax.is_inl (m0_progLib.get_code th) then 2 else 4
   val find_exit =
      stateLib.get_pc_delta
          (Lib.equal "m0_prog$m0_PC" o fst o boolSyntax.dest_strip_comb)
   fun format_thm th = (th, get_length th, find_exit th)
   val count_INTRO_rule =
      stateLib.introduce_triple_definition (false, m0_COUNT_def) o
      Thm.INST [``endianness:bool`` |-> boolSyntax.F,
                ``spsel:bool`` |-> boolSyntax.F]
   val finalise =
      List.map format_thm o stateLib.fix_precond o List.map count_INTRO_rule
in
   val set_opt = m0_progLib.m0_config false
   fun m0_triples hex =
      case finalise (m0_progLib.m0_spec_hex hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "m0_triples" ""
   fun m0_triples_opt s hex = (set_opt s; m0_triples hex)
end

val m0_pc = Term.prim_mk_const {Thy = "m0_prog", Name = "m0_PC"}

fun m0_tools f hide = (f, fn _ => fail(), hide, m0_pc): decompiler_tools
fun m0_tools_opt opt = m0_tools (m0_triples_opt opt)

val l3_m0_tools = m0_tools m0_triples m0_NZCV_HIDE
val l3_m0_tools_no_status = m0_tools m0_triples TRUTH

val l3_m0_tools_flat = m0_tools_opt "flat" m0_NZCV_HIDE
val l3_m0_tools_array = m0_tools_opt "array" m0_NZCV_HIDE
val l3_m0_tools_mapped = m0_tools_opt "mapped" m0_NZCV_HIDE

val l3_m0_tools_flat_no_status = m0_tools_opt "flat" TRUTH
val l3_m0_tools_array_no_status = m0_tools_opt "array" TRUTH
val l3_m0_tools_mapped_no_status = m0_tools_opt "mapped" TRUTH

fun m0_decompile name qcode =
   (set_opt "mapped"; decompilerLib.decompile l3_m0_tools name qcode)

fun m0_decompile_code name (qass: string quotation) =
   ( set_opt "mapped"
   ; decompilerLib.decompile_with m0AssemblerLib.m0_code l3_m0_tools name qass
   )

(* Testing...

open m0_decompLib

(* test program *)
val q =
   `movs r1, #0              ; accumulator
    mov  r3, r0              ; first address
    adds r3, #40             ; last address (10 loads)
l1: ldr  r2, [r0, #4]        ; load data
    adds r0, #4              ; increment address
    add  r1, r2              ; add to accumulator
    cmp  r0, r3              ; test if done
    blt  l1                  ; loop if not done`

(* from GAS *)
val (test_cert, test_def) = m0_decompile "test" `
   2100
   0003
   3328
   6842
   3004
   4411
   4298
   DBFA`

(* internal assembler *)
val () = m0AssemblerLib.print_m0_code q

val (test2_cert, test2_def) = m0_decompile_code "test2" q

val () = computeLib.add_funs [test_def]
val () = computeLib.add_funs [test2_def]

EVAL ``test (12w, 0, dmem, \a. if a && 3w = 0w then 4w else 0w)``
EVAL ``test2 (12w, 0, dmem, \a. if a && 3w = 0w then 4w else 0w)``

map m0_triples
  ["b510", "680b", "2b00", "d003", "681a", "6804", "42a2", "db02",
   "6043", "6008", "bd10", "1d19", "e7f3"]

00000000 <insert>:
   0:   b510            push    {r4, lr}
   2:   680b            ldr     r3, [r1, #0]
   4:   2b00            cmp     r3, #0
   6:   d003            beq.n   10 <insert+0x10>
   8:   681a            ldr     r2, [r3, #0]
   a:   6804            ldr     r4, [r0, #0]
   c:   42a2            cmp     r2, r4
   e:   db02            blt.n   16 <insert+0x16>
  10:   6043            str     r3, [r0, #4]
  12:   6008            str     r0, [r1, #0]
  14:   bd10            pop     {r4, pc}
  16:   1d19            adds    r1, r3, #4
  18:   e7f3            b.n     2 <insert+0x2>

0000001a <sort>:
  1a:   b537            push    {r0, r1, r2, r4, r5, lr}
  1c:   1c04            adds    r4, r0, #0
  1e:   2200            movs    r2, #0
  20:   6800            ldr     r0, [r0, #0]
  22:   9201            str     r2, [sp, #4]
  24:   2800            cmp     r0, #0
  26:   d005            beq.n   34 <sort+0x1a>
  28:   6845            ldr     r5, [r0, #4]
  2a:   a901            add     r1, sp, #4
  2c:   f7ff fffe       bl      0 <insert>
  30:   1c28            adds    r0, r5, #0
  32:   e7f7            b.n     24 <sort+0xa>
  34:   9b01            ldr     r3, [sp, #4]
  36:   6023            str     r3, [r4, #0]
  38:   bd37            pop     {r0, r1, r2, r4, r5, pc}

map m0_triples ["bd10","f7ffff4e"]

*)

end
