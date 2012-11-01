open armML

(* really, the "open" is all that's necessary: we just want to check
   that armML compiles and loads. With MoscowML, the compiler will
   check that for us; with Poly/ML we need an executable (i.e. this
   file) that will cause the load to actually happen. *)

(* But here's a trivial exercising of the armML code *)

val zero32 = wordsML.fromString32 "0"
val one32 = wordsML.fromString32 "1"
val regs0 = regs ((fn r => if r = r0 then zero32 else one32), (fn p => zero32))
(* would like to write something like:

  val state0 = arm_state (regs0, wordsML.fromString "101", ????)

but can't see how to generate a value of type exceptions.

*)

(* I have no idea what this should do. *)
val (_, shiftanswer) = SHIFT_IMMEDIATE (regs_reg regs0) usr false (wordsML.fromString12 "103")

val shiftanswer_n = wordsML.w2n shiftanswer

val _ = print ("SHIFTANSWER = " ^ numML.toString shiftanswer_n ^ "\n")
