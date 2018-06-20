open HolKernel Parse boolLib
open addMLdep1Theory

val _ = new_theory "addMLdep2";

fun grep s fname =
  let
    val instr = TextIO.openIn fname
    fun recurse () =
      case TextIO.inputLine instr of
          NONE => false
        | SOME line => String.isSubstring s line orelse recurse ()
  in
    recurse() before TextIO.closeIn instr
  end

val _ = if grep "MLdepLib" "addMLdep1Theory.sml" then ()
        else OS.Process.exit OS.Process.failure

val _ = save_thm("thm2", TRUTH);

val _ = export_theory();
