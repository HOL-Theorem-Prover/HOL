Theory addMLdep2[bare]
Ancestors
  addMLdep1
Libs
  HolKernel Parse boolLib

fun grep s fname =
  let
    val instr = HOLFileSys.openIn fname
    fun recurse () =
      case HOLFileSys.inputLine instr of
          NONE => false
        | SOME line => String.isSubstring s line orelse recurse ()
  in
    recurse() before HOLFileSys.closeIn instr
  end

val _ = if grep "MLdepLib" "addMLdep1Theory.sml" then ()
        else OS.Process.exit OS.Process.failure

Theorem thm2 = TRUTH;
