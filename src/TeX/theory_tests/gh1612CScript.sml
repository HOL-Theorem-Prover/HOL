Theory gh1612C
Ancestors hol gh1612B

fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure)

fun goodline s =
  if String.isPrefix "\\newcommand{\\HOL" s then
    CharVector.all (fn c => c <> #"@") s
  else true

fun testFile fname =
  let
    val istrm = TextIO.openIn fname
     handle _ => die "Couldn't open file"
    fun recurse () =
      case TextIO.inputLine istrm of
        NONE => NONE before TextIO.closeIn istrm
      | SOME line => if goodline line then recurse ()
                     else SOME line
  in
    case recurse () of
      NONE => save_thm("Testpassed", TRUTH)
    | SOME l => die ("Line\n  " ^ l ^ " is bad")
  end

val _ = testFile "HOLghOneSixOneTwoA.tex"
