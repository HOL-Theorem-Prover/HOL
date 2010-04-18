(* this is an -*- sml -*- file *)
(* the expectation is that this file gets fed into hol *)
val _ = PolyML.print_depth 0;

use "mkmkcline.sml";
local
  fun p1 ++ p2 = OS.Path.concat(p1,p2)
  fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)
in
fun mkmunge () = let
  val (exeopt,theories) = mkmkcline.read_cline()
  val exe = case exeopt of NONE => "munge.exe"
                         | SOME s => s
  val _ = load "EmitTeX"
  fun load1 s = let
    val _ = print ("Loading "^s^"\n")
  in
    load s
  end handle e => (die ("Exception raised: "^General.exnMessage e))
  val _ = load1 "holindex"
  val _ = app load1 theories
  fun appthis s = let
    val nm = Globals.HOLDIR ++ "src" ++ "TeX" ++ s
    val _ = print ("Using "^s^"\n")
  in
    use nm
  end handle e => (die ("Exception raised: "^General.exnMessage e))
  open Systeml
in
  List.app appthis ["mungeTools.sig", "mungeTools.sml", "munger.lex.sml",
                    "mkmunger.sml", "poly-munge.ML"];
  print "Linking object code\n";
  let
    val res = systeml ([CC, "-o", exe, "munger.o"] @ POLY_LDFLAGS)
  in
    if OS.Process.isSuccess res then ()
    else die "Linking of Poly/ML object code failed"
  end
end
end (* local *)

val _ = PolyML.export("mkmunge", mkmunge)

