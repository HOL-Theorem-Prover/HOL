(* this is an -*- sml -*- file *)
(* the expectation is that this file gets fed into hol *)

local
  fun p1 ++ p2 = OS.Path.concat(p1,p2)
  fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)
in
fun mkmunge () = let
  val theories = CommandLine.arguments()
  fun load1 s = let
    val _ = print ("Loading "^s^"\n")
  in
    load s
  end handle e => (die ("Exception raised: "^General.exnMessage e))
  val _ = app load1 ("EmitTeX" :: theories)
  fun appthis s = let
    val nm = Globals.HOLDIR ++ "src" ++ "TeX" ++ s
    val _ = print ("Using "^s^"\n")
  in
    use nm
  end handle e => (die ("Exception raised: "^General.exnMessage e))
in
  List.app appthis ["mungeTools.sig", "mungeTools.sml", "munger.lex.sml",
                    "mkmunger.sml", "poly-munge.ML"]
end
end (* local *)

val _ = PolyML.export("mkmunge", mkmunge)

