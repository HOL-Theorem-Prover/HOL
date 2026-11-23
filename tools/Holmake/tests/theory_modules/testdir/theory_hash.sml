(* The hash the generated FooTheory.sml of [thy] links it under, for the
   theory module test scripts *)
fun read path =
  let val input = HOLFileSys.openIn path
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end;
fun theory_hash thy =
  let
    val text = read (thy ^ "Theory.sml")
    val (_, rest) = Substring.position "hash = \"" (Substring.full text)
  in
    Substring.string
      (Substring.takel (fn c => c <> #"\"") (Substring.triml 8 rest))
  end;
