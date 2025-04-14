
fun main() =
    let
      open theorystats
      val (g, links) = recurse_toDirs find_theory_action (TheoryGraph.empty, []) [OS.FileSys.getDir()]
    in
      print "Keys:\n";
      List.app (println o HOLPP.pp_to_string 70 RawTheorykey.pp) (TheoryGraph.keys g)
    end handle e => theorystats.die ("Uncaught exception: " ^ General.exnMessage e)
