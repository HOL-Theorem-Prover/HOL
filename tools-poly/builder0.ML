(* this is an -*- sml -*- file *)
local
   val pd = !PolyML.Compiler.printDepth
in
   val _ = PolyML.print_depth 0
   val _ = use "poly/poly-init2.ML"
   val _ = PolyML.print_depth pd
end;

local
   infix ++
   fun p1 ++ p2 = OS.Path.concat (p1,p2)
   val target = Systeml.HOLDIR ++ "bin/hol.state0"
   val _ = loadPath := (Systeml.HOLDIR ++ "src/proofman") ::
                       (Systeml.HOLDIR ++ "sigobj") ::
                       (!loadPath)
in
   val _ = app load ["boolLib", "proofManagerLib", "Arbrat"]
               handle e => OS.Process.exit OS.Process.failure
end;

val _ = let
  infix ++
  val op ++ = OS.Path.concat
  fun hol_use p s =
    let
      val nm = Systeml.HOLDIR ++ p ++ s
    in
      use (nm ^ ".sig")
    ; use (nm ^ ".sml")
    end
in
  List.app (hol_use ("tools" ++ "Holmake"))
           ["regexpMatch", "parse_glob", "internal_functions",
            "Holdep_tokens", "Holdep", "Holmake_tools", "Holmake_types",
            "ReadHMF"]
end;


local
   val rebuild_heaps_var = Systeml.build_after_reloc_envvar
   infix ++
   fun p1 ++ p2 = OS.Path.concat (p1,p2)
   val target = Systeml.HOLDIR ++ "bin/hol.state0"
   val _ = loadPath := (Systeml.HOLDIR ++ "src/proofman") ::
                       (Systeml.HOLDIR ++ "sigobj") ::
                       (!loadPath)
   fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
                OS.Process.exit OS.Process.failure)


   fun maxModTime (fname,maxt) =
     Portable.time_max(maxt, OS.FileSys.modTime fname)
      handle OS.SysErr(s, _) =>
       die ("OS error while reading mod-time of "^ fname^": "^s)

   val maxModTimel = List.foldl maxModTime Time.zeroTime
   fun sigobjify s = Systeml.HOLDIR ++ "sigobj" ++ (s ^ ".uo")
   val deps = [sigobjify "boolLib", sigobjify "Arbrat", sigobjify "Parse",
               sigobjify "term_pp",
               Systeml.HOLDIR ++ "src/proofman/proofManagerLib.uo"]

   fun safe_use s = if String.sub (s, 0) = #"-" then () else use s
   fun main () =
     (List.app safe_use (CommandLine.arguments ())
      ; PolyML.rootFunction ())
   fun adjust_timestamp() =
     OS.FileSys.setTime (target, SOME (maxModTimel deps))
      handle OS.SysErr(s, _) => die ("OS error while adjusting time stamp: "^s)
in
   val _ = PolyML.SaveState.saveState target
   val _ =
       case OS.Process.getEnv rebuild_heaps_var of
           NONE => ()
         | SOME "1" => adjust_timestamp()
         | SOME s => TextIO.output(TextIO.stdErr,
                                   "Ignoring strange value (" ^ s ^ ") for " ^
                                   rebuild_heaps_var ^ "\n")
end
