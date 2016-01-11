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
   val _ = loadPath := (Systeml.HOLDIR ++ "src/proofman") ::
                       (Systeml.HOLDIR ++ "sigobj") ::
                       (!loadPath)
   val _ = app load ["boolLib", "proofManagerLib", "Arbrat"]
               handle e => OS.Process.exit OS.Process.failure
   fun safe_use s = if String.sub (s, 0) = #"-" then () else use s
   fun main () =
     (List.app safe_use (CommandLine.arguments ())
      ; PolyML.rootFunction ())
in
   val _ = PolyML.SaveState.saveState (Systeml.HOLDIR ++ "bin/hol.state0")
end
