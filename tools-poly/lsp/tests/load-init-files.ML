(* Compile the LSP's server-start files.
 *
 * `tools-poly/hol.ML' QUse's these from inside `main', so they are
 * compiled when a language server starts and by nothing else: no
 * Holmake directory owns them, and `tools-poly/lsp' has no Holmakefile
 * at all -- which is what keeps the Moscow ML build free of the LSP.
 * The cost is that a rename in `TacticParse', `DefnBase', `Preterm' or
 * `DB' breaks them silently, and stays broken until someone opens a
 * theory script.
 *
 * Loading them is the whole test: each is a structure, so compiling it
 * checks it against everything it names.  `tactic_steps.ML' also runs a
 * load-time selftest of its own, which comes along for free.
 *
 * Kept in step with `hol.ML' by hand.  A file added there and not here
 * is simply not covered; the list below is the contract.
 *
 * Run twice, because a server does: a directory whose Holmakefile names
 * a heap gets that heap, and for everything up to `src/boss' that heap
 * is `hol.state0'.  A file naming a structure that only the full heap
 * has -- `DefnBase' was one -- then takes the server down at startup,
 * in those directories only, and before it can say why.
 *)
val bare = List.exists (fn s => s = "--bare") (CommandLine.arguments ())
val hasBossLib =
  Option.isSome (#lookupStruct PolyML.globalNameSpace "bossLib")

val () =
  print ("\nLoading the LSP's server-start files, on " ^
         (case !heapname of SOME h => h | NONE => "no heap") ^ "\n")

(* Asserted rather than reported: `--bare' dropped from the rule would
   run the full heap twice and still go green, which is the failure
   this file exists to catch. *)
val () =
  if bare = hasBossLib then
    (print ("expected " ^ (if bare then "no bossLib under --bare"
                           else "bossLib on the full heap") ^
            ", and it is the other way round\n");
     OS.Process.exit OS.Process.failure)
  else ()

val failures = ref ([] : string list)

fun note what e =
  (failures := what :: !failures;
   print ("  FAIL " ^ what ^ " : " ^ General.exnMessage e ^ "\n"))

fun tryLoad f =
  (QUse.use (OS.Path.concat (Systeml.HOLDIR, "tools-poly/lsp/" ^ f));
   print ("  ok   " ^ f ^ "\n"))
  handle e => note f e

(* hol.ML loads `Future' before the file that needs it, so do the same
   here.  `TacticParse' needs no load: `poly-init2' compiles it into this
   executable. *)
fun tryMeta m =
  (Meta.load m; print ("  ok   " ^ m ^ " (heap)\n")) handle e => note m e

val () = tryMeta "Future"
val () = List.app tryLoad
  ["deferred_proofs.ML", "pretty_printers_init.ML", "defnbase_init.ML",
   "hover_quote_init.ML", "tactic_steps.ML", "tactic_walker.ML",
   "goal_state_init.ML", "db_symbols_init.ML", "db_search_init.ML"]

val () =
  case rev (!failures) of
    [] => print "all loaded\n"
  | fs => print ("\n" ^ Int.toString (length fs) ^ " failed: " ^
                 String.concatWith ", " fs ^ "\n")

val () = OS.Process.exit
           (if null (!failures) then OS.Process.success
            else OS.Process.failure)
