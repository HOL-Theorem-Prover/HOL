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
 *)
val () = print "\nLoading the LSP's server-start files\n"

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
