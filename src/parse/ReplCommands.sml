structure ReplCommands :> ReplCommands =
struct


datatype string_src =
         Direct of string | ViaFile of {proxy_filename : string} | FromSource
type script_text = locn.locn * {filename : string option, text : string_src}

datatype repl_command = Success of string | Failure of string

fun sml_text s = Failure "Unimplemented"
fun set_initial_goal s = Failure "Unimplemented"
fun set_by_subgoal s = Failure "Unimplemented"
fun set_suffices_by_subgoal s = Failure "Unimplemented"
fun apply_tactic s = Failure "Unimplemented"
fun apply_tactic_pattern s = Failure "Unimplemented"
fun load_dependencies s = Failure "Unimplemented"

(* Under Moscow ML, handling a Success will require writing the string to a
   file and then use-ing it.  Error-reporting will be poor; under Poly/ML the
   compiler can be invoked more directly, with line-numbers set up
   appropriately. *)
fun execute_command rc =
    case rc of
        Failure s => print s
      | Success s => print "Can't do anything yet"


end
