signature derive_specsLib =
sig

  val clear_stack_intro_fails : unit -> unit
  val dest_call_tag : Term.term -> string * bool
  val derive_specs_for :
     string ->
       (int * (Thm.thm * int * int option) *
              (Thm.thm * int * int option) option) list
  val print_stack_intro_report : unit -> unit list

end
