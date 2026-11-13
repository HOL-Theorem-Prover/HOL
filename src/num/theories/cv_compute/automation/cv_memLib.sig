signature cv_memLib =
sig
  include Abbrev

  datatype verbosity = Silent | Quiet | Verbose;

  val use_long_names  : bool ref
  val verbosity_level : verbosity ref
  val cv_print        : verbosity -> string -> unit
  val cv_print_term   : verbosity -> term -> unit
  val cv_print_thm    : verbosity -> thm -> unit
  val cv_time         : ('a -> 'b) -> 'a -> 'b

  val indent_print_term : verbosity -> string -> string -> term -> unit
  val indent_print_thm  : verbosity -> string -> string -> thm -> unit

  val cv_rep_thms     : unit -> (term * thm) list
  (* each cv_rep pattern and theorem, with the names of all the loaded
     theorems that translate the same pattern differently, if there are
     several (they come from different ancestors), and [] otherwise *)
  val cv_rep_entries  : unit -> (term * thm * string list) list
  (* removes the cv_rep theorem of this name, here and in descendants *)
  val cv_rep_delete   : string -> unit
  val cv_pre_thms     : unit -> thm list
  val cv_inline_thms  : unit -> thm list
  val cv_from_to_thms : unit -> thm list

  val cv_pre_add      : thm -> unit
  val cv_inline_add   : thm -> unit
  val cv_from_to_add  : thm -> unit

end
