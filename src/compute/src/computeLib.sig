signature computeLib =
sig

  include Abbrev

  (* compsets and their operations *)

  type compset
  
  val bool_redns    : thm list
  val new_rws       : unit -> compset
  val from_list     : thm list -> compset
  val add_thms      : thm list -> compset -> unit
  val add_conv      : term * int * conv -> compset -> unit
  val set_skip      : compset -> string*string -> int option -> unit

  (* thm preprocessors  *)

  val lazyfy_thm    : thm -> thm
  val strictify_thm : thm -> thm

  val CBV_CONV      : compset -> conv
  val WEAK_CBV_CONV : compset -> conv

  (* Support for pervasive evaluation mechanism *)

  val the_compset   : compset
  val add_funs      : thm list -> unit
  val EVAL          : conv
  val write_datatype_info : TypeBase.tyinfo -> unit
end;
