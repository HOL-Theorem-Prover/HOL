signature computeLib =
sig
  include Abbrev

  (* compsets and their operations *)

  type compset

  val new_compset   : thm list -> compset
  val bool_compset  : unit -> compset

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
  val add_convs     : (term * int * conv) list -> unit
  val EVAL_CONV     : conv

  val write_datatype_info : TypeBasePure.tyinfo -> unit
  val add_persistent_funs : (string * thm) list -> unit

end
