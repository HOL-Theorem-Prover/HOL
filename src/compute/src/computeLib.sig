signature computeLib =
sig

  include Abbrev

  (* compsets and their operations *)

  type compset
  val new_rws       : unit -> compset
  val from_list     : thm list -> compset
  val add_thms      : thm list -> compset -> unit
  val add_conv      : term * int * conv -> compset -> unit
  val set_skip      : compset -> string*string -> int option -> unit
  val CBV_CONV      : comp_rws -> Abbrev.conv
  val WEAK_CBV_CONV : comp_rws -> Abbrev.conv


  val lazyfy_thm    : thm -> thm
  val strictify_thm : thm -> thm

  val CBV_CONV      : compset -> conv
  val WEAK_CBV_CONV : compset -> conv

  (* thm preprocessors  *)

  val lazyfy_thm    : thm -> thm
  val strictify_thm : thm -> thm

end;
