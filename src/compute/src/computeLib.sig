signature computeLib =
sig
  include Abbrev
  type compset

  val monitoring      : (term -> bool) option ref
  val stoppers        : (term -> bool) option ref

  val new_compset     : thm list -> compset
  val bool_compset    : unit -> compset
  val add_thms        : thm list -> compset -> unit
  val add_conv        : term * int * conv -> compset -> unit
  val set_skip        : compset -> term -> int option -> unit

  val lazyfy_thm      : thm -> thm
  val strictify_thm   : thm -> thm

  val CBV_CONV        : compset -> conv
  val WEAK_CBV_CONV   : compset -> conv

  val the_compset     : compset
  val add_funs        : thm list -> unit
  val add_convs       : (term * int * conv) list -> unit
  val EVAL_CONV       : conv
  val EVAL_RULE       : thm -> thm
  val EVAL_TAC        : tactic

  val RESTR_EVAL_CONV : term list -> conv
  val RESTR_EVAL_RULE : term list -> thm -> thm
  val RESTR_EVAL_TAC  : term list -> tactic

  val write_datatype_info : TypeBasePure.tyinfo -> unit
  val add_persistent_funs : (string * thm) list -> unit

end
