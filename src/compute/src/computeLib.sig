signature computeLib =
sig
  include Abbrev
  type compset

  val auto_import_definitions : bool ref

  val monitoring      : (term -> bool) option ref
  val stoppers        : (term -> bool) option ref

  val new_compset     : thm list -> compset
  val bool_compset    : unit -> compset

  val add_thms        : thm list -> compset -> compset
  val add_conv        : term * int * conv -> compset -> compset
  val add_thmset      : string -> compset -> compset
  val set_skip        : compset -> term -> int option -> compset
  val set_EVAL_skip   : term -> int option -> unit
  val temp_set_EVAL_skip : term -> int option -> unit

  val scrub_const     : compset -> term -> compset
  val scrub_thms      : thm list -> compset -> compset

  val lazyfy_thm      : thm -> thm
  val strictify_thm   : thm -> thm

  val CBV_CONV        : compset -> conv
  val CBVn_CONV       : int -> compset -> conv
  val WEAK_CBV_CONV   : compset -> conv

  val the_compset     : compset ref
  val add_funs        : thm list -> unit
  val add_convs       : (term * int * conv) list -> unit

  val del_consts      : term list -> unit
  val del_funs        : thm list -> unit

  val EVAL_CONV       : conv
  val EVALn_CONV      : int -> conv
  val EVAL_RULE       : thm -> thm
  val EVAL_TAC        : tactic

  val RESTR_EVAL_CONV : term list -> conv
  val RESTR_EVAL_RULE : term list -> thm -> thm
  val RESTR_EVAL_TAC  : term list -> tactic

  val add_datatype_info : compset -> TypeBasePure.tyinfo -> compset
  val write_datatype_info : TypeBasePure.tyinfo -> unit

  val add_persistent_funs : string list -> unit
  val del_persistent_consts : term list -> unit
  val pp_compset : compset Parse.pprinter

  type transform = clauses.transform

  val listItems : compset -> ((string * string) * transform list) list
  val unmapped  : compset -> (string * string) list

  datatype compset_element =
      Convs of (term * int * conv) list
    | Defs of thm list
    | Extenders of (compset -> compset) list
    | Tys of hol_type list

  val compset_conv: compset -> compset_element list -> conv
  val extend_compset: compset_element list -> compset -> compset
end
