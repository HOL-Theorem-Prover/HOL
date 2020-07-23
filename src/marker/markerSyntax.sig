signature markerSyntax =
sig
  include Abbrev

  val stmarker_tm : term
  val AC_tm       : term
  val Cong_tm     : term
  val abbrev_tm   : term
  val label_tm    : term

  val mk_abbrev   : string * term -> term
  val dest_abbrev : term -> string * term
  val is_abbrev   : term -> bool
  val is_malformed_abbrev : term -> bool
  val compare_abbrev : term -> term -> bool

  val Abbr        : term frag list -> thm
  val is_abbr     : thm -> bool
  val dest_abbr   : thm -> string

  val label_ty    : hol_type
  val mk_label_var: string -> term
  val L           : string -> thm
  val mk_label    : string * term -> term
  val dest_label  : term -> string * term
  val is_label    : term -> bool
  val dest_label_ref : thm -> string
  val is_label_ref   : thm -> bool

  val using_t : term
  val usingThm_t : term
  val mk_using : thm -> term
  val MK_USING : thm -> thm
  val is_using : term -> bool
  val DEST_USING : thm -> thm

end
