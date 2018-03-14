signature PPBackEnd =
sig

  type hol_type = Type.hol_type
  type break_style = PP.break_style

  datatype lit_type = datatype term_pp_types.lit_type
  datatype pp_color = datatype term_pp_types.pp_color
  datatype pp_style = datatype term_pp_types.pp_style
  datatype annotation = datatype term_pp_types.annotation

  type output_colors = {
      bv    : pp_color,
      fv    : pp_color,
      tyv   : pp_color,
      tyop  : pp_color,
      tysyn : pp_color
    }

  type xstring = term_pp_types.xstring
  type t = term_grammar.grammar term_pp_types.ppbackend

  val known_UserStyles   : unit -> string list
  val lookup_UserStyle   : string -> string -> pp_style list
  val register_UserStyle : string option -> string -> pp_style list -> unit

  val ansi_terminal         : string -> output_colors -> t
  val raw_terminal          : t
  val debug_blocks_terminal : t
  val vt100_terminal        : t
  val emacs_terminal        : t
  val html_terminal         : t
  val html_escape    : string -> string


end
