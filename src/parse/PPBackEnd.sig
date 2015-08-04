signature PPBackEnd =
sig

  type hol_type = Type.hol_type
  type ppstream = PP.ppstream
  type break_style = PP.break_style


  datatype lit_type = datatype term_pp_types.lit_type
  datatype pp_color = datatype term_pp_types.pp_color
  datatype pp_style = datatype term_pp_types.pp_style
  datatype annotation = datatype term_pp_types.annotation

  type xstring = term_pp_types.xstring
  type t = term_grammar.grammar term_pp_types.ppbackend

  val with_ppstream : t -> ppstream ->
                      {add_break      : int * int -> unit,
                       add_newline    : unit -> unit,
                       add_string     : string -> unit,
                       add_xstring    : xstring -> unit,
                       begin_block    : break_style -> int -> unit,
                       end_block      : unit -> unit,
                       begin_style    : pp_style list -> unit,
                       end_style      : unit -> unit,
                       clear_ppstream : unit -> unit,
                       flush_ppstream : unit -> unit}

  val known_UserStyles   : unit -> string list
  val lookup_UserStyle   : string -> string -> pp_style list
  val register_UserStyle : string option -> string -> pp_style list -> unit

  val raw_terminal          : t
  val debug_blocks_terminal : t
  val vt100_terminal        : t
  val emacs_terminal        : t
  val html_terminal         : t
  val html_escape    : string -> string


end
