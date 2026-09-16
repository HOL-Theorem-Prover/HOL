signature PPBackEnd =
sig

  type hol_type = Type.hol_type

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
  val vt100_terminal        : t
  val emacs_terminal        : t
  val html_terminal         : t
  val html_escape    : string -> string

  (* For a consumer that wants what the printer knew as data rather
     than as colour.  `lsp_terminal` wraps each annotated symbol in
     delimiters carrying its kind, the theory-qualified name of a
     constant, and its type; they are added at zero width, so the
     layout is the one the reader would have seen without them.
     `lsp_segments` takes the result apart again into consecutive
     pieces of text, each with what was known about it -- `kind` is ""
     for the punctuation and spacing between symbols.

     Segments rather than offsets into a string: a caller that has to
     say *where* a symbol is must first agree with its reader on
     whether that is counted in bytes, characters or UTF-16 units, and
     HOL prints plenty that is not ASCII. *)
  type pp_segment = {text: string, kind: string, name: string, ty: string}
  val lsp_terminal          : t
  val lsp_segments          : string -> pp_segment list


end
