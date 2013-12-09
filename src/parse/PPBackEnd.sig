signature PPBackEnd =
sig

  type hol_type = Type.hol_type
  type ppstream = PP.ppstream
  type break_style = PP.break_style

  datatype pp_color =
      Black
    | RedBrown
    | Green
    | BrownGreen
    | DarkBlue
    | Purple
    | BlueGreen
    | DarkGrey
    | LightGrey
    | OrangeRed
    | VividGreen
    | Yellow
    | Blue
    | PinkPurple
    | LightBlue
    | White;

  datatype pp_style =
      FG of pp_color
    | BG of pp_color
    | Bold
    | Underline
    | UserStyle of string

  datatype annotation = BV of hol_type * (unit -> string)
                      | FV of hol_type * (unit -> string)
                      | TyV
                      | TyOp of (unit -> string)
                      | TySyn of (unit -> string)
                      | Const of {Thy:string,Name:string,Ty:hol_type} * string
                      | Note of string;

  type xstring = {s:string,sz:int option,ann:annotation option}

  type t = {add_string     : ppstream -> string -> unit,
            add_xstring    : ppstream -> xstring -> unit,
            begin_block    : ppstream -> PP.break_style -> int -> unit,
            end_block      : ppstream -> unit,
            add_break      : ppstream -> int * int -> unit,
            add_newline    : ppstream -> unit,
            begin_style    : ppstream -> pp_style list -> unit,
            end_style      : ppstream -> unit,
            name : string}

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
