structure term_pp_types = struct
  type ('a,'b) smppt =
       ('a * HOLPP.ppstream) -> ('b * ('a * HOLPP.ppstream)) option
  datatype grav = Top | RealTop | Prec of (int * string)

  type printing_info =
       {seen_frees : Term.term HOLset.set,
        current_bvars : Term.term HOLset.set,
        last_string : string, in_gspec : bool}

  type 'a printer = (printing_info,'a)smppt
  type uprinter = unit printer
  type sysprinter = (grav * grav * grav) -> int -> Term.term -> uprinter

  datatype lit_type = FldName | StringLit | NumLit | CharLit

  datatype annotation =
    BV of Type.hol_type * (unit -> string)
  | FV of Type.hol_type * (unit -> string)
  | TyV
  | TyOp of (unit -> string)
  | TySyn of (unit -> string)
  | Const of {Thy:string,Name:string,Ty:Type.hol_type * (unit -> string)}
  | SymConst of {Thy:string,Name:string,Ty:Type.hol_type * (unit -> string)}
  | Note of string
  | Literal of lit_type

  type xstring = {s:string,sz:int option,ann:annotation option}

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
    | White

  datatype pp_style =
      FG of pp_color
    | BG of pp_color
    | Bold
    | Underline
    | UserStyle of string

  type ppstream_funs =
      {add_break      : int * int -> uprinter,
       add_newline    : uprinter,
       add_string     : string -> uprinter,
       add_xstring    : xstring -> uprinter,
       ustyle    : pp_style list -> uprinter -> uprinter,
       ublock    : PP.break_style -> int -> uprinter -> uprinter}

  type 'tmg ppbackend =
       {add_string     : ppstream -> string -> unit,
        add_xstring    : ppstream -> xstring -> unit,
        begin_block    : ppstream -> PP.break_style -> int -> unit,
        end_block      : ppstream -> unit,
        add_break      : ppstream -> int * int -> unit,
        add_newline    : ppstream -> unit,
        begin_style    : ppstream -> pp_style list -> unit,
        end_style      : ppstream -> unit,
        tm_grammar_upd : 'tmg -> 'tmg,
        ty_grammar_upd : type_grammar.grammar -> type_grammar.grammar,
        name : string}

  type ('a,'tmg) userprinter =
    'a -> 'tmg ppbackend -> sysprinter -> ppstream_funs ->
    (grav * grav * grav) -> int -> Term.term -> uprinter
  exception UserPP_Failed
end;
