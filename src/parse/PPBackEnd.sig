signature PPBackEnd =
sig

  type hol_type = Type.hol_type
  type ppstream = PP.ppstream
  type break_style = PP.break_style
  datatype annotation = BV of hol_type * string
                      | FV of hol_type * string
                      | Const of {Thy:string,Name:string,Ty:hol_type} * string
                      | Note of string

  type t = {add_string : ppstream -> string -> unit,
            add_ann_string : ppstream -> string * annotation -> unit,
            begin_block : ppstream -> PP.break_style -> int -> unit,
            end_block : ppstream -> unit,
            add_break : ppstream -> int * int -> unit,
            add_newline : ppstream -> unit,
            name : string}

  val with_ppstream : t -> ppstream ->
                      {add_break      : int * int -> unit,
                       add_newline    : unit -> unit,
                       add_ann_string : string * annotation -> unit,
                       add_string     : string -> unit,
                       begin_block    : break_style -> int -> unit,
                       clear_ppstream : unit -> unit,
                       end_block      : unit -> unit,
                       flush_ppstream : unit -> unit}

  val raw_terminal : t
  val vt100_terminal : t
  val emacs_terminal : t

end