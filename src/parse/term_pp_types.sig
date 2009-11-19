signature term_pp_types = sig
  datatype grav = Top | RealTop | Prec of (int * string)
  type sysprinter = (grav * grav * grav) -> int -> Term.term -> unit


  type ppstream_funs =
      {add_break      : int * int -> unit,
       add_newline    : unit -> unit,
       add_ann_string : string * PPBackEnd.annotation -> unit,
       add_string     : string -> unit,
       begin_style    : PPBackEnd.pp_style list -> unit,
       end_style      : unit -> unit,
       begin_block    : PP.break_style -> int -> unit,
       end_block      : unit -> unit}

  type 'a userprinter =
    'a -> sysprinter -> ppstream_funs ->
    (grav * grav * grav) -> int -> Portable.ppstream ->
    Term.term -> unit
  exception UserPP_Failed


end;
