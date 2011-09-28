structure term_pp_types = struct
  datatype grav = Top | RealTop | Prec of (int * string)

  type printing_info =
       {seen_frees : Term.term HOLset.set,
        current_bvars : Term.term HOLset.set,
        last_string : string, in_gspec : bool}

  type 'a printer = (printing_info,'a)smpp.t
  type uprinter = unit printer
  type sysprinter = (grav * grav * grav) -> int -> Term.term -> uprinter

  type ppstream_funs =
      {add_break      : int * int -> uprinter,
       add_newline    : uprinter,
       add_string     : string -> uprinter,
       add_xstring    : PPBackEnd.xstring -> uprinter,
       ustyle    : PPBackEnd.pp_style list -> uprinter -> uprinter,
       ublock    : PP.break_style -> int -> uprinter -> uprinter}

  type 'a userprinter =
    'a -> PPBackEnd.t -> sysprinter -> ppstream_funs ->
    (grav * grav * grav) -> int -> Term.term -> uprinter
  exception UserPP_Failed
end;
