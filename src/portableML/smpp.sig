signature smpp =
sig

  type ('a,'b) t =
       'a * HOLPP.pretty list -> ('b * ('a * HOLPP.pretty list)) option

  val add_string : string -> ('a,unit) t
  val add_stringsz : string * int -> ('a,unit) t
  val add_newline : ('a,unit) t
  val add_break : int * int -> ('a,unit) t
  val nothing : ('a,unit) t
  val fail : ('a,unit) t
  val >> : ('a,'b) t * ('a,'c) t -> ('a,'c) t
  val >- : ('a,'b) t * ('b -> ('a,'c) t) -> ('a,'c) t
  val || : ('a,'b) t * ('a,'b) t -> ('a,'b) t
  val ||| : ('a,'b) t * (unit -> ('a,'b) t) -> ('a,'b) t
  val return : 'b -> ('a,'b) t
  val fupdate : ('a -> 'a) -> ('a,'a) t

  val block : HOLPP.break_style -> int -> ('a,'b) t -> ('a,'b) t
  val mapp : ('a -> ('b,unit) t) -> 'a list -> ('b, unit) t
  val mmap : ('a -> ('b,'c) t) -> 'a list -> ('b, 'c list) t
  val pr_list : ('b -> ('a,unit)t) -> ('a,unit) t -> 'b list -> ('a,unit)t
  val mappr_list : ('b -> ('a,'c)t) -> ('a,unit) t -> 'b list -> ('a,'c list) t
  val lift : ('a -> HOLPP.pretty) -> 'a -> ('st,unit) t
  val lower : ('st,'a) t -> 'st -> (HOLPP.pretty * 'a * 'st) option

(*
  val from_backend :
      PPBackEnd.t ->
      {add_string : string -> ('a,unit) t,
       add_xstring : PPBackEnd.xstring -> ('a,unit) t,
       flush : ('a,unit) t,
       add_newline : ('a,unit) t,
       add_break : int * int -> ('a,unit) t,
       ublock : HOLPP.break_style -> int -> ('a,unit) t -> ('a,unit) t,
       ustyle : PPBackEnd.pp_style list -> ('a,unit) t -> ('a,unit) t}

  val backend_block : PPBackEnd.t -> HOLPP.break_style -> int ->
                      ('a,'b) t -> ('a,'b) t
  val backend_style : PPBackEnd.t -> PPBackEnd.pp_style list ->
                      ('a,'b) t -> ('a,'b) t
*)
end
