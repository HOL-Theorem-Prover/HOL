signature Portable =
sig
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val ## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val apfst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val pair_map : ('a -> 'b) -> 'a * 'a -> 'b * 'b
  val $  : ('a -> 'b) * 'a -> 'b
  val ?  : (bool * ('a -> 'a)) -> 'a -> 'a
  val |> : 'a * ('a -> 'b) -> 'b
  val |>> : ('a * 'b) * ('a -> 'c) -> ('c * 'b)
  val ||> : ('a * 'b) * ('b -> 'c) -> ('a * 'c)
  val ||-> : ('a * 'b) * ('a -> 'b -> 'c) -> 'c
  val B2 : ('c -> 'd) -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'd
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val flip : ('a * 'b -> 'c) -> ('b * 'a -> 'c)
  val I : 'a -> 'a
  val K : 'a -> 'b -> 'a
  val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
  val W : ('a -> 'a -> 'b) -> 'a -> 'b

  val append : 'a list -> 'a list -> 'a list
  val equal : ''a -> ''a -> bool
  val strcat : string -> string -> string
  val cons : 'a -> 'a list -> 'a list
  val pair : 'a -> 'b -> 'a * 'b

  val rpair : 'a -> 'b -> 'b * 'a
  val swap : 'a * 'b -> 'b * 'a
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val triple : 'a -> 'b -> 'c -> 'a * 'b * 'c
  val quadruple : 'a -> 'b -> 'c -> 'd -> 'a * 'b * 'c * 'd

  val can : ('a -> 'b) -> 'a -> bool
  val total : ('a -> 'b) -> 'a -> 'b option
  val partial : exn -> ('a -> 'b option) -> 'a -> 'b
  val these : 'a list option -> 'a list

  val assert_exn : ('a -> bool) -> 'a -> exn -> 'a
  val with_exn : ('a -> 'b) -> 'a -> exn -> 'b
  val finally : (unit -> unit) -> ('a -> 'b) -> ('a -> 'b)
     (* first argument (the finally finisher) must terminate, and preferably
        quickly, or you may mask/hide user-generated Interrupt exceptions *)

  val list_of_singleton : 'a -> 'a list
  val single : 'a -> 'a list (* synonym of list_of_singleton *)
  val the_single : 'a list -> 'a        (* exn List.Empty if list length <> 1 *)
  val singleton : ('a list -> 'b list) -> 'a -> 'b
                (* singleton f x raises exn List.Empty if length (f [x]) <> 1 *)
  val list_of_pair : 'a * 'a -> 'a list
  val list_of_triple : 'a * 'a * 'a -> 'a list
  val list_of_quadruple : 'a * 'a * 'a * 'a -> 'a list
  val the_list : 'a option -> 'a list
  val the_default : 'a -> 'a option -> 'a

  val all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val first_opt : (int -> 'a -> 'b option) -> 'a list -> 'b option
  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val foldl' : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val foldr' : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val foldl2' : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
                                              (* exn ListPair.UnequalLengths *)
  val foldr2' : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
                                              (* exn ListPair.UnequalLengths *)
  val foldl_map : ('a * 'b -> 'a * 'c) -> 'a * 'b list -> 'a * 'c list
  val zip3 : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
                                              (* exn ListPair.UnequalLengths *)
  val separate : 'a -> 'a list -> 'a list
  val front_last : 'a list -> 'a list * 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val filter_out : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val split : ('a * 'b) list -> 'a list * 'b list
  val mapfilter : ('a -> 'b) -> 'a list -> 'b list
  val flatten : 'a list list -> 'a list
  val trypluck': ('a -> 'b option) -> 'a list -> ('b option * 'a list)
  val plucki : ('a -> bool) -> 'a list -> ('a * int * 'a list) option
  val funpow : int -> ('a -> 'a) -> 'a -> 'a
  val repeat : ('a -> 'a) -> 'a -> 'a
  val enumerate : int -> 'a list -> (int * 'a) list
  val upto : int -> int -> int list
  val appi : (int -> 'a -> unit) -> 'a list -> unit
  val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list

  type 'a cmp = 'a * 'a -> order
  val flip_order : order -> order
  val flip_cmp : 'a cmp -> 'a cmp
  val bool_compare : bool cmp
  val list_compare : 'a cmp -> 'a list cmp
  val option_compare : 'a cmp -> 'a option cmp
  val pair_compare : ('a cmp * 'b cmp) -> ('a * 'b) cmp
  val measure_cmp : ('a -> int) -> 'a cmp
  val inv_img_cmp : ('b -> 'a) -> 'a cmp -> 'b cmp
  val lex_cmp : ('b cmp * 'c cmp) -> (('a -> 'b) * ('a -> 'c)) -> 'a cmp

  val for : int -> int -> (int -> 'a) -> 'a list
  val for_se : int -> int -> (int -> unit) -> unit
  val make_counter : {init:int,inc:int} -> unit -> int
  val syncref : 'a -> {get:unit -> 'a, upd:('a -> 'b * 'a) -> 'b}

  val assoc1 : ''a -> (''a * 'b) list -> (''a * 'b) option
  val assoc2 : ''a -> ('b * ''a) list -> ('b * ''a) option

  val sort : ('a -> 'a -> bool) -> 'a list -> 'a list
  val int_sort : int list -> int list
  val vector_topsort : int list vector -> int list

  type ('a, 'b) subst = {redex: 'a, residue: 'b} list
  val subst_assoc : ('a -> bool) -> ('a, 'b)subst -> 'b option
  val |-> : ('a * 'b) -> {redex: 'a, residue: 'b}

  val mem : ''a -> ''a list -> bool
  val insert : ''a -> ''a list -> ''a list
  val mk_set : ''a list -> ''a list
  val union : ''a list -> ''a list -> ''a list
  val U : ''a list list -> ''a list
  val set_diff : ''a list -> ''a list -> ''a list
  val subtract : ''a list -> ''a list -> ''a list
  val intersect : ''a list -> ''a list -> ''a list
  val null_intersection : ''a list -> ''a list -> bool
  val set_eq : ''a list -> ''a list -> bool

  type 'a eqf = 'a -> 'a -> bool
  val pair_eq : 'a eqf -> 'b eqf -> ('a * 'b) eqf
  val fst_eq : 'a eqf -> ('a * 'b) eqf
  val inv_img_eq : ('a -> 'b) -> 'b eqf -> 'a eqf
  val option_eq : 'a eqf -> 'a option eqf
  val list_eq : 'a eqf -> 'a list eqf
  val redres_eq : 'a eqf -> 'b eqf -> {redex:'a,residue:'b} eqf

  val op_assoc1 : 'a eqf -> 'a -> ('a * 'b) list -> 'b option
  val op_mem : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
  val op_insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  val op_mk_set : ('a -> 'a -> bool) -> 'a list -> 'a list
  val op_union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val op_U : ('a -> 'a -> bool) -> 'a list list -> 'a list
  val op_intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val op_set_diff : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val op_remove : ('a -> 'b -> bool) -> 'a -> 'b list -> 'b list
  val op_update : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list

  val int_to_string : int -> string
  val quote : string -> string
  val mlquote : string -> string
  val enclose : string -> string -> string -> string (* enclose ld rd mid *)
  val is_substring : string -> string -> bool
  val prime : string -> string
  val commafy : string list -> string list
  val words2 : string -> string -> string list
  val str_all : (char -> bool) -> string -> bool

  val hash : int -> string -> int * int -> int

  val with_flag : 'a ref * 'a -> ('b -> 'c) -> 'b -> 'c
  val genwith_flag : {get: unit -> 'a, set : 'a -> unit} * 'a -> ('b -> 'c) ->
                     ('b -> 'c)

  type ('a, 'b) istream
  val mk_istream : ('a -> 'a) -> 'a -> ('a -> 'b) -> ('a, 'b) istream
  val next : ('a, 'b) istream -> ('a, 'b) istream
  val state : ('a, 'b) istream -> 'b
  val reset : ('a, 'b) istream -> ('a, 'b) istream

  datatype 'a delta = SAME | DIFF of 'a
  val delta_apply : ('a -> 'a delta) -> 'a -> 'a
  val delta_map : ('a -> 'a delta) -> 'a list -> 'a list delta
  val delta_pair :
    ('a -> 'a delta) -> ('b -> 'b delta) -> 'a * 'b -> ('a * 'b) delta

  val deinitcomment : string -> string
  val deinitcommentss : substring -> substring

  datatype ('a, 'b) verdict = PASS of 'a | FAIL of 'b
  val verdict : ('a -> 'b) -> ('a -> 'c) -> 'a -> ('b, 'c * exn)verdict
  val ?> : ('a, 'c)verdict * ('a -> ('b, 'c)verdict) -> ('b, 'c)verdict

  type time      = Time.time
  type instream  = TextIO.instream
  type outstream = TextIO.outstream

  datatype frag = datatype HOLPP.frag
  datatype break_style = datatype HOLPP.break_style
  val with_ppstream : OldPP.ppstream
                       -> {add_break      : int * int -> unit,
                           add_newline    : unit -> unit,
                           add_string     : string -> unit,
                           begin_block    : HOLPP.break_style -> int -> unit,
                           clear_ppstream : unit -> unit,
                           end_block      : unit -> unit,
                           flush_ppstream : unit -> unit}

  val dec: int ref -> unit
  val inc: int ref -> unit

  val pull_prefix : ('a -> bool) list -> 'a list -> 'a list

  val explode: string -> string list
  val implode: string list -> string
  val ordof: string * int -> int
  val replace_string : {from:string,to:string} -> string -> string
  val remove_wspace : string -> string

  val time_eq: time -> time -> bool
  val timestamp: unit -> time
  val mk_time: {sec : Arbnum.num, usec : Arbnum.num} -> time
  val time_to_string: time -> string
  val dest_time: time -> {sec : Arbnum.num, usec : Arbnum.num}
  val time_lt: time -> time -> bool
  val time_max : time * time -> time
  val time_maxl : time list -> time
  val time : ('a -> 'b) -> 'a -> 'b
  val realtime : ('a -> 'b) -> 'a -> 'b

  val getEnv: string -> string option
  val getArgs: unit -> string list
  val argv: unit -> string list
  val system: string -> int
  val cd: string -> unit
  val pwd: unit -> string
  val listDir: string -> string list
  val exit: unit -> 'a

  val pointer_eq : 'a * 'a -> bool
  val ref_to_int : 'a ref -> int

  val end_of_stream: instream -> bool
  val flush_out: outstream -> unit
  val stdin   : instream
  val std_out : outstream
  val close_out: outstream -> unit
  val output: outstream * string -> unit
  val close_in: instream -> unit
  val open_out: string -> outstream
  val outputc: outstream -> string -> unit
  val input_line: instream -> string
  val open_in : string -> instream
  exception Io of string

  exception Mod
  exception Div
  exception Interrupt

  type 'a quotation = 'a HOLPP.quotation
  val pprint : 'a HOLPP.pprinter -> 'a -> unit
  val norm_quote : 'a quotation -> 'a quotation
  val quote_to_string : ('a -> string) -> 'a quotation -> string
  val quote_to_string_list : string quotation -> string list

  val catch_SIGINT : unit -> unit
  val md5sum : string -> string

  structure HOLSusp : sig
    type 'a susp
    val delay : (unit -> 'a) -> 'a susp
    val force : 'a susp -> 'a
  end

  val reraise : exn -> 'a
end
