signature Lib =
sig
  datatype frag = datatype Portable.frag
  val curry         : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry       : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val append        : 'a list -> 'a list -> 'a list
  val strcat        : string -> string -> string
  val equal         : ''a -> ''a -> bool
  val pair          : 'a -> 'b -> 'a * 'b
  val rpair         : 'a -> 'b -> 'b * 'a
  val swap          : 'a * 'b -> 'b * 'a
  val triple        : 'a -> 'b -> 'c -> 'a * 'b * 'c
  val quadruple     : 'a -> 'b -> 'c -> 'd -> 'a * 'b * 'c * 'd
  val cons          : 'a -> 'a list -> 'a list
  val ##            : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val apfst         : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val apsnd         : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val |>            : 'a * ('a -> 'b) -> 'b
  val C             : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val I             : 'a -> 'a
  val K             : 'a -> 'b -> 'a
  val S             : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
  val W             : ('a -> 'a -> 'b) -> 'a -> 'b
  val fst           : 'a * 'b -> 'a
  val snd           : 'a * 'b -> 'b
  val can           : ('a -> 'b) -> 'a -> bool
  val partial       : exn -> ('a -> 'b option) -> 'a -> 'b
  val total         : ('a -> 'b) -> 'a -> 'b option
  val try           : ('a -> 'b) -> 'a -> 'b
  val trye          : ('a -> 'b) -> 'a -> 'b
  val assert        : ('a -> bool) -> 'a -> 'a
  val assert_exn    : ('a -> bool) -> 'a -> exn -> 'a
  val with_exn      : ('a -> 'b) -> 'a -> exn -> 'b
  val tryfind       : ('a -> 'b) -> 'a list -> 'b
  val el            : int -> 'a list -> 'a
  val single        : 'a -> 'a list
  val singleton_of_list : 'a list -> 'a
  val pair_of_list  : 'a list -> 'a * 'a
  val triple_of_list : 'a list -> 'a * 'a * 'a
  val quadruple_of_list : 'a list -> 'a * 'a * 'a * 'a
  val index         : ('a -> bool) -> 'a list -> int
  val map2          : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val all           : ('a -> bool) -> 'a list -> bool
  val all2          : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val exists        : ('a -> bool) -> 'a list -> bool
  val first         : ('a -> bool) -> 'a list -> 'a
  val first_opt     : (int -> 'a -> 'b option) -> 'a list -> 'b option
  val get_first     : ('a -> 'b option) -> 'a list -> 'b option
  val split_after   : int -> 'a list -> 'a list * 'a list
  val partition     : ('a -> bool) -> 'a list -> 'a list * 'a list
  val filter        : ('a -> bool) -> 'a list -> 'a list
  val itlist        : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val itlist2       : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val rev_itlist    : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist2   : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val end_itlist    : ('a -> 'a -> 'a) -> 'a list -> 'a
  val foldl_map     : ('a * 'b -> 'a * 'c) -> 'a * 'b list -> 'a * 'c list
  val separate      : 'a -> 'a list -> 'a list
  val zip           : 'a list -> 'b list -> ('a * 'b) list
  val combine       : 'a list * 'b list -> ('a * 'b) list
  val unzip         : ('a * 'b) list -> 'a list * 'b list
  val split         : ('a * 'b) list -> 'a list * 'b list
  val mapfilter     : ('a -> 'b) -> 'a list -> 'b list
  val flatten       : 'a list list -> 'a list
  val pluck         : ('a -> bool) -> 'a list -> 'a * 'a list
  val trypluck      : ('a -> 'b) -> 'a list -> 'b * 'a list
  val trypluck'     : ('a -> 'b option) -> 'a list -> ('b option * 'a list)
  val enumerate     : int -> 'a list -> (int * 'a) list
  val upto          : int -> int -> int list
  val repeat        : ('a -> 'a) -> 'a -> 'a
  val assoc         : ''a -> (''a * 'b) list -> 'b
  val rev_assoc     : ''a -> ('b * ''a) list -> 'b
  val assoc1        : ''a -> (''a * 'b) list -> (''a * 'b) option
  val assoc2        : ''a -> ('b * ''a) list -> ('b * ''a) option
  val appi          : (int -> 'a -> unit) -> 'a list -> unit
  val mapi          : (int -> 'a -> 'b) -> 'a list -> 'b list
  val mapshape       : int list -> ('a list -> 'b) list -> 'a list -> 'b list

  type ('a,'b) subst = {redex:'a, residue:'b} list
  val subst_assoc   : ('a -> bool) -> ('a,'b)subst -> 'b option
  val |->           : ('a * 'b) -> {redex:'a, residue:'b}

  val mem           : ''a -> ''a list -> bool
  val insert        : ''a -> ''a list -> ''a list
  val mk_set        : ''a list -> ''a list
  val union         : ''a list -> ''a list -> ''a list
  val U             : ''a list list -> ''a list
  val set_diff      : ''a list -> ''a list -> ''a list
  val subtract      : ''a list -> ''a list -> ''a list
  val intersect     : ''a list -> ''a list -> ''a list
  val null_intersection : ''a list -> ''a list -> bool
  val set_eq        : ''a list -> ''a list -> bool
  val op_mem        : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
  val op_insert     : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  val op_union      : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val op_mk_set     : ('a -> 'a -> bool) -> 'a list -> 'a list
  val op_U          : ('a -> 'a -> bool) -> 'a list list -> 'a list
  val op_intersect  : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val op_set_diff   : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val for           : int -> int -> (int -> 'a) -> 'a list
  val for_se        : int -> int -> (int -> unit) -> unit
  val int_to_string : int -> string
  val string_to_int : string -> int
  val sort          : ('a -> 'a -> bool) -> 'a list -> 'a list
  val int_sort      : int list -> int list
  val topsort       : ('a -> 'a -> bool) -> 'a list -> 'a list
  val dict_topsort  : ('a,'a list) Redblackmap.dict -> 'a list
  val vector_topsort: int list vector -> int list

  val start_time    : unit -> Timer.cpu_timer
  val end_time      : Timer.cpu_timer -> unit
  val time          : ('a -> 'b) -> 'a -> 'b

  val start_real_time : unit -> Timer.real_timer
  val end_real_time   : Timer.real_timer -> unit
  val real_time       : ('a -> 'b) -> 'a -> 'b

  type ('a,'b) istream
  val mk_istream    : ('a -> 'a) -> 'a -> ('a -> 'b) -> ('a,'b) istream
  val next          : ('a,'b) istream -> ('a,'b) istream
  val state         : ('a,'b) istream -> 'b
  val reset         : ('a,'b) istream -> ('a,'b) istream

  val quote         : string -> string
  val mlquote       : string -> string
  val words2        : string -> string -> string list
  val commafy       : string list -> string list
  val is_substring  : string -> string -> bool
  val saying        : bool ref
  val say           : string -> unit
  val prime         : string -> string
  val unprime       : string -> string
  val unprefix      : string -> string -> string

  val str_all       : (char -> bool) -> string -> bool

  val front_last    : 'a list -> 'a list * 'a
  val butlast       : 'a list -> 'a list
  val last          : 'a list -> 'a
  val funpow        : int -> ('a -> 'a) -> 'a -> 'a
  val with_flag     : 'a ref * 'a -> ('b -> 'c) -> 'b -> 'c
  val hash          : int -> string -> int*int -> int

  type 'a cmp       = 'a * 'a -> order
  val bool_compare  : bool cmp
  val pair_compare  : ('a cmp * 'b cmp) -> ('a * 'b) cmp
  val list_compare  : 'a cmp -> 'a list cmp
  val measure_cmp   : ('a -> int) -> 'a cmp
  val inv_img_cmp   : ('b -> 'a) -> 'a cmp -> 'b cmp
  val lex_cmp       : ('b cmp * 'c cmp) -> (('a -> 'b) * ('a -> 'c)) -> 'a cmp
  val flip_cmp      : 'a cmp -> 'a cmp
  val flip_order    : order -> order

  datatype 'a delta = SAME | DIFF of 'a

  val delta_apply   : ('a -> 'a delta) -> 'a -> 'a
  val delta_map     : ('a -> 'a delta) -> 'a list -> 'a list delta
  val delta_pair    : ('a -> 'a delta) -> ('b -> 'b delta)
                       -> 'a * 'b -> ('a * 'b) delta

  val deinitcommentss : substring -> substring
  val deinitcomment : string -> string

  datatype ('a,'b) verdict = PASS of 'a | FAIL of 'b
  val verdict : ('a -> 'b) -> ('a -> 'c) -> 'a -> ('b, 'c*exn)verdict
  val ?>      : ('a,'c)verdict * ('a -> ('b,'c)verdict) -> ('b,'c)verdict
end
