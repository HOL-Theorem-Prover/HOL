signature Lib =
sig
   datatype 'a delta = SAME | DIFF of 'a
   datatype frag = datatype Portable.frag
   datatype ('a, 'b) verdict = PASS of 'a | FAIL of 'b
   type 'a cmp = 'a * 'a -> order
   type ('a, 'b) istream
   type ('a, 'b) subst = {redex: 'a, residue: 'b} list
   val ## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
   val ?> : ('a, 'c)verdict * ('a -> ('b, 'c)verdict) -> ('b, 'c)verdict
   val |-> : ('a * 'b) -> {redex: 'a, residue: 'b}
   val |> : 'a * ('a -> 'b) -> 'b
   val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
   val I : 'a -> 'a
   val K : 'a -> 'b -> 'a
   val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
   val U : ''a list list -> ''a list
   val W : ('a -> 'a -> 'b) -> 'a -> 'b
   val all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
   val all : ('a -> bool) -> 'a list -> bool
   val apfst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
   val append : 'a list -> 'a list -> 'a list
   val appi : (int -> 'a -> unit) -> 'a list -> unit
   val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
   val assert : ('a -> bool) -> 'a -> 'a
   val assert_exn : ('a -> bool) -> 'a -> exn -> 'a
   val assoc1 : ''a -> (''a * 'b) list -> (''a * 'b) option
   val assoc2 : ''a -> ('b * ''a) list -> ('b * ''a) option
   val assoc : ''a -> (''a * 'b) list -> 'b
   val bool_compare : bool cmp
   val butlast : 'a list -> 'a list
   val can : ('a -> 'b) -> 'a -> bool
   val combine : 'a list * 'b list -> ('a * 'b) list
   val commafy : string list -> string list
   val cons : 'a -> 'a list -> 'a list
   val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
   val deinitcomment : string -> string
   val deinitcommentss : substring -> substring
   val delta_apply : ('a -> 'a delta) -> 'a -> 'a
   val delta_map : ('a -> 'a delta) -> 'a list -> 'a list delta
   val delta_pair :
      ('a -> 'a delta) -> ('b -> 'b delta) -> 'a * 'b -> ('a * 'b) delta
   val dict_topsort : ('a, 'a list) Redblackmap.dict -> 'a list
   val el : int -> 'a list -> 'a
   val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
   val end_real_time : Timer.real_timer -> unit
   val end_time : Timer.cpu_timer -> unit
   val enumerate : int -> 'a list -> (int * 'a) list
   val equal : ''a -> ''a -> bool
   val exists : ('a -> bool) -> 'a list -> bool
   val filter : ('a -> bool) -> 'a list -> 'a list
   val first : ('a -> bool) -> 'a list -> 'a
   val first_opt : (int -> 'a -> 'b option) -> 'a list -> 'b option
   val flatten : 'a list list -> 'a list
   val flip_cmp : 'a cmp -> 'a cmp
   val flip_order : order -> order
   val foldl_map : ('a * 'b -> 'a * 'c) -> 'a * 'b list -> 'a * 'c list
   val for : int -> int -> (int -> 'a) -> 'a list
   val for_se : int -> int -> (int -> unit) -> unit
   val front_last : 'a list -> 'a list * 'a
   val fst : 'a * 'b -> 'a
   val funpow : int -> ('a -> 'a) -> 'a -> 'a
   val get_first : ('a -> 'b option) -> 'a list -> 'b option
   val hash : int -> string -> int * int -> int
   val index : ('a -> bool) -> 'a list -> int
   val insert : ''a -> ''a list -> ''a list
   val int_sort : int list -> int list
   val int_to_string : int -> string
   val intersect : ''a list -> ''a list -> ''a list
   val inv_img_cmp : ('b -> 'a) -> 'a cmp -> 'b cmp
   val is_substring : string -> string -> bool
   val itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
   val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
   val last : 'a list -> 'a
   val lex_cmp : ('b cmp * 'c cmp) -> (('a -> 'b) * ('a -> 'c)) -> 'a cmp
   val list_compare : 'a cmp -> 'a list cmp
   val list_of_pair : 'a * 'a -> 'a list
   val list_of_quadruple : 'a * 'a * 'a * 'a -> 'a list
   val list_of_singleton : 'a -> 'a list
   val list_of_triple : 'a * 'a * 'a -> 'a list
   val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
   val mapfilter : ('a -> 'b) -> 'a list -> 'b list
   val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
   val mapshape : int list -> ('a list -> 'b) list -> 'a list -> 'b list
   val measure_cmp : ('a -> int) -> 'a cmp
   val mem : ''a -> ''a list -> bool
   val mk_istream : ('a -> 'a) -> 'a -> ('a -> 'b) -> ('a, 'b) istream
   val mk_set : ''a list -> ''a list
   val mlquote : string -> string
   val next : ('a, 'b) istream -> ('a, 'b) istream
   val null_intersection : ''a list -> ''a list -> bool
   val op_U : ('a -> 'a -> bool) -> 'a list list -> 'a list
   val op_insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
   val op_intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
   val op_mem : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
   val op_mk_set : ('a -> 'a -> bool) -> 'a list -> 'a list
   val op_set_diff : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
   val op_union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
   val pair : 'a -> 'b -> 'a * 'b
   val pair_compare : ('a cmp * 'b cmp) -> ('a * 'b) cmp
   val pair_of_list : 'a list -> 'a * 'a
   val partial : exn -> ('a -> 'b option) -> 'a -> 'b
   val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
   val pluck : ('a -> bool) -> 'a list -> 'a * 'a list
   val ppstring : (HOLPP.ppstream -> 'a -> unit) -> 'a -> string
   val prime : string -> string
   val quadruple : 'a -> 'b -> 'c -> 'd -> 'a * 'b * 'c * 'd
   val quadruple_of_list : 'a list -> 'a * 'a * 'a * 'a
   val quote : string -> string
   val real_time : ('a -> 'b) -> 'a -> 'b
   val repeat : ('a -> 'a) -> 'a -> 'a
   val reset : ('a, 'b) istream -> ('a, 'b) istream
   val rev_assoc : ''a -> ('b * ''a) list -> 'b
   val rev_itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
   val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
   val rpair : 'a -> 'b -> 'b * 'a
   val say : string -> unit
   val saying : bool ref
   val separate : 'a -> 'a list -> 'a list
   val set_diff : ''a list -> ''a list -> ''a list
   val set_eq : ''a list -> ''a list -> bool
   val singleton_of_list : 'a list -> 'a
   val snd : 'a * 'b -> 'b
   val sort : ('a -> 'a -> bool) -> 'a list -> 'a list
   val split : ('a * 'b) list -> 'a list * 'b list
   val split_after : int -> 'a list -> 'a list * 'a list
   val start_real_time : unit -> Timer.real_timer
   val start_time : unit -> Timer.cpu_timer
   val state : ('a, 'b) istream -> 'b
   val str_all : (char -> bool) -> string -> bool
   val strcat : string -> string -> string
   val string_to_int : string -> int
   val subst_assoc : ('a -> bool) -> ('a, 'b)subst -> 'b option
   val subtract : ''a list -> ''a list -> ''a list
   val swap : 'a * 'b -> 'b * 'a
   val time : ('a -> 'b) -> 'a -> 'b
   val topsort : ('a -> 'a -> bool) -> 'a list -> 'a list
   val total : ('a -> 'b) -> 'a -> 'b option
   val triple : 'a -> 'b -> 'c -> 'a * 'b * 'c
   val triple_of_list : 'a list -> 'a * 'a * 'a
   val try : ('a -> 'b) -> 'a -> 'b
   val trye : ('a -> 'b) -> 'a -> 'b
   val tryfind : ('a -> 'b) -> 'a list -> 'b
   val trypluck': ('a -> 'b option) -> 'a list -> ('b option * 'a list)
   val trypluck : ('a -> 'b) -> 'a list -> 'b * 'a list
   val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
   val union : ''a list -> ''a list -> ''a list
   val unprefix : string -> string -> string
   val unprime : string -> string
   val unzip : ('a * 'b) list -> 'a list * 'b list
   val upto : int -> int -> int list
   val vector_topsort : int list vector -> int list
   val verdict : ('a -> 'b) -> ('a -> 'c) -> 'a -> ('b, 'c * exn)verdict
   val with_exn : ('a -> 'b) -> 'a -> exn -> 'b
   val with_flag : 'a ref * 'a -> ('b -> 'c) -> 'b -> 'c
   val words2 : string -> string -> string list
   val zip : 'a list -> 'b list -> ('a * 'b) list
end
