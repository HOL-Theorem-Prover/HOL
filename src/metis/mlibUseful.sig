(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibUseful =
sig

(* Exceptions, profiling and tracing *)
exception Error of string
exception Bug of string
val report      : exn -> string
val assert      : bool -> exn -> unit
val try         : ('a -> 'b) -> 'a -> 'b
val total       : ('a -> 'b) -> 'a -> 'b option
val can         : ('a -> 'b) -> 'a -> bool
val partial     : exn -> ('a -> 'b option) -> 'a -> 'b
val timed       : ('a -> 'b) -> 'a -> real * 'b
val timed_many  : ('a -> 'b) -> 'a -> real * 'b
val trace_level : int ref
val traces      : {module : string, alignment : int -> int} list ref
val tracing     : {module : string, level : int} -> bool
val trace       : string -> unit

(* Combinators *)
val C      : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
val I      : 'a -> 'a
val K      : 'a -> 'b -> 'a
val S      : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
val W      : ('a -> 'a -> 'b) -> 'a -> 'b
val oo     : ('a -> 'b) * ('c -> 'd -> 'a) -> 'c -> 'd -> 'b
val ##     : ('a -> 'c) * ('b -> 'd) -> 'a * 'b -> 'c * 'd
val funpow : int -> ('a -> 'a) -> 'a -> 'a

(* Booleans *)
val bool_to_string : bool -> string
val non            : ('a -> bool) -> 'a -> bool
val bool_compare   : bool * bool -> order

(* Pairs *)
val D       : 'a -> 'a * 'a
val Df      : ('a -> 'b) -> 'a * 'a -> 'b * 'b
val fst     : 'a * 'b -> 'a
val snd     : 'a * 'b -> 'b
val pair    : 'a -> 'b -> 'a * 'b
val swap    : 'a * 'b -> 'b * 'a
val curry   : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
val equal   : ''a -> ''a -> bool

(* State transformers *)
val unit   : 'a -> 's -> 'a * 's
val bind   : ('s -> 'a * 's) -> ('a -> 's -> 'b * 's) -> 's -> 'b * 's
val mmap   : ('a -> 'b) -> ('s -> 'a * 's) -> 's -> 'b * 's
val mjoin  : ('s -> ('s -> 'a * 's) * 's) -> 's -> 'a * 's
val mwhile : ('a -> bool) -> ('a -> 's -> 'a * 's) -> 'a -> 's -> 'a * 's

(* Lists: note we count elements from 0 *)
val cons         : 'a -> 'a list -> 'a list
val hd_tl        : 'a list -> 'a * 'a list
val append       : 'a list -> 'a list -> 'a list
val sing         : 'a -> 'a list
val first        : ('a -> 'b option) -> 'a list -> 'b option
val index        : ('a -> bool) -> 'a list -> int option
val maps         : ('a -> 's -> 'b * 's) -> 'a list -> 's -> 'b list * 's
val partial_maps : ('a -> 's -> 'b option * 's) -> 'a list -> 's -> 'b list * 's
val enumerate    : int -> 'a list -> (int * 'a) list
val zipwith      : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val zip          : 'a list -> 'b list -> ('a * 'b) list
val unzip        : ('a * 'b) list -> 'a list * 'b list
val cartwith     : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val cart         : 'a list -> 'b list -> ('a * 'b) list
val divide       : 'a list -> int -> 'a list * 'a list      (* Subscript *)
val update_nth   : ('a -> 'a) -> int -> 'a list -> 'a list  (* Subscript *)
val shared_map   : ('a -> 'a) -> 'a list -> 'a list  (* preserves sharing *)

(* Lists-as-sets *)
val mem       : ''a -> ''a list -> bool
val insert    : ''a -> ''a list -> ''a list
val delete    : ''a -> ''a list -> ''a list
val union     : ''a list -> ''a list -> ''a list
val intersect : ''a list -> ''a list -> ''a list
val subtract  : ''a list -> ''a list -> ''a list
val setify    : ''a list -> ''a list
val subset    : ''a list -> ''a list -> bool
val distinct  : ''a list -> bool

(* Comparisons *)
type 'a ordering = 'a * 'a -> order
val order_to_string : order -> string
val map_order       : ('a -> 'b) -> 'b ordering -> 'a ordering
val rev_order       : 'a ordering -> 'a ordering
val lex_order       : 'a ordering -> 'b ordering -> ('a * 'b) ordering
val lex_order2      : 'a ordering -> ('a * 'a) ordering
val lex_order3      : 'a ordering -> ('a * 'a * 'a) ordering
val lex_seq_order   : 'a ordering -> 'a ordering -> 'a ordering
val lex_list_order  : 'a ordering -> 'a list ordering

(* Sorting and searching *)
val min      : 'a ordering -> 'a list -> 'a * 'a list
val max      : 'a ordering -> 'a list -> 'a * 'a list
val merge    : 'a ordering -> 'a list -> 'a list -> 'a list
val sort     : 'a ordering -> 'a list -> 'a list
val sort_map : ('a -> 'b) -> 'b ordering -> 'a list -> 'a list
val top_sort : 'a ordering -> ('a -> 'a list) -> 'a list -> 'a list

(* Integers *)
val int_to_string : int -> string
val string_to_int : string -> int                 (* Overflow, Option *)
val int_to_bits   : int -> bool list
val bits_to_int   : bool list -> int              (* Overflow *)
val int_to_base64 : int -> char
val base64_to_int : char -> int
val interval      : int -> int -> int list
val even          : int -> bool
val odd           : int -> bool
val divides       : int -> int -> bool
val primes        : int -> int list
val gcd           : int -> int -> int

(* Strings *)
val rot         : int -> char -> char
val nchars      : char -> int -> string
val chomp       : string -> string
val unpad       : string -> string
val join        : string -> string list -> string
val split       : string -> string -> string list
val variant     : string -> string list -> string
val variant_num : string -> string list -> string
val dest_prefix : string -> string -> string
val is_prefix   : string -> string -> bool
val mk_prefix   : string -> string -> string
val align_table : {left : bool, pad : char} -> string list list -> string list

(* Reals *)
val real_to_string    : real -> string
val percent_to_string : real -> string
val pos               : real -> real
val log2              : real -> real              (* Domain *)

(* Pretty-printing *)
type 'a pp = ppstream -> 'a -> unit
val LINE_LENGTH : int ref
val pp_map      : ('a -> 'b) -> 'b pp -> 'a pp
val pp_bracket  : string -> string -> 'a pp -> 'a pp
val pp_sequence : string -> 'a pp -> 'a list pp
val pp_binop    : string -> 'a pp -> 'b pp -> ('a * 'b) pp
val pp_char     : char pp
val pp_string   : string pp
val pp_unit     : unit pp
val pp_bool     : bool pp
val pp_int      : int pp
val pp_real     : real pp
val pp_order    : order pp
val pp_porder   : order option pp
val pp_list     : 'a pp -> 'a list pp
val pp_pair     : 'a pp -> 'b pp -> ('a * 'b) pp
val pp_triple   : 'a pp -> 'b pp -> 'c pp -> ('a * 'b * 'c) pp
val to_string   : 'a pp -> 'a -> string           (* Uses LINE_LENGTH *)

(* Sum datatype *)
datatype ('a,'b) sum = INL of 'a | INR of 'b
val is_inl : ('a,'b) sum -> bool
val is_inr : ('a,'b) sum -> bool
val pp_sum : 'a pp -> 'b pp -> ('a,'b) sum pp

(* Maplets *)
datatype ('a,'b) maplet = |-> of 'a * 'b
val pp_maplet : 'a pp -> 'b pp -> ('a,'b) maplet pp

(* Trees *)
datatype ('a,'b) tree = BRANCH of 'a * ('a,'b) tree list | LEAF of 'b
val tree_size  : ('a,'b) tree -> {branches : int, leaves : int}
val tree_foldr : ('a -> 'c list -> 'c) -> ('b -> 'c) -> ('a, 'b) tree -> 'c
val tree_foldl : ('a->'c->'c) -> ('b->'c->'d) -> 'c -> ('a,'b) tree -> 'd list
val tree_partial_foldl :
  ('a->'c->'c option) -> ('b->'c->'d option) -> 'c -> ('a,'b) tree -> 'd list

(* mlibUseful impure features *)
val ==        : 'a * 'a -> bool  (* pointer equality *)
val memoize   : (unit -> 'a) -> unit -> 'a
val new_int   : unit -> int
val new_ints  : int -> int list
val uniform   : unit -> real
val coin_flip : unit -> bool
val with_flag : 'r ref * ('r -> 'r) -> ('a -> 'b) -> 'a -> 'b
val cached    : 'a ordering -> ('a -> 'b) -> 'a -> 'b

(* The environment *)
val host           : string
val date           : unit -> string
val today          : unit -> string
val warn           : string -> unit
val die            : string -> unit
val read_textfile  : {filename : string} -> string
val write_textfile : {filename : string, contents : string} -> unit

end
