signature ThyDataSexp =
sig

datatype t =
         Int of int
       | String of string
       | SharedString of string
       | List of t list
       | Term of Term.term
       | Type of Type.hol_type
       | Thm of Thm.thm
       | Sym of string
       | Bool of bool
       | Char of char
       | Option of t option
       | KName of KernelSig.kernelname

val uptodate : t -> bool
val compare : t * t -> order

(* note that merge functions must take identical "types" on both sides.
   Thus, if the theory data is a list of values, both old and new should be
   lists and the merge will effectively be an append.  If there's just one
   value being "merged", it should still be a singleton list.

   Similarly, if the data is a dictionary, represented as an alist, then the
   new data (representing a single key-value maplet) should be a singleton
   alist
*)
val alist_merge : {old: t, new : t} -> t
val append_merge : {old : t, new : t} -> t

val new : {thydataty : string,
           merge : {old : t, new : t} -> t,
           load : {thyname : string, data : t option} -> unit,
           other_tds : t * TheoryDelta.t -> t option} ->
          {export : t -> unit, segment_data : {thyname : string} -> t option,
           set : t -> unit}

val pp_sexp : Type.hol_type PP.pprinter -> Term.term PP.pprinter ->
              Thm.thm PP.pprinter -> t PP.pprinter

type 'a dec = t -> 'a option
type 'a enc = 'a -> t

val string_decode : string dec
val int_decode    : int dec
val type_decode   : Type.hol_type dec
val term_decode   : Term.term dec
val char_decode   : char dec
val list_decode   : 'a dec -> 'a list dec
val kname_decode  : KernelSig.kernelname dec
val bool_decode   : bool dec

val mk_list : 'a enc -> 'a list enc

val option_encode : 'a enc -> 'a option enc
val option_decode : 'a dec -> 'a option dec

val pair_encode : 'a enc * 'b enc -> ('a * 'b) enc
val pair_decode : 'a dec * 'b dec -> ('a * 'b) dec

val pair3_encode : 'a enc * 'b enc * 'c enc -> ('a * 'b * 'c) enc
val pair3_decode : 'a dec * 'b dec * 'c dec -> ('a * 'b * 'c) dec

val pair4_encode : 'a enc * 'b enc * 'c enc * 'd enc -> ('a * 'b * 'c * 'd) enc
val pair4_decode : 'a dec * 'b dec * 'c dec * 'd dec -> ('a * 'b * 'c * 'd) dec

val require_tag : string -> unit dec
val tag_encode : string -> ('a -> t) -> ('a -> t)
val tag_decode : string -> 'a dec -> 'a dec

val || : 'a dec * 'a dec -> 'a dec
val >> : 'a dec * ('a -> 'b) -> 'b dec
val first : 'a dec list -> 'a dec

end
