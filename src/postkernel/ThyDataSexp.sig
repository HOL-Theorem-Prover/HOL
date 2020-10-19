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
          {export : t -> unit, segment_data : {thyname : string} -> t option}

val pp_sexp : Type.hol_type PP.pprinter -> Term.term PP.pprinter ->
              Thm.thm PP.pprinter -> t PP.pprinter

type 'a dec = t -> 'a option
val string_decode : string dec
val list_decode : 'a dec -> 'a list dec
val mk_list : ('a -> t) -> 'a list -> t

val pair_encode : ('a -> t) * ('b -> t) -> ('a * 'b) -> t
val pair_decode : 'a dec * 'b dec -> ('a * 'b) dec
val require_tag : string -> unit dec
val tag_encode : string -> ('a -> t) -> ('a -> t)
val tag_decode : string -> 'a dec -> 'a dec

val || : 'a dec * 'a dec -> 'a dec
val first : 'a dec list -> 'a dec

end
