signature bnfBase =
sig

  include Abbrev
  type t (* for "pure" manipulations *)
  type key = KernelSig.kernelname
  datatype info = datatype bnfBase_dtype.info
  datatype bnftor = datatype bnfBase_dtype.bnftor


  val pure_lookup : t -> key -> thm info option

  (* Extending a database in memory, without recording anything in the
     theory.  A caller that has just built a functor's theorems — the
     fixed point it defined a moment ago, say — can hand them straight
     to the next step, rather than the next step having to look them up.
     Nothing about an intermediate product needs to be registered. *)
  val pure_insert : (key * thm info) -> t -> t

  val thy_lookup : {thyname:string} -> t option
  val fullDB : unit -> t
  val updateDB : (key * KernelSig.kernelname info) -> unit

end
