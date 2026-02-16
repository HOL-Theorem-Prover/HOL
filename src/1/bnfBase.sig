signature bnfBase =
sig

  include Abbrev
  type t (* for "pure" manipulations *)
  type key = KernelSig.kernelname
  datatype info = datatype bnfBase_dtype.info
  datatype bnftor = datatype bnfBase_dtype.bnftor


  val pure_lookup : t -> key -> thm info option

  val thy_lookup : {thyname:string} -> t option
  val fullDB : unit -> t
  val updateDB : (key * KernelSig.kernelname info) -> unit

end
