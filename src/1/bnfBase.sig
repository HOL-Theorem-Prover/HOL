signature bnfBase =
sig

  include Abbrev
  type t (* for "pure" manipulations *)
  datatype info = datatype bnfBase_dtype.info
  datatype bnftor = datatype bnfBase_dtype.bnftor

  val pure_lookup : t -> hol_type -> thm info option

  val thy_lookup : {thyname:string} -> t option
  val fullDB : unit -> t
  val updateDB : (hol_type * KernelSig.kernelname info) -> unit

end
