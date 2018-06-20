signature TheoryGraph =
sig

  type t
  type thy = {thyname : string}
  val toThy : string -> thy
  exception NotFound of thy

  val thy_compare : thy * thy -> order
  val ancestors : t -> thy -> thy HOLset.set
  (* val strict_dominators_map : t -> (thy, thy HOLset.set) *)
  val empty : t
  val insert : thy * thy list -> t -> t
  val member : t -> thy -> bool
  val parents : t -> thy -> thy HOLset.set

  val current : unit -> t

end
