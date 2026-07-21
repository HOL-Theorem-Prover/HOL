(*
 * Foundational type/term helpers shared across the whole Refute stack.
 *
 * This module deliberately depends only on the HOL kernel (Type, Term,
 * List), so it can be loaded by both the substrate layer (compiled for
 * refuteTableZooTheory) and the model-finder layer (compiled later into
 * refuteheap).  Layer-specific utilities live in Refute_ModelFinder_Util,
 * which re-exports these for the model-finder modules' convenience.
 *)

signature REFUTE_UTIL = sig
  val same_type : Type.hol_type -> Type.hol_type -> bool
  val member_type : Type.hol_type -> Type.hol_type list -> bool
  val add_type :
    Type.hol_type -> Type.hol_type list -> Type.hol_type list
  val aconv_member : Term.term -> Term.term list -> bool
  val distinct_terms : Term.term list -> Term.term list
end

structure Refute_Util :> REFUTE_UTIL = struct
  fun same_type left right = Type.compare (left, right) = EQUAL

  fun member_type ty = List.exists (same_type ty)

  fun add_type ty types =
    if member_type ty types then types else ty :: types

  fun aconv_member term = List.exists (Term.aconv term)

  fun distinct_terms terms =
    List.rev (List.foldl (fn (term, result) =>
      if aconv_member term result then result else term :: result) [] terms)
end
