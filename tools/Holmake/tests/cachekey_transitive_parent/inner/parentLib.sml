(* A regular SML structure that re-exports parent_thm from
   parentTheory.  wrapping_childScript opens THIS, not parentTheory
   directly -- that's the structural element that hides parentTheory
   from wrapping_childScript's direct dep list, which is what makes
   the cachekey miss parentTheory's hash. *)
structure parentLib :> parentLib =
struct
  open parentTheory
  val parent_thm = parent_thm
end
