(* Moscow ML lacks a Word64 in its Basis, so the 64-bit-mask Bloom
   pre-check used in the Poly/ML build is not available here.  This
   degenerate implementation has `t = unit` and `maybeSubset` always
   returning true — i.e. the pre-check never rules anything out, and
   callers fall straight through to the real subset test.  Correct,
   just no speedup. *)
structure BloomApprox :> BloomApprox =
struct

open HolKernel

type t = unit
val empty : t = ()
fun from_term (_ : term) : t = ()
fun union (_ : t, _ : t) : t = ()
fun maybeSubset (_ : t, _ : t) : bool = true

end
