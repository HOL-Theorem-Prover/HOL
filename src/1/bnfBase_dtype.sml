structure bnfBase_dtype =
struct

open Abbrev
type kname = KernelSig.kernelname

(* 'a is either thm, for when we look stuff up, or kname for when
   things are added. (Strings are simpler/smaller to store in .dat files
*)
datatype 'a info = bI of {
  ty : hol_type,
  siblings : hol_type list,  (* types I'm mutually recursive with *)
  map : term * 'a,          (* type's map term and its def'n thm *)
  set : (term * 'a) list,   (* type's set term and its def'n thm *)
  relator : term * 'a,      (* type's rel term and its def'n thm *)
  bnd : term                 (* type's ordinal bnd term and its def'n thm *)
}

(*

map for (α₁, ... αₙ) tyop is of form

   |- map (f₁ : α₁ → β₁) ... (fₙ : αₙ → βₙ) (x : (α₁, ... αₙ) tyop) =
        ... : (β₁, ... βₙ) tyop

set functions are of of form

   |- set₁ (x : (α₁, ... αₙ) tyop) = α₁ set
      .
      .
      .
   |- setₙ (x : (α₁, ... αₙ) tyop) = αₙ set

*)

end
