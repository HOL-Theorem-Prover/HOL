structure bnfBase_dtype =
struct

open Abbrev
type kname = KernelSig.kernelname

(* 'a is either thm, for when we look stuff up, or kname for when
   things are added. (Strings are simpler/smaller to store in .dat files.)
*)
datatype 'a info = bI of {
  siblings : hol_type list, (* types I'm mutually recursive with *)
  map : term,               (* type's map term *)
  set : term list,          (* type's set terms *)
  gset : term,              (* type's "generic set term" *)
  relator : term,           (* type's rel term *)
  bnd : term,               (* type's ordinal bnd term *)
  mapID : 'a,               (* map id₁ .. idₙ = id theorem *)
  mapO : 'a,                (* map f₁ .. fₙ o map g₁ .. gₙ =
                               map (f₁ o g₁) ... (fₙ o gₙ) thm *)
  mapIMAGE : 'a list,       (* set₁ (map f₁ ... fₙ x) = IMAGE f₁ (set₁ x) etc *)
  gsetmap : 'a,             (* gset g₁ .. gₙ (map f₁ ... fₙ x) =
                                 gset (g₁ ∘ f₁) .. (gₙ ∘ fₙ) x *)
  gsetIMAGE : 'a,           (* IMAGE f (gset g₁ .. gₙ x) =
                                 gset (IMAGE f ∘ g₁) .. (IMAGE f ∘ gₙ) x *)
  mapCONG : 'a,             (* (!a1. a1 ∈ set₁ x ⇒ f₁ a1 = g₁ a1) ∧ ... ⇒
                               map f₁ .. fₙ x = map g₁ .. gₙ x *)
  bndthms : 'a list         (* !x. set₁ x ≼ bnd etc *)
}

(*

In all situations, functors have "genuine" type variable arguments with names
'a1, 'a2 etc.  Other ("constant") type variables have names 'b1, 'b2 etc.
These are written α₁, β₂, etc below.  ('c is γ, 'd is δ)

As user gets to choose names for them, there is no fixed naming scheme
for the constants.

Though the tyop is written below as if the αᵢ all come first, followed by the βⱼ,
this is not required and they can be intermingled as arguments to the operator.

map for (α₁, ... αₙ, β₁ ... βₙ) tyop is of form

   |- map (f₁ : α₁ → γ₁) ... (fₙ : αₙ → γₙ) (x : (α₁, ... αₙ, β₁ ... βₘ) tyop) =
        ... : (γ₁, ... γₙ, β₁ ... βₘ) tyop

set functions are of form (and occur in the set field's list in this order):

   |- set₁ (x : (α₁, ... αₙ, β₁ ... βₘ) tyop) = α₁ set
      .
      .
      .
   |- setₙ (x : (α₁, ... αₙ, β₁ ... βₘ) tyop) = αₙ set

generic set functions have type

   |- gset (f₁:α₁ -> γ set) ... (fₙ:αₙ -> γ set)
           (x : (α₁, ... αₙ, β₁ ... βₘ) tyop) : γ set =
        BIGUNION (IMAGE f₁ (set₁ x)) ∪
        ...
        BIGUNION (IMAGE fₙ (set₁ x))

mapO thm has form

   |- map (f₁ : γ₁ -> δ₁) ... (fₙ : γₙ -> δₙ) o
      map (g₁ : α₁ -> γ₁) ... (gₙ : αₙ -> γₙ) =
      map (f₁ o g₁) ... (fₙ o gₙ) :
        (α₁ ... αₙ, β₁ ... βₙ)tyop ->
        (δ₁ ... δₙ, β₁ ... βₙ)tyop


gsetmap has form

   |- gset (f₁ : γ₁ -> δ set) ... (fₙ : γₙ -> δ set)
        (map (g₁ : α₁ -> γ₁) ... (gₙ : αₙ -> γₙ) (x:(α₁,...,αₙ,β₁,...,βₘ)F) =
          gset (f₁ ∘ g₁) ... (fₙ ∘ gₙ) x

gsetIMAGE has form

   |- IMAGE (f : γ -> δ)
      (gset (g₁ : α₁ -> γ set) ... (gₙ : αₙ -> γ set) (x:(α₁,...,αₙ,β₁,...,βₘ)F)) =
      gset (IMAGE f ∘ g₁) ... (IMAGE f ∘ gₙ) x

*)

datatype bnftor =
         ftor of (kname * bnftor list)
       | the_arg
       | constty of hol_type
       | mutrec_var of string
       | previous_op of string

fun bnftor_toString b =
    case b of
        ftor(kn,bs) =>
        if kn = {Name ="sum", Thy = "sum"} then
          "(" ^ bnftor_toString (hd bs) ^ " + " ^
          bnftor_toString (hd (tl bs)) ^ ")"
        else if kn = {Name ="prod", Thy = "pair"} then
          "(" ^ bnftor_toString (hd bs) ^ " * " ^
          bnftor_toString (hd (tl bs)) ^ ")"
        else if kn = {Name = "fun", Thy = "min"} then
          "(" ^ bnftor_toString (hd bs) ^ " -> " ^
          bnftor_toString (hd (tl bs)) ^ ")"
        else
          "F{" ^ #Thy kn ^ "$" ^ #Name kn ^ ",[" ^
          String.concatWith "," (map bnftor_toString bs) ^
          "]}"
      | the_arg => "the_arg"
      | constty ty => "K(" ^ Parse.type_to_string ty ^ ")"
      | mutrec_var s => "Mutual(\"" ^ s ^ "\")"
      | previous_op s => "PrevOp(\"" ^ s ^ "\")"

end
