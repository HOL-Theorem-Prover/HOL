structure bnfBase_dtype =
struct

open Abbrev
type kname = KernelSig.kernelname

(* 'a is either thm, for when we look stuff up, or kname for when
   things are added. (Strings are simpler/smaller to store in .dat files.)
*)
datatype 'a info = bI of {
  bnd : term,               (* type's bounding set *)
  bndthms : 'a list,        (* !x. set₁ x ≼ B etc *)

  canontype : hol_type,     (* canonical expression of type, see below *)

  map : term,               (* type's map term *)
  mapCONG : 'a,             (* (!a1. a1 ∈ set₁ x ⇒ f₁ a1 = g₁ a1) ∧ ... ⇒
                               map f₁ .. fₙ x = map g₁ .. gₙ x *)
  mapID : 'a,               (* map id₁ .. idₙ = id theorem *)
  mapIMAGE : 'a list,       (* set₁ (map f₁ ... fₙ x) = IMAGE f₁ (set₁ x) etc *)
  mapO : 'a,                (* map f₁ .. fₙ o map g₁ .. gₙ =
                               map (f₁ o g₁) ... (fₙ o gₙ) thm *)
  relator : term,           (* type's rel term *)
  set : term list,          (* type's set terms *)

  wits : (term * 'a) list,  (* nonemptiness witnesses; see below *)
  inhabits : (term * 'a) list (* set₁ is inhabited, ...; see below *)
}

(*

In all situations, functors have "genuine" type variable arguments with names
'a1, 'a2 etc.  Other ("constant") type variables have names 'b1, 'b2 etc.
These are written α₁, β₂, etc below.  ('c is γ, 'd is δ)
This is the "canonical" type.

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

Nonemptiness witnesses (the wits field) come in (term,theorem) pairs.  The
term always takes one argument per genuine type variable, whether or not
it uses it, so is of type

   wit : α₁ -> ... -> αₙ -> (α₁, ... αₙ, β₁ ... βₘ) tyop

and its theorem records, for each i, whether the witness needed an αᵢ:

   |- !a₁ ... aₙ. set₁ (wit a₁ ... aₙ) ⊆ W₁ ∧ ... ∧ setₙ (wit a₁ ... aₙ) ⊆ Wₙ

where each Wᵢ is either ∅ (the witness doesn't need an αᵢ) or {aᵢ} (it
does).  Reading the term as a proof of nonemptiness in the style of the
Curry-Howard correspondence, wit says: given elements of those αᵢ whose
Wᵢ is a singleton, here is an element of the type.  A witness with more
∅s is a stronger claim; the whole list is kept because the strongest
witness depends on which arguments turn out to be inhabited (see
Blanchette, Popescu and Traytel, "Witnessing (Co)datatypes", ESOP 2015).

The inhabits field holds one (term,theorem) pair per set function, saying
that setᵢ is not always empty, and in the strong form that lets a
composite functor's nontriviality be built out of its components':

   inhabitᵢ : αᵢ -> (α₁, ... αₙ, β₁ ... βₘ) tyop
   |- !v. v ∈ setᵢ (inhabitᵢ v)

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
