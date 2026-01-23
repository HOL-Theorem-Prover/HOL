structure bnfBase_dtype =
struct

open Abbrev
type kname = KernelSig.kernelname

(* 'a is either thm, for when we look stuff up, or kname for when
   things are added. (Strings are simpler/smaller to store in .dat files
*)
datatype 'a info = bI of {
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
