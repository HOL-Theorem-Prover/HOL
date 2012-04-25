(* ===================================================================== *)
(*                                                                       *)
(* FILE          : quotient.sig                                          *)
(* VERSION       : 2.2                                                   *)
(* DESCRIPTION   : Functions for creating a quotient type.               *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : April 15, 2005                                        *)
(* COPYRIGHT     : Copyright (c) 2005 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


signature quotient =
sig

(* =================================================================== *)
(*           Q U O T I E N T   T Y P E S   D E F I N E D               *)
(* =================================================================== *)

(* ------------------------------------------------------------------- *)
(* This file defines the function "define_quotient_type", which takes  *)
(* an existing type and theorems about it, along with a theorem about  *)
(* an equivalence relation on the type, and creates a new type which   *)
(* is isomorphic to the equivalence classes of the old type.           *)
(* In addition to creating the new type, functions are defined in the  *)
(* HOL logic to translate between the old and new types in both        *)
(* directions.                                                         *)
(*                                                                     *)
(* The arguments to "define_quotient_type" includes a theorem which    *)
(* ->implies<- that the equivalence relation is in fact reflexive,     *)
(* symmetric, and transitive.  These properties all follow from        *)
(*      |- !x y. EQUIV x y = (EQUIV x = EQUIV y)                       *)
(*                                                                     *)
(* The "define_quotient_type" function returns a theorem of the form   *)
(*      |- (!a. abs(rep a) = a) /\                                     *)
(*         (!r r'. EQUIV r r' = (abs r = abs r'))                      *)
(*                                                                     *)
(* We call theorems of this form "quotient theorems"; they are used    *)
(* a good deal as inputs to or results from other functions in this    *)
(* package.                                                            *)
(* ------------------------------------------------------------------- *)

val chatting : bool ref (* default is false, no trace of quotient operation *)

val caching  : bool ref (* default is true, do cache quotient thms for speed *)

val reset_cache : unit -> unit
val list_cache  : unit -> (Type.hol_type * Thm.thm) list

val define_quotient_type :
        string ->      (* name of new quotient type *)
        string ->      (* name of abstraction function from old to new *)
        string ->      (* name of representation function from new to old *)
        Thm.thm ->     (* equivalence or partial equivalence theorem *)
        Thm.thm        (* returns one theorem:

              abs of rep is identity /\
              equivalence is equality of abs
*)


(* Equivalence theorems have the form:

              !x y. R x y = (R x = R y)

   Here are routines to create equivalence theorems,
   and to convert them into theorems of
   reflexivity, symmetry, and transitivity.              *)

val equiv_refl :
        Thm.thm ->     (* equivalence theorem *)
        Thm.thm        (* returns reflexivity theorem for equivalence:

              !x. R x x
*)

val equiv_sym :
        Thm.thm ->     (* equivalence theorem *)
        Thm.thm        (* returns symmetry theorem for equivalence:

              !x y. R x y ==> R y x
*)

val equiv_trans :
        Thm.thm ->     (* equivalence theorem *)
        Thm.thm        (* returns transitivity theorem for equivalence:

              !x y z. R x y /\ R y z ==> R y x
*)

val refl_sym_trans_equiv :
        Thm.thm ->     (* reflexivity theorem *)
        Thm.thm ->     (* symmetry theorem *)
        Thm.thm ->     (* transitivity theorem *)
        Thm.thm        (* returns equivalence theorem:

              !x y. R x y = (R x = R y)
*)

val identity_equiv :
        Type.hol_type -> (* type, whose equivalence relation is equality *)
        Thm.thm        (* returns identity equivalence theorem for type:

              !x y. $= x y = ($= x = $= y)
*)

val pair_equiv :
        Thm.thm ->     (* equivalence theorem for left element of pair *)
        Thm.thm ->     (* equivalence theorem for right element of pair *)
        Thm.thm        (* returns equivalence theorem for pair:

              !x y. (R1 ### R2) x y = ((R1 ### R2) x = (R1 ### R2) y)
*)

val sum_equiv :
        Thm.thm ->     (* equivalence theorem for left element of sum *)
        Thm.thm ->     (* equivalence theorem for right element of sum *)
        Thm.thm        (* returns equivalence theorem for sum:

              !x y. (R1 +++ R2) x y = ((R1 +++ R2) x = (R1 +++ R2) y)
*)

val list_equiv :
        Thm.thm ->     (* equivalence theorem for element of list *)
        Thm.thm        (* returns equivalence theorem for list:

              !x y. LIST_REL R x y = (LIST_REL R x = LIST_REL R y)
*)

val option_equiv :
        Thm.thm ->     (* equivalence theorem for element of option *)
        Thm.thm        (* returns equivalence theorem for option:

              !x y. OPTION_REL R x y = (OPTION_REL R x = OPTION_REL R y)
*)

val make_equiv :
        Thm.thm list ->  (* base equivalence theorems *)
        Thm.thm list ->  (* polymorphic type operator equivalence theorems *)
        Type.hol_type -> (* type, whose equivalence relation is desired *)
        Thm.thm          (* returns equivalence theorem for hol_type:

              !x y. R x y = (R x = R y)
*)


(* Quotient theorems have the form:

              (!a. abs (rep a) = a) /\
              (|x y. R x y = (abs x = abs y))

   These are returned by define_quotient_type.
   Here are more routines to create quotient theorems.  *)

val identity_quotient :
        Type.hol_type -> (* type, whose equivalence relation is equality *)
        Thm.thm        (* returns identity quotient theorem for type:

              (!a. I (I a) = a) /\
              (|x y. $= x y = (I x = I y))
*)

val pair_quotient :
        Thm.thm ->     (* quotient theorem for left element of pair *)
        Thm.thm ->     (* quotient theorem for right element of pair *)
        Thm.thm        (* returns quotient theorem for pair:

              (!a. (abs1 ## abs2) ((rep1 ## rep2) a) = a) /\
              (|x y. (R1 ### R2) x y = ((abs1 ## abs2) x = (abs1 ## abs2) y))
*)

val sum_quotient :
        Thm.thm ->     (* quotient theorem for left element of sum *)
        Thm.thm ->     (* quotient theorem for right element of sum *)
        Thm.thm        (* returns quotient theorem for sum:

              (!a. (abs1 ++ abs2) ((rep1 ++ rep2) a) = a) /\
              (|x y. (R1 +++ R2) x y = ((abs1 ++ abs2) x = (abs1 ++ abs2) y))
*)

val list_quotient :
        Thm.thm ->     (* quotient theorem for element of list *)
        Thm.thm        (* returns quotient theorem for list:

              (!a. MAP abs (MAP rep a) = a) /\
              (|x y. LIST_REL R x y = (MAP abs x = MAP abs y))
*)

val option_quotient :
        Thm.thm ->     (* quotient theorem for base type of option *)
        Thm.thm        (* returns quotient theorem for option:

              (!a. OPTION_MAP abs (OPTION_MAP rep a) = a) /\
              (|x y. OPTION_REL R x y = (OPTION_MAP abs x = OPTION_MAP abs y))
*)

val fun_quotient :
        Thm.thm ->     (* quotient theorem for domain of function *)
        Thm.thm ->     (* quotient theorem for range of function *)
        Thm.thm        (* returns quotient theorem for function:

          (!a. (rep1 --> abs2) ((abs1 --> rep2) a) = a) /\
          (|f g. (rep1 =-> abs2) f g = ((rep1 --> abs2) f = (rep1 --> abs2) g))
*)

val make_quotient :
        Thm.thm list ->  (* quotient theorems for primary lifted types *)
        Thm.thm list ->  (* conditional quotient ths for type operators *)
        Type.hol_type -> (* type (not lifted) of desired quotient *)
        Thm.thm        (* returns quotient theorem for given type:

              (!a. abs (rep a) = a) /\
              (|x y. R x y = (abs x = abs y))
*)



val define_quotient_lifted_function :
        Thm.thm list -> (* quotient thms, e.g. from define_quotient_type *)
        Thm.thm list ->             (* conditional quotient ths for type ops*)
        Thm.thm list ->             (* rel & map simplifications for type ops*)
        {def_name : string,         (* name to store the definition under *)
         fname : string,            (* name of new function *)
         func : Term.term,          (* old function, to be lifted *)
         fixity : Parse.fixity option} ->  (* fixity of new function *)
        Thm.thm                     (* definition of a new lifted function *)


(*
val regularize :
        Term.term ->    (* term to be lifted, may not be regular *)
        Term.term       (* version of input term, that is now regular *)


val REGULARIZE :
        Thm.thm ->      (* theorem to be lifted, may not be regular *)
        Thm.thm         (* version of input theorem, that is now regular *)
*)


val lift_theorem_by_quotients :
        Thm.thm list -> (* quotient thms, e.g. from define_quotient_type *)
        Thm.thm list -> (* equivalence thms, e.g. from user or make_equiv *)
        Thm.thm list -> (* above + conditional equivalence thms for type ops *)
        Thm.thm list -> (* conditional quotient ths for type ops *)
        Thm.thm list -> (* simplification ths for rel/map idents of type ops *)
        Thm.thm list -> (* new function definitions formed by d_q_l_f *)
        Thm.thm list -> (* old functions are well-defined to respect the
                           equivalence relations mentioned above *)
        Thm.thm list -> (* polymorphic function definitions on quotient types
                           as lifted from instanciations on old types,
                           for all quotient theorems *)
        Thm.thm list -> (* polymorphic functions are well-defined to respect
                           all quotient theorems *)
        Thm.thm ->      (* theorem (regarding old functions) to be lifted *)
        Thm.thm         (* lifted version of previous theorem *)



(*---------------------------------------------------------------------------*)
(* Main function of package: define_equivalence_types                        *)
(*                                                                           *)
(* Defines a type of equivalence classes, and transfers a list of            *)
(* functions and theorems about the representatives over to the new type.    *)
(* It returns a list of the transferred theorems.                            *)
(*                                                                           *)
(* types    - list of records of two fields:                                 *)
(*                                                                           *)
(*   name     - desired name of new type                                     *)
(*   equiv    - Theorem that R is an equivalence relation; in the form:      *)
(*               |- !x y. x R y = (R x = R y)                                *)
(*                                                                           *)
(* tyops    - list of conditional quotient theorems; in the form:            *)
(*               |- !R1 (abs1:'a1->'b1) rep1 ... Rn (absn:'an->'bn) repn.    *)
(*                   (!a:'b1. abs1 (rep1 a) = a) /\                          *)
(*                   (|(r:'a1) (r':'a1). R1 r r' = (abs1 r = abs1 r')) ==>   *)
(*                   ...                                                     *)
(*                   (!a:'bn. absn (repn a) = a) /\                          *)
(*                   (|(r:'an) (r':'an). Rn r r' = (absn r = absn r')) ==>   *)
(*                   (!a:('b1,...,'bn)tyop.                                  *)
(*                         F abs1 ... absn (F rep1 ... repn a) = a) /\       *)
(*                   (|(r:('a1,...,'an)tyop) (r':('a1,...,'an)tyop).         *)
(*                         R R1 ... Rn r r' =                                *)
(*                           (F abs1 ... absn r = F abs1 ... absn r'))       *)
(*             where F and R are predefined constants in the logic.          *)
(*                                                                           *)
(*                                                                           *)
(* defs     - list of records of four fields:                                *)
(*                                                                           *)
(*   def_name - string, name of theorem stored in current theory             *)
(*   fname    - string, name of the new function defined in HOL logic        *)
(*   func     - term, the old term which is to be lifted                     *)
(*   fixity   - Parse.fixity, gives the parsing status of the new function   *)
(*                                                                           *)
(* respects - list of theorems asserting that the old functions are          *)
(*            welldefined;  of the form                                      *)
(*                       |- (R1 x1 y1) /\ .. /\ (Rn xn yn) ==>               *)
(*                             R (f x1 .. xn) (f y1 .. yn)                   *)
(*            where "R[i]" becomes "=" for types other than the              *)
(*            representing types.                                            *)
(*                                                                           *)
(* poly_preserves - list of theorems asserting that polymorphic functions    *)
(*            apply to lifted values as they did to representing values;     *)
(*            of the form                                                    *)
(*                       |- ((!a. abs1 (rep1 a) = a) /\                      *)
(*                           (!x y. R1 x y = (abs1 x = abs1 y)) ==>          *)
(*                          ... ==>                                          *)
(*                          ((!a. absk (repk a) = a) /\                      *)
(*                           (!x y. Rk x y = (absk x = absk y)) ==>          *)
(*                          (!x1 ... xn.                                     *)
(*                            f x1 ... xn = abs (f (rep1 x1) ... (repn xn))) *)
(*            where "R[i]" becomes "=" and "abs[i]" or "rep[i]" becomes "I"  *)
(*            for types other than the representing types.                   *)
(*            The k antecedents need not include duplicates, and may be in   *)
(*            any order, so long as all argument and return value types      *)
(*            of f are represented.                                          *)
(*                                                                           *)
(* poly_respects - list of theorems asserting that polymorphic functions     *)
(*            respect the equivalence relations;  of the form                *)
(*                       |- ((!a. abs1 (rep1 a) = a) /\                      *)
(*                           (!x y. R1 x y = (abs1 x = abs1 y)) ==>          *)
(*                          ... ==>                                          *)
(*                          ((!a. absk (repk a) = a) /\                      *)
(*                           (!x y. Rk x y = (absk x = absk y)) ==>          *)
(*                          (R1 x1 y1) /\ .. /\ (Rn xn yn) ==>               *)
(*                             R (f x1 .. xn) (f y1 .. yn)                   *)
(*            where "R[i]" becomes "=" and "abs[i]" or "rep[i]" becomes "I"  *)
(*            for types other than the representing types.                   *)
(*            The k antecedents need not include duplicates, and may be in   *)
(*            any order, so long as all argument and return value types      *)
(*            of f are represented.                                          *)
(*                                                                           *)
(* old_thms - list of theorems about the old functions, on the old types     *)
(*                                                                           *)
(* Restrictions:                                                             *)
(*                                                                           *)
(*  * R[i] must be an equivalence relation over the whole types, no subsets. *)
(*                                                                           *)
(*  * All original functions must be curried (as are the new ones).          *)
(*                                                                           *)
(*  * The theorems must have all variables bound by existential or           *)
(*    universal quantifiers.                                                 *)
(*                                                                           *)
(*  * The theorems must be obviously `well-defined', i.e. invariant under    *)
(*    substitution [t/u] whenever |- t R[i] u. Essentially "R[i]" becomes    *)
(*    "=" and  old functions become the new ones.                            *)
(*                                                                           *)
(*  * All arguments/results of the representing type will be transferred     *)
(*    to the new type.                                                       *)
(*                                                                           *)
(* Original Author: John Harrison                                            *)
(* Revised and extended to lift second-order theorems: Peter V. Homeier      *)
(*---------------------------------------------------------------------------*)

(* MAIN ENTRY POINT: *)

val define_quotient_types :
        {types: {name:string,          (* name of new quotient type *)
                 equiv:Thm.thm} list,  (* relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         tyop_equivs: Thm.thm list,  (* conditional equiv ths for type ops *)
         tyop_quotients: Thm.thm list,(*conditional quotient ths for type ops*)
         tyop_simps: Thm.thm list, (* rel/map simplification ths for type ops*)
         respects : Thm.thm list,    (* old functions respect equivalence *)
         poly_preserves : Thm.thm list, (* polymorphic fns are preserved
                                           by quotients *)
         poly_respects : Thm.thm list,(* polymorphic fns respect equivalence *)
         old_thms : Thm.thm list} -> (* theorems of old fns to be lifted *)
        Thm.thm list                 (* new lifted theorems *)

(* ALTERNATE ENTRY POINT: *)

val define_quotient_types_rule :
        {types: {name:string,          (* name of new quotient type *)
                 equiv:Thm.thm} list,  (* relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         tyop_equivs: Thm.thm list,  (* conditional equiv ths for type ops *)
         tyop_quotients: Thm.thm list,(*conditional quotient ths for type ops*)
         tyop_simps: Thm.thm list, (* rel/map simplification ths for type ops*)
         respects : Thm.thm list,    (* old functions respect equivalence *)
         poly_preserves : Thm.thm list, (* polymorphic fns are preserved
                                           by quotients *)
         poly_respects : Thm.thm list} ->
                                     (* polymorphic fns respect equivalence *)
        (Thm.thm -> Thm.thm)          (* rule for lifting theorems *)

(* MAIN ENTRY POINT INCLUDING STANDARD THEOREMS: *)

val define_quotient_types_full :
        {types: {name:string,          (* name of new quotient type *)
                 equiv:Thm.thm} list,  (* relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         tyop_equivs: Thm.thm list,  (* conditional equiv ths for type ops *)
         tyop_quotients: Thm.thm list,(*conditional quotient ths for type ops*)
         tyop_simps: Thm.thm list, (* rel/map simplification ths for type ops*)
         respects : Thm.thm list,    (* old functions respect equivalence *)
         poly_preserves : Thm.thm list, (* polymorphic fns are preserved
                                           by quotients *)
         poly_respects : Thm.thm list,(* polymorphic fns respect equivalence *)
         old_thms : Thm.thm list} -> (* theorems of old fns to be lifted *)
        Thm.thm list                 (* new lifted theorems *)

(* ALTERNATE ENTRY POINT INCLUDING STANDARD THEOREMS: *)

val define_quotient_types_full_rule :
        {types: {name:string,          (* name of new quotient type *)
                 equiv:Thm.thm} list,  (* relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         tyop_equivs: Thm.thm list,  (* conditional equiv ths for type ops *)
         tyop_quotients: Thm.thm list,(*conditional quotient ths for type ops*)
         tyop_simps: Thm.thm list, (* rel/map simplification ths for type ops*)
         respects : Thm.thm list,    (* old functions respect equivalence *)
         poly_preserves : Thm.thm list, (* polymorphic fns are preserved
                                           by quotients *)
         poly_respects : Thm.thm list} ->
                                     (* polymorphic fns respect equivalence *)
        (Thm.thm -> Thm.thm)          (* rule for lifting theorems *)

(* MAIN ENTRY POINT WITH JUST STANDARD THEOREMS: *)
(* This is a quick, simple entry point if the only type operators involved are
   the list, pair, sum, option, and function ones, and no new polymorphic
   operators need to have their respectfulness or preservation proven.   *)

val define_quotient_types_std :
        {types: {name:string,          (* name of new quotient type *)
                 equiv:Thm.thm} list,  (* relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         respects : Thm.thm list,    (* old functions respect equivalence *)
         old_thms : Thm.thm list} -> (* theorems of old fns to be lifted *)
        Thm.thm list                 (* new lifted theorems *)

(* ALTERNATE ENTRY POINT WITH JUST STANDARD THEOREMS: *)

val define_quotient_types_std_rule :
        {types: {name:string,          (* name of new quotient type *)
                 equiv:Thm.thm} list,  (* relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         respects : Thm.thm list} ->   (* old functions respect equivalence *)
        (Thm.thm -> Thm.thm)          (* rule for lifting theorems *)

(* For backwards compatibility with John Harrison's package: *)

val define_equivalence_type :
        {name : string,              (* name of new quotient type *)
         equiv : Thm.thm,            (* thm that relation is an equivalence *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         welldefs : Thm.thm list,    (* old functions respect equivalence *)
         old_thms : Thm.thm list} -> (* theorems of old fns to be lifted *)
        Thm.thm list                 (* definitions of new lifted functions *)

(* MAIN ENTRY POINT FOR SUBSET TYPE: *)

val define_subset_types :
        {types: {name:string,          (* name of new subset type *)
                 inhab:Thm.thm} list,  (* predicate is inhabited *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         tyop_equivs: Thm.thm list,  (* conditional equiv ths for type ops *)
         tyop_quotients: Thm.thm list,(*conditional quotient ths for type ops*)
         tyop_simps: Thm.thm list, (* rel/map simplification ths for type ops*)
         inhabs : Thm.thm list,    (* old functions respect inhabitation *)
         poly_preserves : Thm.thm list, (* polymorphic fns are preserved
                                           by quotients *)
         poly_respects : Thm.thm list,(* polymorphic fns respect equivalence *)
         old_thms : Thm.thm list} -> (* theorems of old fns to be lifted *)
        Thm.thm list                 (* new lifted theorems *)

val define_subset_types_rule :
        {types: {name:string,          (* name of new subset type *)
                 inhab:Thm.thm} list,  (* predicate is inhabited *)
         defs: {def_name:string,            (* name of stored definition *)
                fname:string,               (* name of new lifted function *)
                func:Term.term,             (* old function to be lifted *)
                fixity: Parse.fixity option} list, (* fixity of new function *)
         tyop_equivs: Thm.thm list,  (* conditional equiv ths for type ops *)
         tyop_quotients: Thm.thm list,(*conditional quotient ths for type ops*)
         tyop_simps: Thm.thm list, (* rel/map simplification ths for type ops*)
         inhabs : Thm.thm list,    (* old functions respect inhabitation *)
         poly_preserves : Thm.thm list, (* polymorphic fns are preserved
                                           by quotients *)
         poly_respects : Thm.thm list (* polymorphic fns respect equivalence *)
        } ->
        Thm.thm ->             (* theorem of old fns to be lifted *)
        Thm.thm                (* new lifted theorem *)


end;  (* of signature quotient *)
