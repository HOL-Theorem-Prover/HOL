(*****************************************************************************)
(* Varmap.sml                                                                *)
(* ---------------------                                                     *)
(*                                                                           *)
(* Definition of type varmap and various operations on it                    *)
(*                                                                           *)
(*****************************************************************************)
(*                                                                           *)
(* Revision history:                                                         *)
(*                                                                           *)
(*   Thu Oct  4 15:45:52 BST 2001 -- created file                            *)
(*   Thu Nov 15 17:07:37 GMT 2001 -- added unify                             *)
(*   Thu Mar 28 09:40:05 GMT 2002 -- added signature file                    *)
(*                                                                           *)
(*****************************************************************************)

structure Varmap :> Varmap = struct

(*
load "Binarymap";
*)

local

open Binarymap;

open HolKernel Parse boolLib BasicProvers

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

in

(*****************************************************************************)
(* A value of ML type term_bdd represents a judgement                        *)
(*                                                                           *)
(*    vm tm |--> bdd                                                         *)
(*                                                                           *)
(* where vm is a variable map, tm a term and bdd a BDD                       *)
(*                                                                           *)
(* A variable map associates BuDDy BDD variables (which are represented      *)
(* as numbers) to HOL variables. Variable maps are represented as            *)
(* dictionaries from the Moscow ML Library structure Binarymap.              *)
(*****************************************************************************)


(*****************************************************************************)
(*                  START OF DEFINITION OF varmap                            *)
(*****************************************************************************)

type varmap = (string, int) Binarymap.dict;

(*****************************************************************************)
(* Create an empty var_map                                                   *)
(*****************************************************************************)

val empty = Binarymap.mkDict String.compare : (string, int) Binarymap.dict;

(*****************************************************************************)
(* Compute number of entries in a varmap                                     *)
(*****************************************************************************)

fun size (vm:varmap) = Binarymap.numItems vm;

(*****************************************************************************)
(* See if name is mapped to anything in a varmap.                           *)
(* Return SOME n if name mapped to n, or NONE if not in the table            *)
(*****************************************************************************)

fun peek (vm:varmap) name = Binarymap.peek(vm,name);

(*****************************************************************************)
(* Explode a varmap into a list of string/int pairs                          *)
(*****************************************************************************)

fun dest (vm:varmap) = Binarymap.listItems vm;

(*****************************************************************************)
(* Insert a new entry in a varmap                                            *)
(*****************************************************************************)

fun insert (s,n) (vm:varmap) = Binarymap.insert(vm, s, n);

(*****************************************************************************)
(* Test pointer equality of varmaps                                          *)
(*****************************************************************************)

val eq = Portable.pointer_eq : varmap*varmap->bool;

(*****************************************************************************)
(* Test whether vm2 extends vm1                                              *)
(* (i.e. every entry in vm1 is also in vm2)                                  *)
(*****************************************************************************)

fun extends (vm1:varmap) (vm2:varmap) =
 eq(vm1,vm2)
  orelse Binarymap.foldl
          (fn (s,n,bv) => bv andalso (case Binarymap.peek(vm2,s) of
                                         SOME m => (m=n)
                                       | NONE   => false))
          true
          vm1;


(*****************************************************************************)
(* Compute smallest varmap vm such that extends vm1 vm and extends vm2 vm.   *)
(* Raises unifyVarmapError if vm1 and vm2 are incompatible.                  *)
(*****************************************************************************)

exception unifyVarmapError;

val unify =
 Binarymap.foldl
  (fn (v,n,vm) => case Binarymap.peek(vm:varmap, v) of
                     SOME n' => if n=n' then vm else raise unifyVarmapError
                   | NONE    => Binarymap.insert(vm,v,n));

(*****************************************************************************)
(* remove s vm removes entry for string s from vm                            *)
(* (identity if no entry for s in vm)                                        *)
(*****************************************************************************)

fun remove s (vm:varmap) =
 fst(Binarymap.remove(vm,s)) handle NotFound => vm;

(*****************************************************************************)
(*                    END OF DEFINITION OF varmap                            *)
(*****************************************************************************)

end;

end
