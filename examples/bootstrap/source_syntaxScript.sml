
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory;

val _ = new_theory "source_syntax";


(* abstract syntax *)

Type name = “:num”

Datatype:
  op = Add | Sub | Div | Cons | Head | Tail | Read | Write
End

Datatype:
  test = Less | Equal
End

Datatype:
  exp = Const num                   (* constant number            *)
      | Var name                    (* local variable             *)
      | Op op (exp list)            (* primitive operations       *)
      | If test (exp list) exp exp  (* if test .. then .. else .. *)
      | Let name exp exp            (* let name = .. in ..        *)
      | Call name (exp list)        (* call a function            *)
End

Datatype:
  dec = Defun name (name list) exp   (* func name, formal params, body *)
End

Datatype:                         (* a complete program is a list of   *)
  prog = Program (dec list) exp   (* function declarations followed by *)
End                               (* an expression to evaluate         *)


val _ = export_theory();
