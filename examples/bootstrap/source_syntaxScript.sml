Theory source_syntax
Ancestors
  arithmetic list pair finite_map string source_values


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
