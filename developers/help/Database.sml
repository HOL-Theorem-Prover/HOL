(* Database.sml *)

datatype component =
    Str					(* structure                       *)
  | Exc of string			(* exception constructor with name *)
  | Typ of string			(* type constructor with name      *)
  | Val of string			(* value with name                 *)
  | Con of string			(* value constructor with name	   *)
  | Term of string * string option	(* term and optional kind          *)

(* An entry consist of a component and the name of its structure: *)

type entry = { comp : component, file : string, line : int }

