(* Database *)

datatype component = 
    Str					(* structure                       *)
  | Exc of string			(* exception constructor with name *)
  | Typ of string			(* type constructor with name      *)
  | Val of string			(* value with name                 *)
  | Con of string			(* value constructor with name	   *)
  | Term of string * string option	(* term and optional kind          *)

(* An entry consist of a component and the name of its structure: *)

type entry = { comp : component, file : string, line : int }

(* Table represented by ordered binary tree: *)

datatype 'contents table =
    Empty
  | Node of string * 'contents * 'contents table * 'contents table

(* The database is a table of sorted lists of entries: *)

type database = entry list table

val writebase : string * database -> unit
val readbase  : string -> database

val keycompare : string * string -> order
val lookup     : database * string -> entry list

(* Extract the name from an entry: *)

val getname : entry -> string
