signature Refute_PropSat = sig
  datatype prop_formula =
      True
    | False
    | BoolVar of int  (* indices must be positive *)
    | Not of prop_formula
    | Or of prop_formula * prop_formula
    | And of prop_formula * prop_formula

  type assignment = int -> bool option
  datatype result =
      SATISFIABLE of assignment
    | UNSATISFIABLE

  exception INVALID_VARIABLE of int

  val SNot : prop_formula -> prop_formula
  val SOr : prop_formula * prop_formula -> prop_formula
  val SAnd : prop_formula * prop_formula -> prop_formula

  val indices : prop_formula -> int list
  val exists : prop_formula list -> prop_formula
  val all : prop_formula list -> prop_formula

  val eval : (int -> bool) -> prop_formula -> bool
  val solve : prop_formula -> result
end
