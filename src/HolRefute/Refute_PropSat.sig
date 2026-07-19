signature REFUTE_PROP_SAT = sig
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
  val simplify : prop_formula -> prop_formula

  val indices : prop_formula -> int list
  val maxidx : prop_formula -> int
  val exists : prop_formula list -> prop_formula
  val all : prop_formula list -> prop_formula

  val is_nnf : prop_formula -> bool
  val is_cnf : prop_formula -> bool
  val nnf : prop_formula -> prop_formula
  val defcnf : prop_formula -> prop_formula

  val eval : (int -> bool) -> prop_formula -> bool
  val solve : prop_formula -> result
end
