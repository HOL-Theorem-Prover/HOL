signature mleSMLLib =
sig

  include Abbrev

  exception Unbuildable

  type instr = string * int * (int list -> int)
  datatype prog =
      Ins of instr * prog list
    | Test of prog * prog * prog
    | Rec of prog list
    | Proj of int
    | Sub of prog * prog list
  datatype bprog =
    BIns of (string * int * (int list -> int))
  | BTest
  | BRec
  | BProj of int
  | BStartSub of int
  | BEndSub;

  val compare_prog : prog * prog -> order
  val instrl : instr list
  val instrd : (string,instr) Redblackmap.dict
  val exec : int -> prog -> int list -> int option
  val build : bprog -> (int * prog list) list -> (int * prog list) list

end
