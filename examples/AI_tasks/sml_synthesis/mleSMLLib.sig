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
  datatype move =
    BIns of (string * int * (int list -> int))
  | BTest
  | BRec
  | BProj of int
  | BSub of int
  | BEndSub
  type board = int * int list * (int * prog list) list

  (* global parameters *)
  val natbase : int
  val maxvar : int
  val maxstep : int
  val instrl : instr list
  val instrd : (string,instr) Redblackmap.dict
  
  (* tree neural network *)
  val operl : term list
  val ol_cat : term
  val head_eval : term
  val head_poli : term
  val term_of_natl : int list -> term
  val term_of_progll : (int * prog list) list -> term
  val term_of_board : board -> term
  val tob : board -> term list
  
  (* program manipluation *)
  val string_of_prog : prog -> string
  val string_of_progll : (int * prog list) list -> string
  val exec : int -> prog -> int list -> int option
  val build : move -> (int * prog list) list -> (int * prog list) list
  val available : board -> move -> bool

  

end
