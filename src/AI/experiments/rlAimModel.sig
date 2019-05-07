signature rlAimModel =
sig

  include Abbrev

  type table = int option vector vector
  type table3 = int option vector vector vector  

  datatype expr = 
    Ic of int | 
    Tc of expr * expr | Lc of expr * expr * expr | Rc of expr * expr * expr |  
    Ec of expr * expr

  type board = table * (int * int) * (expr, expr list) Redblackmap.dict * bool
  type move = int
   

  val mk_under_over : table -> (table * table)

  val empty_partial_loop : int -> table
  val is_partial_loop : table -> bool
  val is_cjaim : table -> bool 
  val print_table : table -> unit
  val init_cgraph : int -> (expr, expr list) Redblackmap.dict
  val update_cgraph : table * (expr, expr list) Redblackmap.dict ->
    (expr, expr list) Redblackmap.dict * bool
  val status_of : board psMCTS.sit -> psMCTS.status
  val apply_move : move -> board psMCTS.sit -> board psMCTS.sit

end
