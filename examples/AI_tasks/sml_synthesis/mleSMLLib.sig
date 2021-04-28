signature mleSMLLib =
sig

  include Abbrev
 

  type state = int list list
  type instr = string * int * (int list -> int)
  val namefunl : instr list
  val mk_varinstr : int -> instr
  val all_input : int -> int -> int list list
  val all_instr : int -> instr list
  val exec_instr : int list list -> instr -> state -> state
  val random_state : int -> int -> state

end
