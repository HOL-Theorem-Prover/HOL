signature mlePrologLib =
sig

  include Abbrev

  
  type prog = (term * term list) list
  type table = (term * bool) list

  (* constructors *)
  val mk_cons : term -> term -> term
  val mk_sing : term -> term
  val mk_del : term -> term -> term -> term
  val mk_leq : term -> term -> term
  val cons_bool : term
  val cons_num : term
  val operlsorted : term list
  val all_var : int * int -> term list

  (* generation of inputs *)
  val cstrdel : term list * hol_type
  val cstrleq : term list * hol_type
  val cstrsorted : term list * hol_type
  val gen_term_n : term list * hol_type -> int -> term list
  val create_table : prog -> term list * hol_type -> table

  (* translation between representation of programs *)
  val qt_to_prog : term -> prog
  val prog_to_qt : prog -> term

  (* execution *)
  val execute : int -> prog -> term -> (term,term) subst
  
  val add_output : prog -> term -> (term * bool)
  val test_io : prog -> (term * bool) -> (bool * bool)  

  (* testing *)
  val inputdel : term
  val progdel : prog
  val progleq : prog
  val progsorted : prog
  
  

end
