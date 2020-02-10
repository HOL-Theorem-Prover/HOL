signature mleCombinLib =
sig

  include Abbrev

  (* position *)
  val subst_pos : term * int list -> term -> term
  val all_pos : term -> (term * int list) list
  val tag_pos : term * int list -> term

  (* combinator terms *)
  val cA : term
  val cT : term
  val cS : term
  val cK : term
  val cX : term
  val cL : term
  val cV : term
  val v1 : term
  val v2 : term
  val v3 : term
  val cts : term -> string
  val cterm_size : term -> int
  
  (* combinator theorems *)
  val forall_capital : term -> term
  val tag_axl_bare : term list
  val eq_axl_bare : term list
  val eq_axl : term list
  val ev_axl : term list
  val rw_axl : term list

  (* constructors and destructors *)
  val mk_cV : term -> term
  val mk_cL : term -> term  
  val mk_cEV : term * term -> term
  val mk_cRW : term * term -> term
  val mk_cA : term * term -> term
  val dest_cA : term -> term * term
  val list_mk_cA : term list-> term
  val strip_cA : term -> term list
  val mk_tag : term -> term
  val dest_tag : term -> term
  
  (* rewriting *)
  val is_match : term -> term -> bool
  val lo_cnorm : int -> term list -> term -> term option
  val fast_lo_cnorm : int -> term list -> term -> term option
  val subst_match : term -> term -> term
  val contain_red : term -> bool
  val is_nf : term -> bool
 
  (* generation *)
  val random_nf : int -> term
  val gen_nf_exhaustive : int -> term list

end
