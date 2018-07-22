signature tttSynt =
sig

  include Abbrev
  
  type psubst = (int * int) list
  datatype pattern =
    Pconst of int
  | Pcomb  of pattern * pattern
  | Plamb  of pattern * pattern

  (* pattern *)
  val patternify : term -> pattern * int list
  val p_compare : pattern * pattern -> order
  val regroup : term list -> (pattern, int list list) Redblackmap.dict
  val gen_psubst : (pattern, int list list) Redblackmap.dict -> psubst list
  val norm_psubst : psubst -> psubst
  
  (* substitution *)
  val read_subst  : psubst -> (term,term) subst
  val check_subst : (term,term) subst -> bool
  
  (* conjecturing *)
  val int_div : int -> int -> real
  val subst_changed : {redex: term, residue: term} list -> term -> 
    (term * term) option
  val eval_subst    : term list ->
    (term,term) subst * int ->
    (term,term) subst * (term * term) list * real
 
end
