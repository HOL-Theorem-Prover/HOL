signature tttSynt =
sig

  include Abbrev
  
  type psubst = (int * int) list
  type tsubst = (term * term) list

  datatype pattern =
    Pconst of int
  | Pcomb  of pattern * pattern
  | Plamb  of pattern * pattern
  
  (* global *)
  val freq_limit : int ref

  (* debugging *)
  val ttt_synt_dir : string
  val log_synt     : string -> unit 
  val log_synt_file : string -> string -> unit
  val msg_synt     : 'a list -> string -> unit 
  
  (* concept *)
  val concept_threshold : int ref
  val concept_flag : bool ref
  val conceptualize :
    (term, int) Redblackmap.dict ->
    (term, term) Redblackmap.dict -> term -> term list

  (* pattern *)
  val patternify : term -> pattern * int list
  val p_compare : pattern * pattern -> order
  val regroup : term list -> (pattern, int list list) Redblackmap.dict
  val gen_psubst : 
    (pattern, int list list) Redblackmap.dict -> (psubst * int) list
  val norm_psubst : psubst -> psubst
  
  (* substitution *)
  val read_subst : psubst -> tsubst
  
  (* conjecturing *)
  val gen_cjl : term list -> 
    term list *
    ((term * term) list, term list * real) Redblackmap.dict *
    (term, ((term * term) list * term) list) Redblackmap.dict
 
end
