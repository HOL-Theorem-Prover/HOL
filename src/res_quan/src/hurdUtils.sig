signature hurdUtils =
sig
  include Abbrev

  (* GENERAL *)
  type 'a thunk = unit -> 'a
  type 'a susp = 'a Susp.susp
  type ('a, 'b) maplet = {redex : 'a, residue : 'b}

  (* Error handling *)
  val ERR : string -> string -> exn
  val BUG : string -> string -> exn
  val BUG_to_string : exn -> string
  val err_BUG : string -> exn -> exn

  (* Success and failure *)
  val assert : bool -> exn -> unit
  val try : ('a -> 'b) -> 'a -> 'b
  val total : ('a -> 'b) -> 'a -> 'b option
  val can : ('a -> 'b) -> 'a -> bool
  val partial : exn -> ('a -> 'b option) -> 'a -> 'b

  (* Exception combinators *)
  val nof : 'a -> 'b
  val allf : 'a -> 'a
  val thenf : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
  val orelsef : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  val tryf : ('a -> 'a) -> 'a -> 'a
  val repeatf : ('a -> 'a) -> 'a -> 'a
  val repeatplusf : ('a -> 'a) -> 'a -> 'a
  val firstf : ('a -> 'b) list -> 'a -> 'b

  (* Combinators *)
  val A : ('a -> 'b) -> 'a -> 'b
  val N : int -> ('a -> 'a) -> 'a -> 'a
  val oo : ('a -> 'b) * ('c -> 'd -> 'a) -> 'c -> 'd -> 'b

  (* Pairs *)
  val ## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val D : 'a -> 'a * 'a
  val Df : ('a -> 'b) -> ('a * 'a -> 'b * 'b)
  val add_fst : 'a -> 'b -> 'a * 'b
  val add_snd : 'a -> 'b -> 'b * 'a
  val equal : ''a -> ''a -> bool
  val pair_to_string : ('a -> string) -> ('b -> string) -> 'a * 'b -> string

  (* Integers *)
  val plus : int -> int -> int
  val multiply : int -> int -> int
  val succ : int -> int

  (* Strings *)
  val concat : string -> string -> string
  val int_to_string : int -> string
  val string_to_int : string -> int
  val mk_string_fn : string -> string list -> string
  val dest_string_fn : string -> string -> string list
  val is_string_fn : string -> string -> bool

  (* Debugging *)
  val time_n : int -> ('a -> 'b) -> 'a -> unit
  val tt : ('a -> 'b) -> 'a -> 'b
  val tt2 : ('a -> 'b -> 'c) -> 'a -> 'b -> 'c
  val tt3 : ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val tt4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a -> 'b -> 'c -> 'd -> 'e
  val ff : ('a -> 'b) -> 'a -> unit
  val ff2 : ('a -> 'b -> 'c) -> 'a -> 'b -> unit
  val ff3 : ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> unit
  val ff4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a -> 'b -> 'c -> 'd -> unit

  (* Useful imperative features *)
  val new_int : unit -> int
  val random_generator : Random.generator
  val random_integer : int -> int
  val random_real : unit -> real
  val pair_susp : 'a susp -> 'b susp -> ('a * 'b) susp
  val susp_map : ('a -> 'b) -> 'a susp -> 'b susp

  (* Options *)
  val is_some : 'a option -> bool
  val grab : 'a option -> 'a
  val o_pair : 'a option * 'b -> ('a * 'b) option
  val pair_o : 'a * 'b option -> ('a * 'b) option
  val o_pair_o : 'a option * 'b option -> ('a * 'b) option
  val app_o : ('a -> 'b) -> 'a option -> 'b option
  val o_app : ('a -> 'b) option -> 'a -> 'b option
  val o_app_o : ('a -> 'b) option -> 'a option -> 'b option
  val partial_app_o : ('a -> 'b option) -> 'a option -> 'b option
  val partial_o_app : ('a -> 'b option) option -> 'a -> 'b option
  val partial_o_app_o : ('a -> 'b option) option -> 'a option -> 'b option
  val option_to_list : 'a option -> 'a list

  (* Lists *)
  val cons : 'a -> 'a list -> 'a list
  val append : 'a list -> 'a list -> 'a list
  val wrap : 'a -> 'a list
  val unwrap : 'a list -> 'a
  val fold : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val trans : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val partial_trans : ('a -> 'b -> 'b option) -> 'b -> 'a list -> 'b option
  val first : ('a -> bool) -> 'a list -> 'a
  val partial_first : ('a -> 'b option) -> 'a list -> 'b option
  val forall : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val index : ('a -> bool) -> 'a list -> int
  val nth : int -> 'a list -> 'a
  val split_after : int -> 'a list -> 'a list * 'a list
  val assoc : ''a -> (''a * 'b) list -> 'b
  val rev_assoc : ''a -> ('b * ''a) list -> 'b
  val map : ('a -> 'b) -> 'a list -> 'b list
  val partial_map : ('a -> 'b option) -> 'a list -> 'b list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val zipwith : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val partial_zipwith : ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list
  val cart : 'a list -> 'b list -> ('a * 'b) list
  val cartwith : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val partial_cartwith :
    ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list
  val list_to_string : ('a -> string) -> 'a list -> string

  (* Lists as sets *)
  val subset : ''a list -> ''a list -> bool
  val distinct : ''a list -> bool
  val union2 : ''a list * ''b list -> ''a list * ''b list -> ''a list * ''b list

  (* Permutations and sorting (order functions should always be <=) *)
  val rotations : 'a list -> ('a * 'a list) list
  val rotate : int -> ('a list -> 'a * 'a list)
  val rotate_random : 'a list -> 'a * 'a list
  val permutations : 'a list -> 'a list list
  val permute : int list -> 'a list -> 'a list
  val permute_random : 'a list -> 'a list
  val min : ('a -> 'a -> bool) -> 'a list -> 'a
  val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val sort : ('a -> 'a -> bool) -> 'a list -> 'a list
  val top_min : ('a -> 'a -> bool option) -> 'a list -> 'a * 'a list
  val top_sort : ('a -> 'a -> bool option) -> 'a list -> 'a list

  (* Sums *)
  datatype ('a, 'b) sum = LEFT of 'a | RIGHT of 'b

  (* Streams *)
  datatype ('a) stream = STREAM_NIL | STREAM_CONS of ('a * 'a stream thunk)
  val stream_null : 'a stream -> bool
  val dest_stream_cons : 'a stream -> 'a * 'a stream thunk
  val stream_hd : 'a stream -> 'a
  val stream_tl : 'a stream -> 'a stream thunk
  val stream_to_list : 'a stream -> 'a list
  val stream_append : 'a stream thunk -> 'a stream thunk -> 'a stream thunk
  val stream_concat : 'a stream thunk list -> 'a stream thunk

  (* Trees *)
  datatype ('a, 'b) tree = BRANCH of 'a * ('a, 'b) tree list | LEAF of 'b
  val tree_size : ('a, 'b) tree -> int
  val tree_fold : ('a -> 'b list -> 'b) -> ('c -> 'b) -> ('a, 'c) tree -> 'b
  val tree_trans :
    ('a -> 'b -> 'b) -> ('c -> 'b -> 'd) -> 'b -> ('a, 'c) tree -> 'd list
  val tree_partial_trans :
    ('a -> 'b -> 'b option) -> ('c -> 'b -> 'd option) -> 'b ->
    ('a, 'c) tree -> 'd list

  (* Pretty-printing *)
  val pp_map : ('a -> 'b) -> 'b PP.pprinter -> 'a PP.pprinter
  val pp_string : string PP.pprinter
  val pp_unknown : 'a PP.pprinter
  val pp_int : int PP.pprinter
  val pp_pair : 'a PP.pprinter -> 'b PP.pprinter -> ('a * 'b) PP.pprinter
  val pp_list : 'a PP.pprinter -> 'a list PP.pprinter

  (* Substitutions *)
  val redex : ('a, 'b) maplet -> 'a
  val residue : ('a, 'b) maplet -> 'b
  val maplet_map : ('a -> 'c) * ('b -> 'd) -> ('a, 'b) maplet -> ('c, 'd) maplet
  val find_redex : ''a -> (''a, 'b) subst -> (''a, 'b) maplet
  val clean_subst : (''a, ''a) subst -> (''a, ''a) subst
  val subst_vars : ('a, 'b) subst -> 'a list
  val subst_map : ('a -> 'c) * ('b -> 'd) -> ('a, 'b) subst -> ('c, 'd) subst
  val redex_map : ('a -> 'c) -> ('a, 'b) subst -> ('c, 'b) subst
  val residue_map : ('b -> 'c) -> ('a, 'b) subst -> ('a, 'c) subst
  val is_renaming_subst : ''b list -> ('a, ''b) subst -> bool
  val invert_renaming_subst : ''b list -> ('a, ''b) subst -> (''b, 'a) subst

  (* HOL Types *)
  type 'a set = 'a HOLset.set
  type vars = term list * hol_type list
  type vterm = vars * term
  type vthm = vars * thm
  type type_subst = (hol_type, hol_type) subst
  type term_subst = (term, term) subst
  type substitution = term_subst * type_subst
  type ho_substitution = substitution * thm thunk
  type raw_substitution = (term_subst * term set) * (type_subst * hol_type list)
  type ho_raw_substitution = raw_substitution * thm thunk

  (* General *)
  val profile : ('a -> 'b) -> 'a -> 'b
  val parse_with_goal : term frag list -> goal -> term
  val PARSE_TAC : (term -> tactic) -> term frag list -> tactic

  (* Term/type substitutions *)
  val empty_subst : substitution
  val type_inst : type_subst -> hol_type -> hol_type
  val inst_ty : type_subst -> term -> term
  val pinst : substitution -> term -> term
  val type_subst_vars_in_set : type_subst -> hol_type list -> bool
  val subst_vars_in_set : substitution -> vars -> bool
  val type_refine_subst : type_subst -> type_subst -> type_subst
  val refine_subst : substitution -> substitution -> substitution
  val type_vars_after_subst : hol_type list -> type_subst -> hol_type list
  val vars_after_subst : vars -> substitution -> vars
  val type_invert_subst : hol_type list -> type_subst -> type_subst
  val invert_subst : vars -> substitution -> substitution
  val clean_tsubst : term_subst -> term_subst
  val tfind_redex : term -> (term, 'b) subst -> (term, 'b) maplet

  (* Logic variables *)
  val empty_vars : vars
  val is_tyvar : vars -> hol_type -> bool
  val is_tmvar : vars -> term -> bool
  val type_new_vars : hol_type list -> hol_type list * (type_subst * type_subst)
  val term_new_vars : term list -> term list * (term_subst * term_subst)
  val new_vars : vars -> vars * (substitution * substitution)
  val vars_eq : vars -> vars -> bool
  val vars_union : vars -> vars -> vars

  (* Bound variables *)
  val dest_bv : term list -> term -> int
  val is_bv : term list -> term -> bool
  val mk_bv : term list -> int -> term

  (* Terms *)
  val type_vars_in_terms : term list -> hol_type list
  val list_dest_comb : term -> term * term list
  val conjuncts : term -> term list
  val dest_unaryop : string -> term -> term
  val is_unaryop : string -> (term -> bool)
  val dest_binop : string -> term -> term * term
  val is_binop : string -> (term -> bool)
  val dest_imp : term -> term * term
  val is_imp : term -> bool
  val dest_foralls : term -> term list * term
  val mk_foralls : term list * term -> term
  val spec : term -> term -> term
  val specl : term list -> term -> term
  val var_match : vars -> term -> term -> substitution

  (* Theorems *)
  val FUN_EQ : thm
  val SET_EQ : thm
  val hyps : thm list -> term list
  val LHS : thm -> term
  val RHS : thm -> term
  val INST_TY : type_subst -> thm -> thm
  val PINST : substitution -> thm -> thm

  (* Conversions *)
  val FIRSTC : conv list -> conv
  val TRYC : conv -> conv
  val REPEATPLUSC : conv -> conv
  val REPEATC_CUTOFF : int -> conv -> conv
  val DEPTH_ONCE_CONV : conv -> conv
  val FORALLS_CONV : conv -> conv
  val CONJUNCT_CONV : conv -> conv
  val EXACT_CONV : term -> conv
  val NEGNEG_CONV : conv
  val FUN_EQ_CONV : conv
  val SET_EQ_CONV : conv
  val N_BETA_CONV : int -> conv
  val EQ_NEG_BOOL_CONV : conv
  val GENVAR_ALPHA_CONV : conv
  val GENVAR_BVARS_CONV : conv
  val ETA_EXPAND_CONV : term -> conv
  val GENVAR_ETA_EXPAND_CONV : conv

  (* Rules *)
  val THENR : rule * rule -> rule
  val REPEATR : rule -> rule
  val ORELSER : rule * rule -> rule
  val TRYR : rule -> rule
  val ALL_RULE : rule
  val EVERYR : rule list -> rule
  val FORALL_IMP : rule
  val EQ_BOOL_INTRO : rule
  val GENVAR_BVARS : rule
  val GENVAR_SPEC : rule
  val GENVAR_SPEC_ALL : rule
  val REV_CONJUNCTS : thm list -> thm
  val REORDER_ASMS : term list -> rule
  val NEW_CONST_RULE : term -> rule
  val GENVAR_CONST_RULE : rule
  val ZAP_CONSTS_RULE : rule

  (* Variable theorem (vthm) operations *)
  val thm_to_vthm : thm -> vthm
  val vthm_to_thm : vthm -> thm
  val clean_vthm : vthm -> vthm
  val var_GENVAR_SPEC : vthm -> vthm
  val var_CONJUNCTS : vthm -> vthm list
  val var_MATCH_MP : thm -> vthm -> vthm

  (* Discharging assumptions onto the lhs of an implication *)
  val DISCH_CONJ_CONV : conv
  val DISCH_CONJ : term -> rule
  val DISCH_CONJUNCTS : term list -> rule
  val DISCH_CONJUNCTS_ALL : rule
  val DISCH_CONJUNCTS_FILTER : (term -> bool) -> rule
  val DISCH_CONJ_TAC : tactic
  val DISCH_CONJUNCTS_TAC : tactic
  val UNDISCH_CONJ_CONV : conv
  val UNDISCH_CONJ : rule
  val UNDISCH_CONJUNCTS : rule
  val UNDISCH_CONJ_TAC : term -> tactic
  val UNDISCH_CONJUNCTS_TAC : tactic

  (* Tactics *)
  val PURE_CONV_TAC : conv -> tactic
  val ASMLIST_CASES : tactic -> (term -> tactic) -> tactic
  val POP_ASSUM_TAC : tactic -> tactic
  val TRUTH_TAC : tactic
  val S_TAC : tactic
  val Strip : tactic
  val K_TAC : 'a -> tactic
  val KILL_TAC : tactic
  val FUN_EQ_TAC : tactic
  val SET_EQ_TAC : tactic
  val STRONG_CONJ_TAC : tactic
  val STRONG_DISJ_TAC : tactic
  val FORWARD_TAC : (thm list -> thm list) -> tactic
  val Know : term quotation -> tactic
  val Suff : term quotation -> tactic
  val POP_ORW : tactic
  val Rewr  : tactic
  val Rewr' : tactic
  val art : thm list -> tactic (* ASM_REWRITE_TAC *)

  (* Simple CNF conversion *)
  val CNF_CONV : conv
  val CNF_RULE : rule
  val CNF_EXPAND : thm -> thm list
  val CNF_TAC : tactic

  (* ASM_MATCH_MP_TAC *)
  val MATCH_MP_DEPTH : int -> thm list -> thm list -> thm list
  val ASM_MATCH_MP_TAC_N : int -> thm list -> tactic
  val ASM_MATCH_MP_TAC : thm list -> tactic

end
