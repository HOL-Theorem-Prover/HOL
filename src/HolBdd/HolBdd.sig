signature HolBdd = sig
(*
  type varnum = int
  eqtype method
  datatype bdd.bddop
  type varSet
  eqtype fixed
  type nodetable = int * (int * int * int) vector
  type level = int
  type bdd
  type pairSet
  type restriction
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
*)
  type var_map = (string, int) Binarymap.dict
  type table = int * (string, int) Binarymap.dict
  type bdd_map = (Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net
(*
  val var : bdd.bdd -> int
  con And = And : bdd.bddop
*)
  val DIFF : bdd.bdd * bdd.bdd -> bdd.bdd
  val REORDER_NONE : bdd.method
  val stats : unit ->
                 {cachesize : int, freenodes : int, gbcnum : int, maxnodenum : int,
                  minfreenodes : int, nodenum : int, produced : int, varnum : int}
(*
  con Nor = Nor : bdd.bddop
*)
  val IMP : bdd.bdd * bdd.bdd -> bdd.bdd
  val LESSTH : bdd.bdd * bdd.bdd -> bdd.bdd
  val fnprintset : string -> bdd.bdd -> unit
  val nithvar : int -> bdd.bdd
  val ithvar : int -> bdd.bdd
  val FALSE : bdd.bdd
  val SIFTITE : bdd.method
(*
  con Lessth = Lessth : bdd.bddop
*)
  val addvarblock : int -> int -> bdd.fixed -> unit
  val autoReorder : bdd.method -> bdd.method
  val BIIMP : bdd.bdd * bdd.bdd -> bdd.bdd
  val printset : bdd.bdd -> unit
(*
  con Or = Or : bdd.bddop
  con Xor = Xor : bdd.bddop
*)
  val RANDOM : bdd.method
  val FREE : bdd.fixed
  val OR : bdd.bdd * bdd.bdd -> bdd.bdd
  val WIN2 : bdd.method
  val varAtLevel : int -> int
  val makepairSet : (int * int) list -> bdd.pairSet
  val simplify : bdd.bdd -> bdd.bdd -> bdd.bdd
  val nodetable : bdd.bdd -> int * (int * int * int) vector
  val getVarnum : unit -> int
  val INVIMP : bdd.bdd * bdd.bdd -> bdd.bdd
(*
  con Imp = Imp : bdd.bddop
*)
  val fromBool : bool -> bdd.bdd
(*
  con Diff = Diff : bdd.bddop
  con Invimp = Invimp : bdd.bddop
*)
  val toSet_ : bdd.bdd -> bdd.varSet
  val autoReorderTimes : bdd.method -> int -> bdd.method
  val reorder : bdd.method -> unit
  val disableReorder : unit -> unit
  val apply : bdd.bdd -> bdd.bdd -> bdd.bddop -> bdd.bdd
  val restrict : bdd.bdd -> bdd.restriction -> bdd.bdd
  val equal : bdd.bdd -> bdd.bdd -> bool
  val support : bdd.bdd -> bdd.varSet
  val compose : bdd.bdd -> bdd.bdd -> int -> bdd.bdd
  val enableReorder : unit -> unit
  val TRUE : bdd.bdd
  val exist : bdd.varSet -> bdd.bdd -> bdd.bdd
  val NAND : bdd.bdd * bdd.bdd -> bdd.bdd
  val getMethod : unit -> bdd.method
  val isRunning : unit -> bool
  val scanset : bdd.varSet -> int vector
  val ITE : bdd.bdd -> bdd.bdd -> bdd.bdd -> bdd.bdd
  val varToLevel : int -> int
(*
  con Biimp = Biimp : bdd.bddop
*)
  val getTimes : unit -> int
  val nodecount : bdd.bdd -> int
  val low : bdd.bdd -> bdd.bdd
  val appex : bdd.bdd -> bdd.bdd -> bdd.bddop -> bdd.varSet -> bdd.bdd
  val replace : bdd.bdd -> bdd.pairSet -> bdd.bdd
  val setVarnum : int -> unit
  val toBool : bdd.bdd -> bool
  val done : unit -> unit
  val fromSet : bdd.varSet -> bdd.bdd
  val forall : bdd.varSet -> bdd.bdd -> bdd.bdd
  val clrvarblocks : unit -> unit
  val appall : bdd.bdd -> bdd.bdd -> bdd.bddop -> bdd.varSet -> bdd.bdd
  val AND : bdd.bdd * bdd.bdd -> bdd.bdd
  val NOR : bdd.bdd * bdd.bdd -> bdd.bdd
  val fnprintdot : string -> bdd.bdd -> unit
  val satcount : bdd.bdd -> real
  val makeset : int list -> bdd.varSet
  val NOT : bdd.bdd -> bdd.bdd
  val WIN2ITE : bdd.method
(*
  con Nand = Nand : bdd.bddop
*)
  val printdot : bdd.bdd -> unit
  val init : int -> int -> unit
  val XOR : bdd.bdd * bdd.bdd -> bdd.bdd
  val makeRestriction : (int * bool) list -> bdd.restriction
  val high : bdd.bdd -> bdd.bdd
  val hash : bdd.bdd -> int
  val makeset_ : int vector -> bdd.varSet
  val FIXED : bdd.fixed
  val SIFT : bdd.method
(*
  val dest_comb : Term.term -> Term.term * Term.term
  val new_binder : string * Type.hol_type -> unit
  val dest_cons : Term.term -> Term.term * Term.term
  val mk_let : Term.term * Term.term -> Term.term
  val mk_const : string * Type.hol_type -> Term.term
  val mk_exists : Term.term * Term.term -> Term.term
  val match_type : Type.hol_type -> Type.hol_type -> (Type.hol_type * Type.hol_type) list
  val match_term : Term.term -> Term.term ->
      (Term.term * Term.term) list * (Type.hol_type * Type.hol_type) list
  val mk_forall : Term.term * Term.term -> Term.term
  val mk_type : string * Type.hol_type list -> Type.hol_type
  val dest_const : Term.term -> string * Type.hol_type
  val dest_abs : Term.term -> Term.term * Term.term
  val type_subst : (Type.hol_type * Type.hol_type) list -> Type.hol_type -> Type.hol_type
  val dest_var : Term.term -> string * Type.hol_type
  val mk_select : Term.term * Term.term -> Term.term
  val INST_TYPE : (Type.hol_type * Type.hol_type) list -> Thm.thm -> Thm.thm
  val inst : (Type.hol_type * Type.hol_type) list -> Term.term -> Term.term
  val mk_imp : Term.term * Term.term -> Term.term
  val mk_pair : Term.term * Term.term -> Term.term
  val dest_let : Term.term -> Term.term * Term.term
  val dest_type : Type.hol_type -> string * Type.hol_type list
  val mk_disj : Term.term * Term.term -> Term.term
  val dest_exists : Term.term -> Term.term * Term.term
  val mk_cond : Term.term * Term.term * Term.term -> Term.term
  val mk_list : Term.term list * Type.hol_type -> Term.term
  val new_recursive_definition : fixity -> Thm.thm -> string -> Term.term -> Thm.thm
  val new_type_definition : string * Term.term * Thm.thm -> Thm.thm
  val new_type : int -> string -> unit
  val dest_forall : Term.term -> Term.term * Term.term
  val dest_pair : Term.term -> Term.term * Term.term
  val mk_primed_var : string * Type.hol_type -> Term.term
  val mk_pabs : Term.term * Term.term -> Term.term
  val new_constant : string * Type.hol_type -> unit
  val dest_disj : Term.term -> Term.term * Term.term
  val mk_conj : Term.term * Term.term -> Term.term
  val dest_cond : Term.term -> Term.term * Term.term * Term.term
  val dest_imp : Term.term -> Term.term * Term.term
  val dest_list : Term.term -> Term.term list * Type.hol_type
  val dest_select : Term.term -> Term.term * Term.term
  val new_specification : string -> (string * string * int) list -> Thm.thm -> Thm.thm
  val mk_eq : Term.term * Term.term -> Term.term
  val SUBST : (Thm.thm * Term.term) list -> Term.term -> Thm.thm -> Thm.thm
  val subst_occs : int list list -> (Term.term * Term.term) list -> Term.term -> Term.term
  val SUBST_CONV : (Thm.thm * Term.term) list -> Term.term -> Term.term -> Thm.thm
  val dest_pabs : Term.term -> Term.term * Term.term
  val dest_conj : Term.term -> Term.term * Term.term
  val subst : (Term.term * Term.term) list -> Term.term -> Term.term
  val mk_comb : Term.term * Term.term -> Term.term
  val mk_cons : Term.term * Term.term -> Term.term
  val new_infix : string * Type.hol_type * int -> unit
  val INST_TY_TERM : (Term.term * Term.term) list * (Type.hol_type * Type.hol_type) list ->
      Thm.thm -> Thm.thm
  val INST : (Term.term * Term.term) list -> Thm.thm -> Thm.thm
  val define_new_type_bijections : string -> string -> string -> Thm.thm -> Thm.thm
  val mk_abs : Term.term * Term.term -> Term.term
  val mk_var : string * Type.hol_type -> Term.term
  val dest_eq : Term.term -> Term.term * Term.term
  val FORK_CONV : (Term.term -> Thm.thm) * (Term.term -> Thm.thm) -> Term.term -> Thm.thm
  val BINOP_CONV : (Term.term -> Thm.thm) -> Term.term -> Thm.thm
  val QUANT_CONV : (Term.term -> Thm.thm) -> (Term.term -> Thm.thm)
  val BINDER_CONV : (Term.term -> Thm.thm) -> (Term.term -> Thm.thm)
*)
  val EX_OR_CONV : Term.term -> Thm.thm
(*
  val TERNOP_CONV : (Term.term -> Thm.thm) -> (Term.term -> Thm.thm)
*)
  val T : Term.term
  val F : Term.term
(*
  val mk_conj1 : Term.term * Term.term -> Term.term
  val mk_disj1 : Term.term * Term.term -> Term.term
  exception Error
  val error : unit -> 'a
*)
  val hol_err : string -> string -> 'a
(*
  val tag : Tag.tag
  val empty_var_map : (string, int) Binarymap.dict
  val empty_table : int * (string, int) Binarymap.dict
  val insert : int * ('a, int) Binarymap.dict -> 'a -> int * ('a, int) Binarymap.dict
  val peek : 'a * ('b, 'c) Binarymap.dict -> 'b -> 'c option
  val size : ('a, 'b) Binarymap.dict -> int
  val peek_map : ('a, 'b) Binarymap.dict -> 'a -> 'b option
  val var_to_int : (string, int) Binarymap.dict -> string -> int
  val list_to_var_map : string list -> (string, int) Binarymap.dict
  val var_map_to_pairs : ('a, 'b) Binarymap.dict -> ('a * 'b) list
  val PolyTableSizeHint : int ref
  val current_bdd_map : (Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net
  val lookup_var : (string, int) Binarymap.dict -> string -> bdd.bdd
  val check_var : Term.term -> bool
  val match_to_pairs : (Term.term * Term.term) list -> (string * string) list
  val subst_bdd : (string, int) Binarymap.dict -> (string * string) list -> bdd.bdd -> bdd.bdd
  val find_data : string -> ('a, 'b) Polyhash.hash_table -> 'a list -> 'a * 'b
  val NetPeek : (string, int) Binarymap.dict ->
      (Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net -> Term.term ->
      bdd.bdd option
  val appQuantTest : Term.term -> bool
  val fromTerm_aux : (string, int) Binarymap.dict ->
      (Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net -> Term.term ->
      bdd.bdd
  val combExp : (string, int) Binarymap.dict ->
      ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net ->
       (Term.term -> (Term.term list -> bdd.bdd)))
  val binExp : (string, int) Binarymap.dict ->
      ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net ->
       (bdd.bddop -> (Term.term list -> bdd.bdd)))
  val quantExp : (string, int) Binarymap.dict ->
      ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net ->
       ((Term.term -> Term.term list * Term.term) ->
        ((bdd.varSet -> bdd.bdd -> bdd.bdd) ->
         ((bdd.bdd -> bdd.bdd -> bdd.bddop -> bdd.varSet -> bdd.bdd) -> (Term.term -> bdd.bdd)))))
  val condExp : (string, int) Binarymap.dict ->
      ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net ->
       (Term.term list -> bdd.bdd))
  val fromTerm : (string, int) Binarymap.dict ->
      (Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net -> Term.term ->
      bdd.bdd
  val pureFromTerm_aux : (string, int) Binarymap.dict -> Term.term -> bdd.bdd
  val pureBinExp : (string, int) Binarymap.dict -> (bdd.bddop -> (Term.term list -> bdd.bdd))
  val pureQuantExp : (string, int) Binarymap.dict ->
      ((Term.term -> Term.term list * Term.term) ->
       ((bdd.varSet! -> bdd.bdd -> bdd.bdd) -> (Term.term -> bdd.bdd)))
  val pureCondExp : (string, int) Binarymap.dict -> (Term.term list -> bdd.bdd)
  val pureFromTerm : (string, int) Binarymap.dict -> Term.term -> bdd.bdd
  val bdd_match_split : (Term.term * 'a) list -> Term.term list ->
      (Term.term * 'a) list * (Term.term * 'a) list
*)
  val BDD_CONV : (Term.term, 'a) Polyhash.hash_table * Term.term Net.net -> Term.term -> Thm.thm
(*
  val NetPrePeek : (Term.term, 'a) Polyhash.hash_table * Term.term Net.net ->
      (Term.term -> Thm.thm option)
  val BDD_MATCH_CONV : (Term.term, 'a) Polyhash.hash_table * Term.term Net.net ->
      (Term.term -> (Term.term -> Thm.thm))
  val BDD_TR : (Term.term, 'a) Polyhash.hash_table * Term.term Net.net -> Term.term -> Term.term
  val add_var_to_table : string * (int * (string, int) Binarymap.dict) ->
      int * (string, int) Binarymap.dict
  val add_vars_to_table : int * (string, int) Binarymap.dict -> Term.term list ->
      int * (string, int) Binarymap.dict
  val add_names_to_table : int * (string, int) Binarymap.dict -> string list ->
      int * (string, int) Binarymap.dict
  val term_to_var_map : string list -> Term.term -> (string, int) Binarymap.dict
  val var_map_to_sed_script : string -> (string * int) list -> unit
*)
  val showBDD : string -> string -> bdd.bdd -> bdd.bdd
(*
  val showBDDofTerm : string -> string -> (string, int) Binarymap.dict ->
      (Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net -> Term.term ->
      bdd.bdd * (string * int) list
  val print_bdd_state : string ->
      (int * (string, int) Binarymap.dict) *
      ((Term.term, bdd.bdd) Polyhash.hash_table * 'a) -> (Term.term * bdd.bdd) list
*)
  val bdd_state : ((int * (string, int) Binarymap.dict) *
       ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net)) ref
  val initHolBdd : string list -> unit
  val showVarMap : unit -> (string * int) list
  val showBddMap : unit -> (Term.term * bdd.bdd) list
  val showVarOrd : unit -> string list
  val deleteBdd : Term.term -> bdd.bdd
  val deleteBdd_flag : bool ref
  exception termToBddError
  val termToBdd : Term.term -> bdd.bdd
  exception pureTermToBddError
  val pureTermToBdd : Term.term -> bdd.bdd
(*
  val add_var : string -> int
  val add_definition : Thm.thm ->
      (int * (string, int) Binarymap.dict) *
      ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net) ->
      (Term.term * bdd.bdd) *
      ((int * (string, int) Binarymap.dict) *
       ((Term.term, bdd.bdd) Polyhash.hash_table * Term.term Net.net))
*)
  val addEquation : Thm.thm -> Term.term * bdd.bdd
(*
  val default_dot_dir : string ref
  val print_state : unit -> (Term.term * bdd.bdd) list
*)
  val showTerm : Term.term -> unit
(*
  val termToBddDiagram : string -> string -> Term.term -> bdd.bdd * (string * int) list
*)
  val is_taut : bdd.bdd -> bool
  val tautCheck : Term.term -> bool option
  val pureTautCheck : Term.term -> bool option
  val isT : Term.term -> bool
  val isF : Term.term -> bool
  val eqCheck : Term.term * Term.term -> bool
(*
  val mk_bdd_thm : Term.term -> Thm.thm
*)
  exception bddOracleError
  val bddOracle : Term.term -> Thm.thm
  val bddEqOracle : Term.term * Term.term -> Thm.thm
  val BDD_TAC : Term.term list * Term.term -> 'a list * ('b list -> Thm.thm)
  val findAssignment_aux : bdd.bdd -> bdd.bdd list
(*
  val bdd_to_literal : (string, int) Binarymap.dict -> bdd.bdd -> Term.term
  val findAssignment : (string, int) Binarymap.dict * bdd.bdd -> Term.term
*)
  val findRefutation : Term.term -> Term.term
(*
  val find_bdd_model_aux : bdd.bdd -> bdd.bdd list -> bdd.bdd list option
  val find_bdd_model : bdd.bdd -> bdd.bdd option
*)
  val findModel : Term.term -> Term.term
(*
  val find_bdd_refutation : bdd.bdd -> bdd.bdd option
  val get_node_name : int -> string
*)
  val bddToTerm : bdd.bdd -> Term.term
  val bddRepOracle : Term.term -> Thm.thm
  val statecount : bdd.bdd -> real
end