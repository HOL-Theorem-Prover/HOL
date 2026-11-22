signature hhMePo =
sig
  type ptype = int * Type.hol_type list
  type pconst = string * ptype
  type pconst_table
  type frequency_table

  type fudge =
    {local_const_multiplier : real,
     worse_irrel_freq : real,
     higher_order_irrel_weight : real,
     abs_rel_weight : real,
     abs_irrel_weight : real,
     theory_const_rel_weight : real,
     theory_const_irrel_weight : real,
     chained_const_irrel_weight : real,
     intro_bonus : real,
     elim_bonus : real,
     simp_bonus : real,
     local_bonus : real,
     assum_bonus : real,
     chained_bonus : real,
     max_imperfect : real,
     max_imperfect_exp : real,
     threshold_divisor : real,
     ridiculous_threshold : real,
     fact_threshold0 : real,
     fact_threshold1 : real,
     perfect_threshold : real,
     hopeless_threshold : real,
     special_fact_index : int,
     hopeless_iter : int}

  val default_fudge : fudge
  val pseudo_abs_name : string
  val pseudo_theory_name : string -> string

  val order_of_type : Type.hol_type -> int
  val ptype_eq : ptype * ptype -> bool
  (* The second argument is an instance of the first.  In particular, an
     exhausted instance list matches a nonempty pattern list. *)
  val match_patternT : Type.hol_type * Type.hol_type -> bool
  val match_ptype : ptype * ptype -> bool

  (* The string argument is the owning theory.  Each call also inserts its
     [%thy%...] pseudo-constant. *)
  val empty_pconst_table : unit -> pconst_table
  val add_pconst_to_table : pconst -> pconst_table -> pconst_table
  val add_pconsts_in_term :
    string -> Term.term -> pconst_table -> pconst_table
  val pconsts_of_table : pconst_table -> pconst list
  val pconsts_in_term : string -> Term.term -> pconst list
  val pconst_hyper_mem :
    (ptype * ptype -> bool) -> pconst_table -> pconst -> bool

  (* Inputs are (owning theory, conclusion).  This traversal is deliberately
     raw: logical and set constants are counted rather than stripped. *)
  val count_fact_consts : (string * Term.term) list -> frequency_table
  val pconst_freq :
    (ptype * ptype -> bool) -> frequency_table -> pconst -> int
  val frequency_entries : frequency_table -> (pconst * int) list

  (* These are the mathematical parts of MePo's score.  They are exposed so
     that the port can be checked against hand calculations without exposing
     the representation of a cached fact. *)
  val rel_weight_for : int -> int -> real
  val irrel_weight_for : fudge -> int -> int -> real
  val rel_pconst_weight : fudge -> frequency_table -> pconst -> real
  val irrel_pconst_weight :
    fudge -> frequency_table -> pconst_table -> pconst -> real
  val stature_bonus : fudge -> hhStature.stature -> real
  val fact_weight :
    fudge -> hhStature.stature -> frequency_table -> pconst_table ->
    pconst_table -> pconst list -> real

  (* Return the accepted candidates, followed by those left for later. *)
  val take_most_relevant :
    fudge -> {max_facts : int, remaining_max : int,
              candidates : ('a * real) list} ->
    ('a * real) list * ('a * real) list
  val purge_hopeless :
    fudge -> int -> ('a * real) list -> ('a * real) list

  type context
  val make_context :
    {current_theory : string,
     facts : {thmid : string, theory : string, concl : Term.term,
              stature : hhStature.stature} list} -> context
  val create_context_for :
    string -> mlThmData.thmdata -> hhStature.statures -> context
  val create_context : mlThmData.thmdata -> hhStature.statures -> context
  val restrict_context : context -> string list -> context
  (* Reuse a set of requested theorem names built with String.compare.
     The result retains the context's fact order. *)
  val restrict_context_to : context -> (string, unit) Redblackmap.dict ->
    context
  val context_thmids : context -> string list
  val mepo_rank_with_fudge : fudge -> context -> Abbrev.goal -> int ->
    string list
  val mepo_rank : context -> Abbrev.goal -> int -> string list
end
