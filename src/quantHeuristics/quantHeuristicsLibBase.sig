signature quantHeuristicsLibBase =
sig
  include Abbrev


(*some general conversions, that might be useful
  in other context as well *)
  val TOP_ONCE_REWRITE_CONV        : thm list -> conv;
  val NEG_NEG_INTRO_CONV           : conv;
  val NEG_NEG_ELIM_CONV            : conv;
  val NOT_FORALL_LIST_CONV         : conv;
  val NOT_EXISTS_LIST_CONV         : conv;
  val STRIP_NUM_QUANT_CONV         : int -> conv -> conv;
  val BOUNDED_NOT_EXISTS_LIST_CONV : int -> conv;
  val BOUNDED_REPEATC              : int -> conv -> conv;

  val EXISTS_NOT_LIST_CONV         : conv;
  val FORALL_NOT_LIST_CONV         : conv;
  val QUANT_SIMP_CONV              : conv;

  val NOT_OR_CONV                  : conv;
  val NOT_AND_CONV                 : conv;
  val AND_NOT_CONV                 : conv;
  val OR_NOT_CONV                  : conv;

  val VARIANT_TAC                  : term list -> tactic
  val VARIANT_CONV                 : term list -> conv


  datatype guess_type =
      gty_exists | gty_exists_gap | gty_exists_point
    | gty_forall | gty_forall_gap | gty_forall_point

  datatype guess =
       guess_general of term * term list
     | guess_term of guess_type * term * term list * term
     | guess_thm of guess_type * term * term list * thm

  val is_guess_general : guess -> bool
  val is_guess_thm     : guess_type -> guess -> bool
  val is_guess_term    : guess_type -> guess -> bool
  val is_guess         : guess_type -> guess -> bool
  val guess_has_thm    : guess -> bool
  val guess_has_no_free_vars     : guess -> bool
  val guess_has_thm_no_free_vars : guess -> bool

  val guess_type2string   : guess_type -> string
  val guess_type2term     : guess_type -> term
  val guess_term2type     : term -> guess_type
  val make_guess_thm_term : guess_type -> term -> term -> term -> term list -> term
  val guess_remove_thm    : term -> term -> guess -> guess
  val make_set_guess_thm  : guess -> (term -> thm) -> guess
  val mk_guess            : guess_type -> term -> term -> term -> term list -> guess
  val mk_guess_opt        : guess_type option -> term -> term -> term -> term list -> guess

  val make_guess___dummy  : guess_type -> term -> term -> term -> term list -> guess
  val make_guess___assume : guess_type -> term -> term -> term -> term list -> guess
  val make_guess___simple : guess_type -> term -> term -> term -> term list -> guess

  val make_set_guess_thm___dummy  : guess -> guess
  val make_set_guess_thm___simple : guess -> guess
  val make_set_guess_thm___assume : guess -> guess

  val guess_extract       : guess -> term * term list
  val guess_extract_thm   : guess -> guess_type * term * term list * thm * bool
  val guess2term          : guess -> term option
  val guess2thm           : guess -> bool * thm
  val guess2thm_opt       : guess -> thm option
  val guess_extract_type  : guess -> guess_type option


  val guess_thm_to_guess  : bool -> (term * term list) option -> thm -> guess
  val dest_guess_tm       : term -> guess_type * term * term * term
  val is_guess_tm         : term -> bool

  val guess_to_string : bool -> guess -> string


  (*guesses are organised in collections. They are used to
    store the different types of guesses separately. Moreover,
    rewrite theorems, that might come in handy, are there as well.*)
  type guess_collection =
   {rewrites     : thm list,
    general      : guess list,
    exists_point : guess list,
    forall_point : guess list,
    forall       : guess list,
    exists       : guess list,
    forall_gap   : guess list,
    exists_gap   : guess list}

  val guess_collection_guess_type : guess_type -> guess_collection -> guess list

  val empty_guess_collection    : guess_collection;
  val is_empty_guess_collection : guess_collection -> bool;
  val guess_collection_append   : guess_collection -> guess_collection -> guess_collection;
  val guess_collection_flatten  : guess_collection option list -> guess_collection;
  val guess_list2collection     : thm list * guess list -> guess_collection;
  val guess_collection2list     : guess_collection -> thm list * guess list;
  val guess_collection___get_exists_weaken     : guess_collection -> guess list;
  val guess_collection___get_forall_weaken : guess_collection -> guess list;



  val guess_weaken       : guess -> guess
  val check_guess        : term -> term -> guess -> bool
  val correct_guess      : term -> term -> guess -> guess option
  val correct_guess_list : term -> term -> guess list -> guess list;
  val correct_guess_collection :
     term -> term -> guess_collection -> guess_collection


  type inference_collection =
     {exists_point : thm list,
      forall_point : thm list,
      exists       : thm list,
      forall       : thm list,
      exists_gap   : thm list,
      forall_gap   : thm list};

  val GUESS_THM_list2collection : thm list -> inference_collection;


  exception QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

(*Basic types*)
  type quant_heuristic_base = term -> term -> guess_collection;
  type quant_heuristic      = quant_heuristic_base -> quant_heuristic_base;
  type quant_heuristic_cache;

  val mk_quant_heuristic_cache : unit -> quant_heuristic_cache;


(* Quantifier Heuristics Parameters are the main way to configure the behaviour. They
   are a record of theorems, conversion and full heuristics used during proof search. *)

  type quant_param;

(* constructing quantifier heuristics parameters*)

  val distinct_qp      : thm list -> quant_param
  val cases_qp         : thm list -> quant_param
  val rewrite_qp       : thm list -> quant_param
  val inst_filter_qp   : (term -> term -> term -> term list -> bool) list -> quant_param
  val instantiation_qp : thm list -> quant_param
  val imp_qp           : thm list -> quant_param
  val fixed_context_qp : thm list -> quant_param
  val inference_qp     : thm list -> quant_param
  val convs_qp         : conv list -> quant_param
  val filter_qp        : (term -> term -> bool) list -> quant_param
  val top_heuristics_qp: quant_heuristic list -> quant_param
  val context_heuristics_qp : (thm list -> quant_heuristic) list -> quant_param
  val context_top_heuristics_qp : (thm list -> quant_heuristic) list -> quant_param
  val heuristics_qp    : quant_heuristic list -> quant_param
  val oracle_qp        : (term -> term -> (term * term list) option) -> quant_param (* creates heuristic that produces oracle guesses *)
  val context_oracle_qp: (thm list -> term -> term -> (term * term list) option) -> quant_param (* creates heuristic that produces oracle guesses *)
  val final_rewrite_qp : thm list -> quant_param

  (* a stateful version and combining several*)
  val clear_stateful_qp : unit -> unit
  val stateful_qp___add_combine_arguments :
     quant_param list -> unit;

  val empty_qp           : quant_param;
  val basic_qp           : quant_param; (* the basic things that should always be turned on *)
  val stateful_qp        : unit -> quant_param;
  val pure_stateful_qp   : unit -> quant_param;
  val TypeBase_qp        : quant_param;
  val get_qp___for_types : hol_type list -> quant_param

  val combine_qp :
     quant_param -> quant_param ->
     quant_param;

  val combine_qps :
     quant_param list -> quant_param;


  val COMBINE_HEURISTIC_FUNS : (unit -> guess_collection) list -> guess_collection;

(*Heuristics that might be useful to write own ones*)
  val QUANT_INSTANTIATE_HEURISTIC___CONV                : conv -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___EQUATION_distinct   : thm list -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___EQUATION_two_cases  : thm -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___one_case            : thm -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___cases               : thm -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___GIVEN_INSTANTIATION : thm list -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___STRENGTHEN_WEAKEN   : thm list -> quant_heuristic;

  val QUANT_INSTANTIATE_HEURISTIC___max_rec_depth : int ref

  (*use this to create sys for debugging own heuristics*)
  val qp_to_heuristic : quant_param -> quant_heuristic_cache ref option -> thm list -> term -> term -> guess_collection
  val debug_sys : term -> term -> guess_collection

 (*The most important functions *)
  val EXTENSIBLE_QUANT_INSTANTIATE_CONV : quant_heuristic_cache ref option ->
      bool -> bool -> bool -> thm list -> quant_param -> quant_param list -> conv;
  val QUANT_INSTANTIATE_TAC             : quant_param list -> tactic;
  val ASM_QUANT_INSTANTIATE_TAC         : quant_param list -> tactic;
  val QUANT_INSTANTIATE_CONV            : quant_param list -> conv;
  val FAST_QUANT_INSTANTIATE_CONV       : quant_param list -> conv;
  val FAST_QUANT_INSTANTIATE_TAC        : quant_param list -> tactic;
  val FAST_ASM_QUANT_INSTANTIATE_TAC    : quant_param list -> tactic;
  val EXPAND_QUANT_INSTANTIATE_CONV     : quant_param list -> conv;
  val FAST_EXPAND_QUANT_INSTANTIATE_CONV: quant_param list -> conv;

  val NORE_QUANT_INSTANTIATE_CONV        : quant_param list -> conv;
  val NORE_EXPAND_QUANT_INSTANTIATE_CONV : quant_param list -> conv;


  val EXTENSIBLE_QUANT_INSTANTIATE_CONSEQ_CONV :
      quant_heuristic_cache ref option -> bool -> bool -> quant_param -> quant_param list -> ConseqConv.directed_conseq_conv;
  val EXTENSIBLE_QUANT_INSTANTIATE_STEP_CONSEQ_CONV :
      quant_heuristic_cache ref option -> bool -> quant_param -> quant_param list -> ConseqConv.directed_conseq_conv;
  val QUANT_INSTANTIATE_CONSEQ_CONV :
      quant_param list -> ConseqConv.directed_conseq_conv;
  val QUANT_INSTANTIATE_CONSEQ_TAC : quant_param list -> tactic;
  val NORE_QUANT_INSTANTIATE_CONSEQ_CONV :
      quant_param list -> ConseqConv.directed_conseq_conv;
  val FAST_QUANT_INSTANTIATE_CONSEQ_CONV :
      quant_param list -> ConseqConv.directed_conseq_conv;


  val INST_QUANT_CONV : (string * Parse.term Lib.frag list * Parse.term Parse.frag list list) list
   -> conv;
  val QUANT_TAC  : (string * Parse.term Lib.frag list * Parse.term Parse.frag list list) list
   -> tactic;

(* Predefined filters to use with filter_qp *)
val subterm_filter       : term list -> term -> term -> bool
val subterm_match_filter : term list -> term -> term -> bool
val type_filter          : hol_type list -> term -> term -> bool
val type_match_filter    : hol_type list -> term -> term -> bool
val neg_filter           : (term -> term -> bool) -> term -> term -> bool

(*combination with simplifier*)
  val QUANT_INST_ss        : quant_param list -> simpLib.ssfrag;
  val EXPAND_QUANT_INST_ss : quant_param list -> simpLib.ssfrag;
  val FAST_QUANT_INST_ss   : quant_param list -> simpLib.ssfrag;

(* Traces *)
(* "QUANT_INST_DEBUG" can be used to get debug information on
   how guesses are obtained

   "QUANT_INST___print_term_length" used for printing debug concisely


   "QUANT_INST___REC_DEPTH" can set the maximal recursion depth, default is 250.
   If the search is aborted, because the depth is not big enough, a warning
   is printed. Decrease for speed and increase if the warning appears and you want to search deeper.
*)



end
