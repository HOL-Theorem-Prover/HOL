signature ConseqConv =
sig

include Abbrev


(*
  trace "DEPTH_CONSEQ_CONV" can be used to get debug information
  on DEPTH_CONSEQ_CONV and related conversions
*)


(* Types *)
datatype CONSEQ_CONV_direction =
         CONSEQ_CONV_STRENGTHEN_direction
       | CONSEQ_CONV_WEAKEN_direction
       | CONSEQ_CONV_UNKNOWN_direction;

datatype CONSEQ_CONV_context =
         (* do not use context at all *)
         CONSEQ_CONV_NO_CONTEXT
         (* use just the antecedents of implications *)
       | CONSEQ_CONV_IMP_CONTEXT
         (* use all available context (from and, or, ...) *)
       | CONSEQ_CONV_FULL_CONTEXT;

type conseq_conv = term -> thm;
type directed_conseq_conv = CONSEQ_CONV_direction -> conseq_conv;

type conseq_conv_congruence_syscall =
   term list -> thm list -> int -> CONSEQ_CONV_direction -> term -> (int * thm option)

type conseq_conv_congruence =
   thm list -> conseq_conv_congruence_syscall ->
   CONSEQ_CONV_direction -> term -> (int * thm)


(* Technical stuff that might help writing
   your own CONSEQ-CONVs, but is otherwise uninteresting *)
val CONSEQ_CONV_DIRECTION_NEGATE      : CONSEQ_CONV_direction -> CONSEQ_CONV_direction;
val CONSEQ_CONV___GET_SIMPLIFIED_TERM : thm -> term -> term;
val CONSEQ_CONV___GET_DIRECTION       : thm -> term -> CONSEQ_CONV_direction;
val THEN_CONSEQ_CONV___combine        : thm -> thm -> term -> thm;
val CONSEQ_CONV___APPLY_CONV_RULE     : thm -> term -> (term -> thm) -> thm;




(* General rules and tactics. These might be useful in general *)
val GEN_ASSUM               : term -> thm -> thm;
val GEN_IMP                 : term -> thm -> thm;
val LIST_GEN_IMP            : term list -> thm -> thm;
val GEN_EQ                  : term -> thm -> thm;
val LIST_GEN_EQ             : term list -> thm -> thm;
val EXISTS_INTRO_IMP        : term -> thm -> thm;
val LIST_EXISTS_INTRO_IMP   : term list -> thm -> thm;
val SPEC_ALL_TAC            : tactic;
val REMOVE_TRUE_TAC         : tactic;


val IMP_QUANT_CANON             : thm -> thm;
val IMP_FORALL_CONCLUSION_CANON : thm -> thm;
val IMP_EXISTS_PRECOND_CANON    : thm -> thm;



(* Basic consequence conversions; some of these are trivial, but
   useful for writing your own conseq_convs *)
val FALSE_CONSEQ_CONV       : conseq_conv;
val TRUE_CONSEQ_CONV        : conseq_conv;
val REFL_CONSEQ_CONV        : conseq_conv;
val FORALL_EQ___CONSEQ_CONV : conseq_conv;
val EXISTS_EQ___CONSEQ_CONV : conseq_conv;

val TRUE_FALSE_REFL_CONSEQ_CONV : directed_conseq_conv


(*Some things about asm_marker*)
val asm_marker_tm         : term
val dest_asm_marker       : term -> term * term
val is_asm_marker         : term -> bool
val mk_asm_marker         : term -> term -> term
val mk_asm_marker_random  : term -> term
val dest_neg_asm_marker   : term -> term * term
val is_neg_asm_marker     : term -> bool
val asm_marker_ELIM_CONV  : conv
val asm_marker_INTRO_CONV : term -> conv

(* Cache and congruence options *)

type depth_conseq_conv_cache
type depth_conseq_conv_cache_opt =
   ((unit -> depth_conseq_conv_cache) * ((term * (int * thm option)) -> bool)) option

(* make a new cache *)
val mk_DEPTH_CONSEQ_CONV_CACHE : unit -> depth_conseq_conv_cache;
(* the default cache option, a cache option is a pair,
   first is a function to create a new cache, by default
   mk_DEPTH_CONSEQ_CONV_CACHE is used, however often
   (K some_existing_cache) might be useful. The second one is
   a predicate of (t, (n, result_opt)) that determines whether
   the result that t was converted in n steps to result_opt should
   be put into the cache or not (default is (K true)).
*)
val CONSEQ_CONV_default_cache_opt : depth_conseq_conv_cache_opt


val mk_DEPTH_CONSEQ_CONV_CACHE_OPT : ((term * (int * thm option)) -> bool) -> depth_conseq_conv_cache_opt;
val mk_PERSISTENT_DEPTH_CONSEQ_CONV_CACHE_OPT : ((term * (int * thm option)) -> bool) -> depth_conseq_conv_cache_opt;

val CONSEQ_CONV_get_context_congruences :
    CONSEQ_CONV_context -> conseq_conv_congruence list;

val clear_CONSEQ_CONV_CACHE     : depth_conseq_conv_cache -> unit
val clear_CONSEQ_CONV_CACHE_OPT : depth_conseq_conv_cache_opt -> unit



(* Rewriting consequence conversions *)
val CONSEQ_REWRITE_CONV         : (thm list * thm list * thm list) -> directed_conseq_conv;
val CONSEQ_HO_REWRITE_CONV      : (thm list * thm list * thm list) -> directed_conseq_conv;
val ONCE_CONSEQ_REWRITE_CONV    : (thm list * thm list * thm list) -> directed_conseq_conv;
val ONCE_CONSEQ_HO_REWRITE_CONV : (thm list * thm list * thm list) -> directed_conseq_conv;

val EXT_CONSEQ_REWRITE_CONV             : (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;
val EXT_CONSEQ_HO_REWRITE_CONV          : (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;
val EXT_CONTEXT_CONSEQ_REWRITE_CONV     : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;
val EXT_CONTEXT_CONSEQ_HO_REWRITE_CONV  : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;


val FULL_EXT_CONSEQ_REWRITE_CONV        :
   conseq_conv_congruence list -> (* congruences *)
   depth_conseq_conv_cache_opt -> (* cache *)
   int option ->                  (* steps *)
   bool ->                        (* redepth *)
   bool ->                        (* higher order rewriting ? *)
   thm list ->                    (* context *)
   (bool * int option * (thm list -> conv)) list -> (* conversions *)
   (thm list * thm list * thm list) -> (*consequence rewrites *)
   directed_conseq_conv



val step_opt_sub          : int option -> int -> int option
val step_opt_allows_steps : int option -> int -> int option -> bool

(* Depth consequence conversions *)
val EXT_DEPTH_CONSEQ_CONV  :
    conseq_conv_congruence list ->    (*congruence_list*)
    depth_conseq_conv_cache_opt ->    (*use cache*)
    int option ->                     (*no of steps, NONE for unbounded *)
    bool ->                           (*redepth ?*)
    (bool * int option * (thm list -> directed_conseq_conv)) list ->
         (*conversion list:
           (1: apply before or after descending in subterms
            2: weight, how many steps are counted, 0 means that it does
               not count
            3: context -> conversion
          *)
    thm list ->                       (*context that might be used*)
    directed_conseq_conv

val EXT_DEPTH_NUM_CONSEQ_CONV  :
    conseq_conv_congruence list ->    (*congruence_list*)
    depth_conseq_conv_cache_opt ->    (*use cache*)
    int option ->                     (*no of steps, NONE for unbounded *)
    bool ->                           (*redepth ?*)
    (bool * int option * (thm list -> directed_conseq_conv)) list ->
         (*conversion list:
           (1: apply before or after descending in subterms
            2: weight, how many steps are counted, 0 means that it does
               not count
            3: context -> conversion
          *)
    thm list ->                       (*context that might be used*)
    CONSEQ_CONV_direction -> term ->
    (int * thm option)

val DEPTH_CONSEQ_CONV      : directed_conseq_conv -> directed_conseq_conv;
val REDEPTH_CONSEQ_CONV    : directed_conseq_conv -> directed_conseq_conv;
val ONCE_DEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv;
val NUM_DEPTH_CONSEQ_CONV  : directed_conseq_conv -> int ->
			     directed_conseq_conv;
val NUM_REDEPTH_CONSEQ_CONV: directed_conseq_conv -> int ->
			     directed_conseq_conv

val CONTEXT_DEPTH_CONSEQ_CONV      : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> directed_conseq_conv;
val CONTEXT_REDEPTH_CONSEQ_CONV    : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> directed_conseq_conv;
val CONTEXT_ONCE_DEPTH_CONSEQ_CONV : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> directed_conseq_conv;
val CONTEXT_NUM_DEPTH_CONSEQ_CONV  : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> int ->
			             directed_conseq_conv;
val CONTEXT_NUM_REDEPTH_CONSEQ_CONV: (thm list -> directed_conseq_conv) -> int ->
		         	     directed_conseq_conv

val DEPTH_STRENGTHEN_CONSEQ_CONV   : conseq_conv -> conseq_conv;
val REDEPTH_STRENGTHEN_CONSEQ_CONV : conseq_conv -> conseq_conv;




(* Combinations for consequence conversions *)
val CHANGED_CONSEQ_CONV    : conseq_conv -> conseq_conv;
val QCHANGED_CONSEQ_CONV   : conseq_conv -> conseq_conv;
val ORELSE_CONSEQ_CONV     : conseq_conv -> conseq_conv -> conseq_conv
val THEN_CONSEQ_CONV       : conseq_conv -> conseq_conv -> conseq_conv;
val FIRST_CONSEQ_CONV      : conseq_conv list -> conseq_conv;
val EVERY_CONSEQ_CONV      : conseq_conv list -> conseq_conv;

val FORALL_CONSEQ_CONV     : conseq_conv -> conseq_conv;
val EXISTS_CONSEQ_CONV     : conseq_conv -> conseq_conv;
val QUANT_CONSEQ_CONV      : conseq_conv -> conseq_conv;

val STRENGTHEN_CONSEQ_CONV : conseq_conv -> directed_conseq_conv;
val WEAKEN_CONSEQ_CONV     : conseq_conv -> directed_conseq_conv;


(* Rules *)
val STRENGTHEN_CONSEQ_CONV_RULE  : directed_conseq_conv -> thm -> thm;
val WEAKEN_CONSEQ_CONV_RULE      : directed_conseq_conv -> thm -> thm;




(* Tactics *)
val CONSEQ_CONV_TAC              : directed_conseq_conv -> tactic;
val ASM_CONSEQ_CONV_TAC          : (thm list -> directed_conseq_conv) -> tactic

val DISCH_ASM_CONV_TAC           : conv -> tactic;
val DISCH_ASM_CONSEQ_CONV_TAC    : directed_conseq_conv -> tactic;

val DEPTH_CONSEQ_CONV_TAC        : directed_conseq_conv -> tactic;
val REDEPTH_CONSEQ_CONV_TAC      : directed_conseq_conv -> tactic;
val ONCE_DEPTH_CONSEQ_CONV_TAC   : directed_conseq_conv -> tactic;
val CONSEQ_REWRITE_TAC           : (thm list * thm list * thm list) -> tactic;
val CONSEQ_HO_REWRITE_TAC        : (thm list * thm list * thm list) -> tactic;
val ONCE_CONSEQ_REWRITE_TAC      : (thm list * thm list * thm list) -> tactic;
val ONCE_CONSEQ_HO_REWRITE_TAC   : (thm list * thm list * thm list) -> tactic;

val EXT_CONSEQ_REWRITE_TAC              :                        (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;
val EXT_CONTEXT_CONSEQ_REWRITE_TAC      : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;
val EXT_CONSEQ_HO_REWRITE_TAC           :                        (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;
val EXT_CONTEXT_CONSEQ_HO_REWRITE_TAC   : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;


end

