signature ConseqConv =
sig

include Abbrev


(*
  trace "DEPTH_CONSEQ_CONV" can be used to get debug information
  on DEPTH_CONSEQ_CONV and related conversions
*)


(* A consequence conversion is a function
   that given a term t returns a theorem of the form

   |- t' ==> t (STRENGTHEN) or
   |- t ==> t' (WEAKEN) or
   |- t <=> t' (EQUIVALENT)
*)
type conseq_conv = term -> thm;


(* Directed consequence conversions allow specifying, whether
   strengthening or weakening is desired. *)
datatype CONSEQ_CONV_direction =
         CONSEQ_CONV_STRENGTHEN_direction
       | CONSEQ_CONV_WEAKEN_direction
       | CONSEQ_CONV_UNKNOWN_direction;

type directed_conseq_conv = CONSEQ_CONV_direction -> conseq_conv;


(* Some basic consequence conversions. Most are trivial,
   but useful building blocks for writing more interesting ones. *)
val FALSE_CONSEQ_CONV       : conseq_conv;
val TRUE_CONSEQ_CONV        : conseq_conv;
val REFL_CONSEQ_CONV        : conseq_conv;
val FORALL_EQ___CONSEQ_CONV : conseq_conv;
val EXISTS_EQ___CONSEQ_CONV : conseq_conv;

val TRUE_FALSE_REFL_CONSEQ_CONV : directed_conseq_conv

(* Consequence Conversions can be combined. There are similar
   operations as for conversions. *)

val CHANGED_CONSEQ_CONV    : conseq_conv -> conseq_conv;
val QCHANGED_CONSEQ_CONV   : conseq_conv -> conseq_conv;
val ORELSE_CONSEQ_CONV     : conseq_conv -> conseq_conv -> conseq_conv
val THEN_CONSEQ_CONV       : conseq_conv -> conseq_conv -> conseq_conv;
val FIRST_CONSEQ_CONV      : conseq_conv list -> conseq_conv;
val EVERY_CONSEQ_CONV      : conseq_conv list -> conseq_conv;

val FORALL_CONSEQ_CONV     : conseq_conv -> conseq_conv;
val EXISTS_CONSEQ_CONV     : conseq_conv -> conseq_conv;
val QUANT_CONSEQ_CONV      : conseq_conv -> conseq_conv;

(* Enforce a consequence conversion to operate in only one direction *)
val STRENGTHEN_CONSEQ_CONV : conseq_conv -> directed_conseq_conv;
val WEAKEN_CONSEQ_CONV     : conseq_conv -> directed_conseq_conv;


(* Rules *)
val STRENGTHEN_CONSEQ_CONV_RULE  : directed_conseq_conv -> thm -> thm;
val WEAKEN_CONSEQ_CONV_RULE      : directed_conseq_conv -> thm -> thm;


(* Tactics *)
val CONSEQ_CONV_TAC              : directed_conseq_conv -> tactic;
val ASM_CONSEQ_CONV_TAC          : (thm list -> directed_conseq_conv) -> tactic
val DISCH_ASM_CONSEQ_CONV_TAC    : directed_conseq_conv -> tactic;



(* DEPTH_CONSEQ_CONV

   For equality, it is comparatively simple to write a conversion that
   looks at subterms. For consequence conversion one needs to exploit
   semantic information about boolean operations one wants operate on.

   However, for the common operators

   - conjunction
   - disjunction
   - negation
   - implication
   - if-then-else
   - universal quantification
   - existential quantification

   this is provided by the ConseqConv library. This leads to easily usable
   consequence conversions and corresponding tactics that traverse a term.
*)

val DEPTH_CONSEQ_CONV              : directed_conseq_conv -> directed_conseq_conv;
val REDEPTH_CONSEQ_CONV            : directed_conseq_conv -> directed_conseq_conv;
val ONCE_DEPTH_CONSEQ_CONV         : directed_conseq_conv -> directed_conseq_conv;

val DEPTH_CONSEQ_CONV_TAC          : directed_conseq_conv -> tactic;
val REDEPTH_CONSEQ_CONV_TAC        : directed_conseq_conv -> tactic;
val ONCE_DEPTH_CONSEQ_CONV_TAC     : directed_conseq_conv -> tactic;

val DEPTH_STRENGTHEN_CONSEQ_CONV   : conseq_conv -> conseq_conv;
val REDEPTH_STRENGTHEN_CONSEQ_CONV : conseq_conv -> conseq_conv;


(* A bit uncommon is a generalisation of ONCE_DEPTH_CONSEQ_CONV, which at most
   performs 1 step. This generalisation allows specifying how many steps should
   at most be taken. *)
val NUM_DEPTH_CONSEQ_CONV  : directed_conseq_conv -> int ->
                             directed_conseq_conv;
val NUM_REDEPTH_CONSEQ_CONV: directed_conseq_conv -> int ->
                             directed_conseq_conv


(* The most common application of DEPTH_CONSEQ_CONV is a tool similar to
   REWRITE_CONV. The directed consequence conversion CONSEQ_TOP_REWRITE_CONV gets
   a triple (both_thmL,strengthen_thmL,weaken_thmL) of theorem lists. The theorem
   lists are preprocessed (most prominently by getting their body conjuncts, but
   also by moving quantifiers around a bit). Moreover, equivalence theorems
   might be split into two implications. The resulting theorems lists are used as follows:


   strengthen_thmL:
   These theorems are used for strengthening. This means, given a term "t0" and
   a theorem "|- t' ==> t" in the preprocessed strengthen list. Then CONSEQ_TOP_REWRITE_CONV
   tries to match t0 with t, which would result in a theorem "|- t0' ==> t0".

   weaken_thmL:
   These theorems are used for weakening.

   both_thmL:
   These theorems are used for both strengthening and weakening.

   CONSEQ_TOP_REWRITE_CONV searches (depending on the given direction) for a theorem to
   strengthen or weaken its input term with. The first one it finds is applied and the
   resulting theorem returned. If none is found, UNCHANGED is raised.

   CONSEQ_TOP_HO_REWRITE_CONV is similar, but uses higher order matching instead of
   first order one.
*)

val CONSEQ_TOP_REWRITE_CONV     : (thm list * thm list * thm list) -> directed_conseq_conv;
val CONSEQ_TOP_HO_REWRITE_CONV  : (thm list * thm list * thm list) -> directed_conseq_conv;


(* Combined with various versions of DEPTH_CONSEQ_CONV, this leads to a powerful tools for
   applying implicational theorems. *)

val CONSEQ_REWRITE_CONV         : (thm list * thm list * thm list) -> directed_conseq_conv;
val CONSEQ_HO_REWRITE_CONV      : (thm list * thm list * thm list) -> directed_conseq_conv;
val ONCE_CONSEQ_REWRITE_CONV    : (thm list * thm list * thm list) -> directed_conseq_conv;
val ONCE_CONSEQ_HO_REWRITE_CONV : (thm list * thm list * thm list) -> directed_conseq_conv;

val CONSEQ_REWRITE_TAC          : (thm list * thm list * thm list) -> tactic;
val CONSEQ_HO_REWRITE_TAC       : (thm list * thm list * thm list) -> tactic;
val ONCE_CONSEQ_REWRITE_TAC     : (thm list * thm list * thm list) -> tactic;
val ONCE_CONSEQ_HO_REWRITE_TAC  : (thm list * thm list * thm list) -> tactic;

val CONSEQ_TOP_REWRITE_TAC      : (thm list * thm list * thm list) -> tactic;
val CONSEQ_TOP_HO_REWRITE_TAC   : (thm list * thm list * thm list) -> tactic;


(* General rules and tactics. These were implemented to might be useful in general *)
val GEN_ASSUM               : term -> thm -> thm;
val GEN_IMP                 : term -> thm -> thm;
val LIST_GEN_IMP            : term list -> thm -> thm;
val GEN_EQ                  : term -> thm -> thm;
val LIST_GEN_EQ             : term list -> thm -> thm;
val EXISTS_INTRO_IMP        : term -> thm -> thm;
val LIST_EXISTS_INTRO_IMP   : term list -> thm -> thm;

val SPEC_ALL_TAC            : tactic;
val REMOVE_TRUE_TAC         : tactic;
val DISCH_ASM_CONV_TAC      : conv -> tactic;



(******************************************************************)
(******************************************************************)
(* ADVANCED USAGE                                                 *)
(******************************************************************)
(******************************************************************)


(* The functionality shown above mimics for implications some of the
   infrastructure for equations. However, for equational reasoning the
   simplifier is available, which allows to use context
   information. Something like is also beneficial for reasoning with
   implications. The implementation underlying the simple DEPTH
   conversions above allows in it's full detail:

   - using context information
   - providing a list of congruence rules
   - caching intermediate steps
   - fine control over counting steps
   - control over reiterating of already modified subterms
*)

type conseq_conv_congruence_syscall =
   term list -> thm list -> int -> CONSEQ_CONV_direction -> term -> (int * thm option)

type conseq_conv_congruence =
   thm list -> conseq_conv_congruence_syscall ->
   CONSEQ_CONV_direction -> term -> (int * thm)

type depth_conseq_conv_cache

type depth_conseq_conv_cache_opt =
   ((unit -> depth_conseq_conv_cache) * ((term * (int * thm option)) -> bool)) option

val EXT_DEPTH_NUM_CONSEQ_CONV  :
    conseq_conv_congruence list ->    (*congruence_list*)
    depth_conseq_conv_cache_opt ->    (*use cache*)
    int option ->                     (*max no of steps, NONE for unbounded *)
    bool ->                           (*redepth ?*)
    (bool * int option * (thm list -> directed_conseq_conv)) list ->
         (*conversion list:
           (1: true : apply before descending into subterms
               false : apply after returning from descend
            2: weight, how many steps are counted, 0 means that it does
               not count
            3: context -> conversion
          *)
    thm list ->                       (*context that might be used*)
    CONSEQ_CONV_direction -> term ->
    (int * thm option)
      (* number of steps taken + theorem option. NONE might be returned if nothing changed. *)


(***************)
(* Congruences *)
(***************)

(* conseq_conv_congruences are used for moving consequence conversions
   through boolean terms.

   A congruence gets 4 arguments

     context : thm list
       A list of theorems from the context it may use.

     sys : conseq_conv_congruence_syscall
       A callback for actually trying to work on subterms (see below)

     dir : CONSEQ_CONV_direction
       The direction it should work in.

     t : term
       The term to work on

   It results in the number of steps performed and a resulting theorem.
   If the congruence fails, it raises an exception.

   The job of a congruence is to call the system callback sys on suitable
   subterms and recombine the results.

   The system callback gets the following arguments

     new_context : term list
       new context information that may be assumed theorems are build
       via ASSUME from these terms, it's the job of the congruence to
       remove the resulting assumptions

     old_context : thm list
       the old context theorems that can be used

     m : int
       number of steps already taken so far

     dir : CONSEQ_CONV_direction
       the direction

     t : term
       term to work on

   The syscall returns the number of steps performed as well a
   potential resulting theorem.
*)



(* For the common operations, i.e. for

   - conjunction
   - disjunction
   - negation
   - implication
   - if-then-else
   - universal quantification
   - existential quantification

   there are already defined congruences. These come with
   different levels of using context information. If more
   context is used, potentially more can be done. However,
   there is a speed penalty. CONSEQ_CONV_get_context_congruences
   returns lists of congruences for these operations for
   different levels of using context information.
*)


datatype CONSEQ_CONV_context =
  (* do not use context at all *)
  CONSEQ_CONV_NO_CONTEXT

  (* use just the antecedents of implications *)
| CONSEQ_CONV_IMP_CONTEXT

  (* use all available context (from and, or, ...) *)
| CONSEQ_CONV_FULL_CONTEXT;


val CONSEQ_CONV_get_context_congruences :
    CONSEQ_CONV_context -> conseq_conv_congruence list;



(***************)
(* Cashing     *)
(***************)

(* There is support for caching results. A depth_conseq_conv_cache
   is a reference a dictionary for looking up previously recorded results. *)

(* make a new, empty cache *)
val mk_DEPTH_CONSEQ_CONV_CACHE : unit -> depth_conseq_conv_cache;

(* clear an existing cache, i.e. remove all entries *)
val clear_CONSEQ_CONV_CACHE     : depth_conseq_conv_cache -> unit


(* However, at top-level, no cache, but a depth_conseq_conv_cache_opt is
   passed around. If such an option is NONE, no caching is used.
   Otherwise, it consists of a function for getting a cache and a
   predicate that determines which new results are added to the cache.

   The result for getting the cache is called once before traversing
   the term begins. It can create a fresh cache or return a previously
   used cache containing already useful results. If a result is not
   found in the cache and newly computed, the predicate passed
   determines, whether it is added to the cache. *)


(* The default cache-option. It always creates a fresh cache and
   stores all results in this cache. *)
val CONSEQ_CONV_default_cache_opt : depth_conseq_conv_cache_opt

(* Always create a fresh cache and use given predicate. *)
val mk_DEPTH_CONSEQ_CONV_CACHE_OPT : ((term * (int * thm option)) -> bool) -> depth_conseq_conv_cache_opt;

(* Create a cache just once and keep it for multiple calls.
   Use the given predicate. *)
val mk_PERSISTENT_DEPTH_CONSEQ_CONV_CACHE_OPT : ((term * (int * thm option)) -> bool) -> depth_conseq_conv_cache_opt;

(* A function to clear the cache of a persistent cache-option. *)
val clear_CONSEQ_CONV_CACHE_OPT : depth_conseq_conv_cache_opt -> unit



(********************)
(* Derived DEPTH    *)
(* consequence      *)
(* conversions      *)
(********************)

(* ignore the number of steps result and raise UNCHANGED, if no thm is returned *)
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

(* Use congruences for given context level and argument consequence consequence conv
   might use context. *)
val CONTEXT_DEPTH_CONSEQ_CONV      : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> directed_conseq_conv;
val CONTEXT_REDEPTH_CONSEQ_CONV    : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> directed_conseq_conv;
val CONTEXT_ONCE_DEPTH_CONSEQ_CONV : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> directed_conseq_conv;
val CONTEXT_NUM_DEPTH_CONSEQ_CONV  : CONSEQ_CONV_context -> (thm list -> directed_conseq_conv) -> int ->
                                     directed_conseq_conv;
val CONTEXT_NUM_REDEPTH_CONSEQ_CONV: (thm list -> directed_conseq_conv) -> int ->
                                     directed_conseq_conv




(**********************)
(* Fancy REWRITE      *)
(**********************)

(* Allowing full access to all parameters leads for
   CONSEQ_REWRITE_CONV to the following function.

   Most arguments are known from EXT_DEPTH_NUM_CONSEQ_CONV or
   CONSEQ_REWRITE_CONV. the list of conversions corresponds to the
   list of directed_conseq_conv for EXT_DEPTH_NUM_CONSEQ_CONV.
   However, here really conversions, not consequence conversions are
   required. *)

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


(* Derived functions *)
val EXT_CONSEQ_REWRITE_CONV             : (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;
val EXT_CONSEQ_HO_REWRITE_CONV          : (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;
val EXT_CONTEXT_CONSEQ_REWRITE_CONV     : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;
val EXT_CONTEXT_CONSEQ_HO_REWRITE_CONV  : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> directed_conseq_conv;

val EXT_CONSEQ_REWRITE_TAC              :                        (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;
val EXT_CONTEXT_CONSEQ_REWRITE_TAC      : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;
val EXT_CONSEQ_HO_REWRITE_TAC           :                        (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;
val EXT_CONTEXT_CONSEQ_HO_REWRITE_TAC   : CONSEQ_CONV_context -> (thm list -> conv) list -> thm list -> (thm list * thm list * thm list) -> tactic;




(*************************************************************************)
(* Technical Stuff for writing own, low level consequence conversion     *)
(*************************************************************************)

val asm_marker_tm         : term
val dest_asm_marker       : term -> term * term
val is_asm_marker         : term -> bool
val mk_asm_marker         : term -> term -> term
val mk_asm_marker_random  : term -> term
val dest_neg_asm_marker   : term -> term * term
val is_neg_asm_marker     : term -> bool
val asm_marker_ELIM_CONV  : conv
val asm_marker_INTRO_CONV : term -> conv


val CONSEQ_CONV_DIRECTION_NEGATE      : CONSEQ_CONV_direction -> CONSEQ_CONV_direction;
val CONSEQ_CONV___GET_SIMPLIFIED_TERM : thm -> term -> term;
val CONSEQ_CONV___GET_DIRECTION       : thm -> term -> CONSEQ_CONV_direction;
val THEN_CONSEQ_CONV___combine        : thm -> thm -> term -> thm;
val CONSEQ_CONV___APPLY_CONV_RULE     : thm -> term -> (term -> thm) -> thm;


val step_opt_sub          : int option -> int -> int option
val step_opt_allows_steps : int option -> int -> int option -> bool


end
