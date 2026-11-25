(* =====================================================================
 * FILE        : simpLib.sig
 * DESCRIPTION : A programmable, contextual, conditional simplifier
 *
 * AUTHOR      : Donald Syme
 *               Based loosely on original HOL rewriting by
 *               Larry Paulson et al, and on the Isabelle simplifier.
 * =====================================================================*)


signature simpLib =
sig
 include Abbrev

   (* ---------------------------------------------------------------------
    * type simpset
    *
    * A simpset contains:
    *    - a collection of rewrite rules
    *    - a collection of equational conversions
    *    - a traversal strategy for applying them
    *
    * The traversal strategy may include other actions, especially
    * decision procedures, which can work cooperatively with
    * rewriting during simplification.
    *
    * REWRITE RULES
    *
    * Simpsets are foremost a collection of rewrite theorems stored
    * efficiently in a termnet.  These are made into conversions
    * by using COND_REWR_CONV.
    *
    * CONVERSIONS IN SIMPSETS
    *
    * Simpsets can contain arbitrary user conversions, as well as
    * rewrites and contextual-rewrites.  These conversions should
    * be thought of as infinite families of rewrites.
    *
    * Conversions can be keyed by term patterns (implemented
    * using termnets).  Thus a conversion won't even be called if
    * the target term doesn't match (in the termnet sense of matching)
    * its key.
    * ---------------------------------------------------------------------*)

 type thname = KernelSig.kernelname
 type convdata = { name: string,
                    key: (term list * term) option,
                  trace: int,
                   conv: (term list -> term -> thm) -> term list -> conv}

  type stdconvdata = { name: string,
                       pats: term list,
                       conv: conv}

  type relsimpdata = {refl: thm,
                      trans:thm,
                      weakenings:thm list,
                      subsets : thm list,
                      rewrs : thm list}

  type controlled_thm = BoundedRewrites.controlled_thm

  type ssfrag
  type simpset
  type rewrite_source

  val SSFRAG :
    {name : string option,
     convs: convdata list,
     rewrs: (thname option * thm) list,
        ac: (thm * thm) list,
    filter: (controlled_thm -> controlled_thm list) option,
    dprocs: Traverse.reducer list,
     congs: thm list} -> ssfrag

  val empty_ssfrag : ssfrag
  val ssf_upd_rewrs : ((thname option * thm) list -> (thname option * thm) list)
                      ->
                      ssfrag -> ssfrag
  val frag_rewrites : ssfrag -> thm list
  val frag_name : ssfrag -> string option

  val register_frag : ssfrag -> ssfrag
  val lookup_named_frag : string -> ssfrag option
  val all_named_frags : unit -> string list

  (*------------------------------------------------------------------------*)
  (* Easy building of common kinds of ssfrag objects                        *)
  (*------------------------------------------------------------------------*)

  val Cong        : thm -> thm
  (* A split rule for one call; see add_split *)
  val Split       : thm -> thm
  val AC          : thm -> thm -> thm
  val Excl        : string -> thm
  (* Excludes a rule, looper, solver, split rule or datatype case split
     from one call; a prefix rule:, looper:, solver:, split: or case: says
     which.  Without a prefix, the name is first read as by Excl.  The
     call fails if the target is ambiguous or matches nothing. *)
  val ExclX       : string -> thm
  val ExclSF      : string -> thm
  val Req0        : thm -> thm
  val ReqD        : thm -> thm
  val SF          : ssfrag -> thm

  val rewrites       : thm list -> ssfrag
  val rewrites_with_names : (thname * thm) list -> ssfrag
  val threaded_cong_ss : thm list -> ssfrag
  val dproc_ss       : Traverse.reducer -> ssfrag
  val ac_ss          : (thm * thm) list -> ssfrag
  val conv_ss        : convdata -> ssfrag
  val relsimp_ss     : relsimpdata -> ssfrag
  val looper_ss      : string * (simpset -> tactic) -> ssfrag
  val solver_ss      : Traverse.ssolver -> ssfrag
  val safe_solver_ss : Traverse.ssolver -> ssfrag
  val std_conv_ss    : stdconvdata -> ssfrag
  val merge_ss       : ssfrag list -> ssfrag
  val name_ss        : string -> ssfrag -> ssfrag
  val named_rewrites : string -> thm list -> ssfrag
  val named_rewrites_with_names : string -> (thname * thm) list -> ssfrag
  val named_merge_ss : string -> ssfrag list -> ssfrag
  val type_ssfrag    : hol_type -> ssfrag
  val tyi_to_ssdata  : TypeBasePure.tyinfo -> ssfrag

  val partition_ssfrags : string list -> ssfrag list ->
                          (ssfrag list * ssfrag list)

   (* ---------------------------------------------------------------------
    * mk_simpset: Joins several ssfrag fragments to make a simpset.
    * This is a "runtime" object - the ssfrag can be thought of as the
    * static, data objects.
    * Beware of duplicating information - you should only
    * merge distinct ssfrag fragments! (like BOOL_ss and PURE_ss).
    * You cannot merge simpsets with lower-case names (like bool_ss).
    *
    * The order of the merge is significant w.r.t. congruence rules
    * and rewrite makers.
    * ---------------------------------------------------------------------*)

  type weakener_data = Travrules.preorder list * thm list * Traverse.reducer

  val empty_ss        : simpset
  val ssfrags_of      : simpset -> ssfrag list
  (* The theorems a simpset's rewrites were made from, with their names,
     most recent first; and the given theorems without Once/Ntimes bounds.
     Conversions and decision procedures have no theorems here.  Fails on
     a directive: apply those with prepare_rewrite_arguments first. *)
  val rewrite_sources : simpset -> thm list ->
      (thname option * thm) list * thm list
  (* A handle for each rewrite of a simpset (e.g. for each conjunct of a
     theorem), surviving rebuilding the simpset while the rewrite is
     unchanged; aliases added by rewrite_views have none. *)
  val rewrite_source_handles : simpset -> rewrite_source list
  (* Applies the directives (Excl, SF, Split, ...) in a theorem list to a
     simpset, and returns it with the other theorems.  Bounded rewrites
     (Once, Ntimes) already in the simpset keep their remaining uses. *)
  val prepare_rewrite_arguments : simpset -> thm list -> simpset * thm list
  val source_rewrite : rewrite_source -> thname option * thm
  val same_rewrite_source : rewrite_source * rewrite_source -> bool
  (* Orders handles by installation *)
  val rewrite_source_compare : rewrite_source * rewrite_source -> order
  (* Aliases: each theorem rewrites as its handle's rewrite does, under
     its name and sharing its remaining uses, until that rewrite is
     removed or changed.  Aliases of rewrites not in the simpset, or that
     are not rewrites, are ignored. *)
  val rewrite_views : (rewrite_source * thm) list -> ssfrag
  (* Rewrites made once, with the simpset's rewrite maker, and not yet
     added to it, so that several calls can share them: wherever the
     bundle is installed, a bounded rewrite has one count of remaining
     uses.  Rebuilding a simpset resets that count, except with the
     *_preserving_controls functions. *)
  type rewrite_bundle
  val prepare_rewrite_bundle : simpset -> thm list -> rewrite_bundle
  (* Fails if a bundle occurs twice *)
  val combine_rewrite_bundles : rewrite_bundle list -> rewrite_bundle
  val rewrite_bundle_rules : rewrite_bundle ->
    (thm * rewrite_source list) list
  (* Adds a bundle's rewrites, and the aliases, to a simpset; fails if the
     bundle is already installed in it *)
  val install_rewrite_bundle : rewrite_bundle ->
    (rewrite_source * thm) list -> simpset -> simpset
  (* Disables the rewrites and their aliases; other rewrites of the same
     theorem are unaffected, and handles not in the simpset are ignored. *)
  val suspend_rewrite_sources : rewrite_source list -> simpset -> simpset
  (* What changed between two simpsets, for callers that cache results.
     keys are the patterns of the conversions added or removed.  rebuild
     holds if anything else changed that affects simplification (limit,
     settings, decision procedures, congruence rules, aliases, rewrite
     makers, conversions without a pattern).  context_sensitive holds if
     either has decision procedures, whose results may depend on any
     context theorem.  Changes to rewrites are found by comparing
     rewrite_source_handles. *)
  val rewrite_context_changes : simpset * simpset ->
    {keys : (term list * term) list, rebuild : bool,
     context_sensitive : bool}
  val mk_simpset      : ssfrag list -> simpset
  val remove_ssfrags  : string list -> simpset -> simpset
  (* As remove_ssfrags, but bounded rewrites keep their remaining uses
     rather than starting again. *)
  val remove_ssfrags_preserving_controls :
    string list -> simpset -> simpset

  (* Removes from every fragment the rewrites the predicate rejects,
     keeping the rest of the simpset's history -- what it has excluded
     by name, its limit, its rewrite maker, its strategy -- as it
     stands.  Rebuilding from ssfrags_of does not: that keeps the
     fragments alone.  Returns the simpset itself where nothing is
     rejected, and never raises Conv.UNCHANGED. *)
  val filter_rewrites :
    ((thname option * thm) -> bool) -> simpset -> simpset
  (* As filter_rewrites, but bounded rewrites keep their remaining uses *)
  val filter_rewrites_preserving_controls :
    ((thname option * thm) -> bool) -> simpset -> simpset

  (* Like remove_ssfrags, but additionally records the names so that any
     subsequent ++ of a named fragment with one of those names is silently
     a no-op.  force_add is the override for that prohibition.
     Never raises Conv.UNCHANGED. *)
  val exclude_ssfrags : string list -> simpset -> simpset
  val force_add       : simpset -> ssfrag -> simpset

  val ssfrag_names_of : simpset -> string list
  val ++              : simpset * ssfrag -> simpset  (* infix *)
  val -*              : simpset * string list -> simpset (* infix *)
  val remove_simps    : string list -> simpset -> simpset (* curried version *)
  val &&              : simpset * thm list -> simpset  (* infix *)
  val limit           : int -> simpset -> simpset
  val unlimit         : simpset -> simpset
  val add_named_rwt   : (thname * thm) -> ssfrag -> ssfrag

  val add_looper : string * (simpset -> tactic) -> simpset -> simpset
  val del_looper : string -> simpset -> simpset
  val set_looper : string * (simpset -> tactic) -> simpset -> simpset
  val add_split : thm -> simpset -> simpset
  val del_split : string -> simpset -> simpset
  val split_ss : ssfrag
  val add_unsafe_solver : Traverse.ssolver -> simpset -> simpset
  val add_safe_solver : Traverse.ssolver -> simpset -> simpset
  val set_unsafe_solvers : Traverse.ssolver list -> simpset -> simpset
  val set_safe_solvers : Traverse.ssolver list -> simpset -> simpset
  val remove_solver : string -> simpset -> simpset
  val set_subgoaler : Traverse.subgoaler -> simpset -> simpset
  val set_cond_depth : int -> simpset -> simpset
  val set_term_ord : (term * term -> order) -> simpset -> simpset
  val mk_tactic_solver : string * tactic -> Traverse.ssolver
  val clear_rules : simpset -> simpset

  val add_weakener : weakener_data -> simpset -> simpset

  val add_relsimp  : relsimpdata -> simpset -> simpset

  (* The traversal data of a simpset, without its settings, for
     Traverse.TRAVERSE.  Bounded rewrites share their remaining uses
     with the simpset. *)
  val traversedata_for_ss: simpset -> Traverse.traverse_data

  (* A simpset's settings (subgoaler, unsafe solvers, side-condition
     depth, term order), and its traversal data paired with them, for
     Traverse.XTRAVERSE. *)
  val traverseconfig_for_ss: simpset -> Traverse.traverse_config
  val xtraversedata_for_ss: simpset -> Traverse.xtraverse_data


   (* ---------------------------------------------------------------------
    * SIMP_CONV : simpset -> conv
    *
    * SIMP_CONV makes a simplification conversion from the given simpset.  The
    * conversion uses a top-depth strategy for rewriting.  It sets both
    * the solver and the depther to be SIMP_CONV itself.
    *
    * FAILURE CONDITIONS
    *
    * SIMP_CONV never fails, though it may diverge.  Beware of
    * divergence when trying to solve conditions to conditional rewrites.
    * ---------------------------------------------------------------------*)

   val SIMP_PROVE : simpset -> thm list -> term -> thm
   val SIMP_CONV  : simpset -> thm list -> conv
   (* As SIMP_CONV, but simplifies subterms before the terms containing
      them, following the policy (see Traverse.child_first_policy).
      The ETA_CONV rewrite also leaves the abstractions the policy keeps.
      Exceptions raised by the policy propagate. *)
   val SIMP_CONV_CHILD_FIRST :
     Traverse.child_first_policy -> simpset -> thm list -> conv

   (* Child-first simplification with a simpset, prepared once for
      repeated use.  normalize ths simplifies with the theorems ths as
      context; arguments ths simplifies only the arguments of a term, as
      Traverse.NORMALIZE_ARGUMENTS does.  Each conversion starts the
      simpset's bounded rewrites with their full allowance, and restores
      their counts afterwards.  may_reduce_arguments t is false only if
      no argument of t can be simplified; it is always true if the
      simpset has decision procedures, congruence rules or relations. *)
   val prepare_child_first : Traverse.child_first_policy -> simpset ->
     {normalize : thm list -> conv,
      arguments : thm list -> conv,
      may_reduce_arguments : term -> bool}
   (* As prepare_child_first, also calling the observer on the input and
      result of each conversion, and on every term offered to the
      reducers and side-condition solvers, even where they fail. *)
   val prepare_child_first_observed :
     (term -> unit) -> Traverse.child_first_policy -> simpset ->
     {normalize : thm list -> conv,
      arguments : thm list -> conv,
      may_reduce_arguments : term -> bool}

   (* ---------------------------------------------------------------------
    * SIMP_TAC : simpset -> tactic
    * ASM_SIMP_TAC : simpset -> tactic
    * FULL_SIMP_TAC : simpset -> tactic
    *
    * SIMP_TAC makes a simplification tactic from the given simpset.  The
    * tactic uses a top-depth strategy for rewriting, and will be recursively
    * reapplied when a simplification step makes a change to a term.
    * This is done in the same way as similar to TOP_DEPTH_CONV.
    *
    * ASM_SIMP_TAC draws extra rewrites (conditional and unconditional)
    * from the assumption list.  These are also added to the context that
    * will be passed to conversions.
    *
    * FULL_SIMP_TAC simplifies the assumptions one by one, before
    * simplifying the goal.  The assumptions are simplified in the order
    * that they are found in the assumption list, and the simplification
    * of each assumption is used when simplifying the next assumption.
    *
    * FAILURE CONDITIONS
    *
    * These tactics never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   (* safe chooses the solvers tried on the simplified goal: the safe or
      the unsafe ones.  Side conditions always use the unsafe solvers.
      Bounded rewrites in the theorem list, and the simpset's limit on
      loopers, apply to the whole call, including the subgoals loopers
      produce; each application of the tactic starts afresh. *)
   type simp_mode = {safe : bool}
   val GEN_SIMP_TAC  : simp_mode -> simpset -> thm list -> tactic
   val GEN_SIMP_TAC_CHILD_FIRST :
     Traverse.child_first_policy -> simp_mode -> simpset -> thm list ->
     tactic
   val SIMP_TAC      : simpset -> thm list -> tactic
   val simp_tac      : simpset -> thm list -> tactic
   val ASM_SIMP_TAC  : simpset -> thm list -> tactic
   val asm_simp_tac  : simpset -> thm list -> tactic
   val FULL_SIMP_TAC : simpset -> thm list -> tactic
   val full_simp_tac : simpset -> thm list -> tactic

   val REV_FULL_SIMP_TAC          : simpset -> thm list -> tactic
   val rev_full_simp_tac          : simpset -> thm list -> tactic
   val NO_STRIP_FULL_SIMP_TAC     : simpset -> thm list -> tactic
   val NO_STRIP_REV_FULL_SIMP_TAC : simpset -> thm list -> tactic

   type simptac_config =
        {strip : bool, elimvars : bool, droptrues : bool, oldestfirst : bool}
   val psr : simptac_config -> simpset -> tactic
     (* Pop, Simp, Rotate to back *)
   val allasms : simptac_config -> simpset -> tactic
     (* do the above to all the assumptions in turn *)
   type xsimptac_config =
        {base : simptac_config, concl_in_fixpoint : bool,
         imp_rebuild : bool, imp_premises : bool}
     (* imp_premises discharges the conclusion's leading implications
        into the assumptions before the fixpoint, so that a premise
        written as an antecedent is simplified with the others in
        context rather than only with the ones before it. *)
   val GEN_GLOBAL_SIMP_TAC :
     simp_mode -> xsimptac_config -> simpset -> thm list -> tactic
   (* As GEN_GLOBAL_SIMP_TAC, simplifying subterms first *)
   val GEN_GLOBAL_SIMP_TAC_CHILD_FIRST :
     Traverse.child_first_policy -> simp_mode -> xsimptac_config ->
     simpset -> thm list -> tactic
   (* As GEN_GLOBAL_SIMP_TAC_CHILD_FIRST, with a bundle already installed
      in the simpset (install_rewrite_bundle).  Its rewrites are used as
      they are, keeping their remaining uses, and its theorems are given
      to the solvers. *)
   val GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND :
     Traverse.child_first_policy -> simp_mode -> xsimptac_config ->
     simpset -> rewrite_bundle -> thm list -> tactic
   val global_simp_tac : simptac_config -> simpset -> thm list -> tactic
     (* do allasms until quiescence, then simp in the goal as well *)

   (* ---------------------------------------------------------------------
    * SIMP_RULE : simpset -> tactic
    * ASM_SIMP_RULE : simpset -> tactic
    *
    * Make a simplification rule from the given simpset.  The
    * rule uses a top-depth strategy for rewriting.
    *
    * FAILURE CONDITIONS
    *
    * These rules never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   val SIMP_RULE     : simpset -> thm list -> thm -> thm
   val ASM_SIMP_RULE : simpset -> thm list -> thm -> thm

   (* ---------------------------------------------------------------------*)
   (* Reporting which rewrite rules actually fired.  This is an aid for a
      human watching a simplification, so it hands the list back with the
      result rather than leaving it in a ref to be read afterwards; there
      is no flag to set and none to forget to unset.  Nested tracking
      reports only the inner extent.                                     *)
   (* ---------------------------------------------------------------------*)

   val track : ('a -> 'b) -> 'a -> 'b * thm list

   (* ---------------------------------------------------------------------*)
   (* Prettyprinters for ssfrags and simpsets.                             *)
   (* ---------------------------------------------------------------------*)

   val pp_ssfrag : ssfrag Parse.pprinter
   val pp_simpset : simpset Parse.pprinter

end
