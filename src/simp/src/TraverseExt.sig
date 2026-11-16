(* Explicit extended traversal. Ordinary clients continue to use Traverse. *)
signature TraverseExt =
sig
  include Abbrev

  type context = TraverseCore.context
  type reducer_config_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int option,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  type reducer_context_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}

  (* Lifting is explicit and opaque: no source inventory is recovered.
     The type is abstract and no reverse adapter into Traverse is provided:
     a reducer is built by lift, CONTEXT_REDUCER or CONFIG_REDUCER, and read
     back as record data (reducer_config_data, reducer_data) or as its
     payload-free reducer_kind. *)
  type reducer
  val lift : Traverse.reducer -> reducer
  val CONTEXT_REDUCER : reducer_context_data -> reducer
  val CONFIG_REDUCER : reducer_config_data -> reducer
  (* Which of lift, CONTEXT_REDUCER or CONFIG_REDUCER built the reducer;
     addctxt preserves it and it exposes no payload. It reports provenance,
     not behaviour: CONFIG_REDUCER (reducer_config_data (lift r)) reports
     ConfigReducer, so it is not a behavioural predicate. *)
  datatype reducer_kind = LiftedReducer | ContextReducer | ConfigReducer
  val reducer_kind : reducer -> reducer_kind
  (* These projections do not invoke collectors or apply callbacks.
     NONE stays live for CONFIG_REDUCER, and is sampled immediately before
     a CONTEXT_REDUCER callback using the shared Cond_rewr.stack_limit. *)
  val reducer_config_data : reducer -> reducer_config_data
  val reducer_data : reducer -> reducer_context_data
  val addctxt : thm list -> reducer -> reducer

  type simp_prover_ctxt = TraverseCore.simp_prover_ctxt
  type ssolver = TraverseCore.ssolver
  type subgoaler = TraverseCore.subgoaler
  type traverse_data =
    {rewriters : reducer list, limit : int option, dprocs : reducer list,
     travrules : Travrules.travrules, relation : term}
  type traverse_config =
    {subgoaler : subgoaler option, solvers : ssolver list,
     cond_depth : int option, term_ord : (term * term -> order) option}
  type xtraverse_data = traverse_data * traverse_config
  val default_config : traverse_config

  (* Default configuration, eager factories, construction-once contexts. *)
  val TRAVERSE : traverse_data -> thm list -> conv
  (* Refresh reducer contexts on every application, including defaults.
     Extended entry points construct congruence factories on attempted use. *)
  val XTRAVERSE : xtraverse_data -> thm list -> conv

  type child_first_policy = TraverseCore.child_first_policy
  datatype traversal_policy = datatype TraverseCore.traversal_policy
  val charge_only : (unit -> unit) -> child_first_policy
  val keep_abstraction : child_first_policy -> term -> bool
  (* Normalize proper arguments/body while preserving the root. Repeat
     selected eta contraction and descent until stable; charge bounds passes.
     Logical binder predicates are never eta-contracted by this policy.
     Policy callback exceptions (including HOL_ERR) abort with their original
     identity, rather than becoming rejected conversion candidates. *)
  val NORMALIZE_ARGUMENTS : child_first_policy -> conv -> conv
  (* Solver-only facts extend generic solver and capture-avoidance contexts,
     without being installed in reducer-private contexts. *)
  val TRAVERSE_WITH_CONTEXT : traversal_policy -> xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  (* Observe descent/reducer attempts and side conditions, even failed ones.
     charge runs before head preservation, descent and reducer attempts.
     Observer and policy callback exceptions propagate with their original
     identity. Saved conversions refresh contexts on every application;
     recursive solver closures retain the context of their own application. *)
  val CHILD_FIRST_WITH_OBSERVER : (term -> unit) -> child_first_policy ->
    xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  (* Driver hook for a child-first owner whose native converters also call
     the policy. Check its application-local abort state before callbacks,
     including solver continuations after a failed recursive conversion.
     The check must be inert on success and rethrow a remembered failure. *)
  val CHILD_FIRST_WITH_ABORT : (unit -> unit) -> (term -> unit) option ->
    child_first_policy -> xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  (* One root rewrite without descent; side conditions use full traversal. *)
  val ROOT_REWRITE : xtraverse_data -> thm list -> conv
  val ROOT_REWRITE_WITH_CONTEXT : xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
end
