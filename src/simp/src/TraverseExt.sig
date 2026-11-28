(* The traversal of the extension simplifier (simpExtLib).  Its reducers
   are distinct from Traverse's: lift converts an ordinary reducer, and
   there is no conversion back. *)
signature TraverseExt =
sig
  include Abbrev

  type context = TraverseCore.context
  (* A reducer's apply function also receives the side-condition depth
     limit (NONE when none is set; see Cond_rewr.stack_limit) and the order
     used for permutative rewrites.  In reducer_context_data, an unset
     limit is given as the value of Cond_rewr.stack_limit. *)
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

  type reducer
  val lift : Traverse.reducer -> reducer
  val CONTEXT_REDUCER : reducer_context_data -> reducer
  val CONFIG_REDUCER : reducer_config_data -> reducer
  (* Which of the three functions above built a reducer.  This is not a
     statement about behaviour: CONFIG_REDUCER (reducer_config_data r)
     behaves as r, but is a ConfigReducer. *)
  datatype reducer_kind = LiftedReducer | ContextReducer | ConfigReducer
  val reducer_kind : reducer -> reducer_kind
  (* A reducer's data, in either form.  Nothing is applied. *)
  val reducer_config_data : reducer -> reducer_config_data
  val reducer_data : reducer -> reducer_context_data
  val addctxt : thm list -> reducer -> reducer

  (* Side-condition solvers; see simpExtLib.add_unsafe_solver *)
  type simp_prover_ctxt = TraverseCore.simp_prover_ctxt
  type ssolver = TraverseCore.ssolver
  type subgoaler = TraverseCore.subgoaler
  type traverse_data =
    {rewriters : reducer list, limit : int option, dprocs : reducer list,
     travrules : Travrules.travrules, relation : term}
  (* The settings of simpExtLib's set_subgoaler, add_unsafe_solver,
     set_cond_depth and set_term_ord; NONE gives the default. *)
  type traverse_config =
    {subgoaler : subgoaler option, solvers : ssolver list,
     cond_depth : int option, term_ord : (term * term -> order) option}
  type xtraverse_data = traverse_data * traverse_config
  val default_config : traverse_config

  (* Adds the theorems to the reducers' contexts once, and returns a
     conversion using the default settings. *)
  val TRAVERSE : traverse_data -> thm list -> conv
  (* With the given settings.  The theorems are added to the reducers'
     contexts each time the conversion is applied. *)
  val XTRAVERSE : xtraverse_data -> thm list -> conv

  (* Child-first traversal simplifies subterms before the terms containing
     them.  The policy's charge is called before each step, and may raise
     an exception to stop the traversal; an abstraction argument of a
     function is eta-contracted before descent unless it is a binder's or
     keep_abstraction holds of the application.  Exceptions raised by the
     policy (or by an observer) propagate, rather than counting as the
     failure of a conversion. *)
  type child_first_policy = TraverseCore.child_first_policy
  datatype traversal_policy = datatype TraverseCore.traversal_policy
  (* A policy calling the function, and keeping no abstraction *)
  val charge_only : (unit -> unit) -> child_first_policy
  val keep_abstraction : child_first_policy -> term -> bool
  (* NORMALIZE_ARGUMENTS policy c t applies c to the arguments of t (or to
     its body, if t is an abstraction) but not to t itself, eta-contracting
     as the policy allows, and repeats until nothing changes. *)
  val NORMALIZE_ARGUMENTS : child_first_policy -> conv -> conv
  (* As XTRAVERSE, with the given traversal order.  The solver_context
     theorems are given to the side-condition solvers, but not added to
     the reducers' contexts. *)
  val TRAVERSE_WITH_CONTEXT : traversal_policy -> xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  (* Child-first, calling the observer on every term offered to the
     reducers and to the side-condition solvers, even where they fail. *)
  val CHILD_FIRST_WITH_OBSERVER : (term -> unit) -> child_first_policy ->
    xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  (* As CHILD_FIRST_WITH_OBSERVER, with an optional observer, also calling
     the check before each step and solver call.  The check should raise
     an exception to stop the traversal. *)
  val CHILD_FIRST_WITH_ABORT : (unit -> unit) -> (term -> unit) option ->
    child_first_policy -> xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  (* Rewrites at the root only, without descending into subterms; side
     conditions are simplified with the full traversal. *)
  val ROOT_REWRITE : xtraverse_data -> thm list -> conv
  val ROOT_REWRITE_WITH_CONTEXT : xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
end
