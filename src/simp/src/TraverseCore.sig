(* =====================================================================
 * FILE          : TraverseCore.sig
 * DESCRIPTION   : The traversal engine for the extended entry points.
 *                 It is polymorphic in the reducer type: a client supplies
 *                 each reducer's initial context, its context collector and
 *                 how to apply it.
 * ===================================================================== *)

signature TraverseCore =
sig
  include Abbrev

  type context = exn

  (* What a reducer's apply function receives from the traversal *)
  type apply_args =
    {solver : term list -> term -> thm,
     conv : term list -> term -> thm,
     context : context,
     stack : term list,
     relation : term * (term -> thm)}

  (* Side-condition provers (TraverseExt's configured traversals) *)
  type simp_prover_ctxt =
    {stack : term list, context_thms : thm list, recurse : term -> thm}
  type ssolver = {name : string, solve : simp_prover_ctxt -> term -> thm}
  type subgoaler = simp_prover_ctxt -> term -> thm

  type child_first_policy =
    {charge : unit -> unit, keep_abstraction : term -> bool}
  datatype traversal_policy = ParentFirst | ChildFirst of child_first_policy

  (* Eta-contract the leftmost function argument that is an abstraction,
     unless it is a logical binder's or the policy keeps it *)
  val eta_argument : child_first_policy -> conv

  type 'r traversal =
    {rewriters : 'r list,
     dprocs : 'r list,
     limit : int option,
     travrules : Travrules.travrules,
     relation : term,
     initial : 'r -> context,
     addcontext : 'r -> context * thm list -> context,
     apply : 'r -> apply_args -> conv,
     subgoaler : subgoaler option,
     solvers : ssolver list}

  (* Collect context once and return a reusable conversion; congruence
     procedures are built eagerly for each traversal context. *)
  val TRAVERSE : 'r traversal -> thm list -> conv

  (* Collect the given contexts afresh at each application.  check_abort
     runs before each step; observer sees every term offered to reducers
     and the side-condition solver; root_only applies reducers at the root
     only (side conditions still use the full traversal).  Solver-only
     facts reach the prover and capture avoidance, not reducer contexts.
     An exception raised by a callback (check_abort, observer, policy) is
     re-raised with its identity even where a conversion combinator would
     have read it as failure. *)
  val TRAVERSE_WITH_CONTEXT :
    {check_abort : (unit -> unit) option, observer : (term -> unit) option,
     policy : traversal_policy, root_only : bool} ->
    'r traversal ->
    {reducer_context : thm list, solver_context : thm list} -> conv

end
