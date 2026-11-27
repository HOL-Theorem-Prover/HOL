(* =====================================================================
 * FILE          : traverse.sig
 * DESCRIPTION   : A programmable term traversal engine for hol90
 *
 * AUTHOR        : Donald Syme
 * ===================================================================== *)

signature Traverse =
sig
  include Abbrev

   (* ---------------------------------------------------------------------
    * type context
    *
    * Each reducer collects the working context on its own.
    * A context object is the current state of a single reducer.
    * ---------------------------------------------------------------------*)

  type context = exn (* well known SML hack to allow any kind of data *)

   (* ---------------------------------------------------------------------
    * Reducers
    *   These are the things that get applied to terms during
    * traversal.  They prove theorems which state that the
    * current term reduces to a related
    *
    * Each reducer manages its own storage of the working context (of one
    * of the forms above - Nb. in SML exceptions are able to contain
    * any kind of data, so contexts can be any appropriate format.  This
    * is a hack, but it is the best way to get good data hiding in SML
    * without resorting to functors)
    *
    * The fields of a reducer are:
    *
    * apply:  This is the reducer itself.  The arguments passed by
    *   the traversal engine to the reduce routine are:
    *    solver:
    *      A continuation function, to be used if the reducer needs to
    *      solve some side conditions and want to continue traversing
    *      in order to do so.  The continuation invokes traversal
    *      under equality, then calls EQT_ELIM.
    *
    *      At the moment the continuation is primarily designed to
    *      be used to solve side conditions in context.
    *
    *      Note that this function is *not* the same as
    *      the congruence side condition solver.
    *
    *    context:
    *      The reducer's current view of the context, as
    *      collected by its "addcontext" function.
    *    term list:
    *      The current side condition stack, which grows as nested calls
    *      to the solver are made.
    *
    * conv:
    *   A continuation function, to be used if the reducer
    *   wants to continue traversing. The continuation invokes traversal
    *   under equality. Similar to solver, but does not call EQT_ELIM.
    *
    * addcontext: routine is invoked every time more context is added
    *   to the current environment by virtue of congruence routines.
    *
    * initial:  The inital context.
    * ---------------------------------------------------------------------*)

  (* A CONTEXT_REDUCER or CONFIG_REDUCER is also given the traversal's
     side-condition depth limit and the order used for permutative
     rewrites (see TRAVERSE_WITH_CONTEXT).  An unset limit is NONE for a
     CONFIG_REDUCER, and the value of Cond_rewr.stack_limit for a
     CONTEXT_REDUCER. *)
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

  datatype reducer = REDUCER of {
         name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 conv: term list -> term -> thm,
                 context: context,
                 stack:term list,
                 relation : (term * (term -> thm))} -> conv
       }
    | CONTEXT_REDUCER of reducer_context_data
    | CONFIG_REDUCER of reducer_config_data

  (* A reducer's data, in either form.  Nothing is applied. *)
  val reducer_config_data : reducer -> reducer_config_data
  val reducer_data : reducer -> reducer_context_data
  (* A CONTEXT_REDUCER or CONFIG_REDUCER is given the default depth and
     term order *)
  val dest_reducer : reducer ->
        {name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 conv: term list -> term -> thm,
                 context: context,
                 stack:term list,
                 relation : (term * (term -> thm))} -> conv}

  val addctxt : thm list -> reducer -> reducer

 (* ----------------------------------------------------------------------
     TRAVERSE : {rewriters: reducer list,
                 dprocs: reducer list,
                 travrules: travrules,
                 relation: term,
                 limit : int option}
                -> thm list -> conv

     Implements a procedure which tries to prove a term is related
     to a (simpler) term by the relation given in the travrules.
     This is done by traversing the term, applying the
     procedures specified in the travrules at certain subterms.
     The traversal strategy is similar to TOP_DEPTH_CONV.

     The traversal has to be justified by congruence rules.
     These are also in the travrules.  See "Congprocs" for a more
     detailed description of congruence rules.

     In the case of rewriting and simplification, the relation used is
     equality (--`$=`--).  However traversal can also be used with
     other congruences and preorders.

     The behaviour of TRAVERSE depends almost totally on what
     is contained in the input travrules.

     The theorem list is a set of theorems to add initially as context
     to the traversal.

     FAILURE CONDITIONS

     TRAVERSE never fails, though it may diverge or raise an exception
     indicating that a term is unchanged by the traversal.

     Bad congruence rules may cause very strange behaviour.
    ---------------------------------------------------------------------- *)

   type traverse_data = {rewriters: reducer list,
                         limit : int option,
                         dprocs: reducer list,
                         travrules: Travrules.travrules,
                         relation: term};

   val TRAVERSE : traverse_data -> thm list -> conv

 (* ----------------------------------------------------------------------
     Configured traversals

     XTRAVERSE (data,config) traverses as TRAVERSE does, except that

     - a side condition of a reducer or congruence rule is simplified by
       the subgoaler (given the condition, the side-condition stack, the
       context theorems and the traversal itself as recurse), or by the
       traversal if there is none; unless that gives T, the solvers are
       tried in turn on the result.  Without a subgoaler or solvers, a
       side condition is proved as TRAVERSE proves it.

     - cond_depth and term_ord are given to CONTEXT_REDUCER and
       CONFIG_REDUCER reducers (term_ord defaults to
       Cond_rewr.ac_term_ord).

     - the theorems are added to the reducers' contexts each time the
       conversion is applied.  TRAVERSE adds them once.

     TRAVERSE_WITH_CONTEXT policy xdata {reducer_context, solver_context}
     is XTRAVERSE with the given order: ChildFirst {charge,
     keep_abstraction} simplifies the subterms of a term before the
     reducers see the term itself.  The charge is called before each step,
     and may raise an exception to stop the traversal.  Before descending
     into an application, an abstraction argument that is not a binder's
     (!, ?, @) is eta-contracted, unless keep_abstraction holds of the
     application.  The reducer_context theorems are added to the reducers'
     contexts and given to the subgoaler and solvers; the solver_context
     theorems are given only to the subgoaler and solvers.

     CHILD_FIRST_WITH_OBSERVER calls the observer on every term offered to
     the reducers and to the side-condition solvers, even where they fail;
     CHILD_FIRST_WITH_ABORT also calls the check before each step and
     solver call.  ROOT_REWRITE applies the reducers at the root of the
     term only; side conditions are still simplified by the full
     traversal, which for ROOT_REWRITE_WITH_CONTEXT follows the given
     policy, charging it for the root attempt too.  Exceptions raised
     by a policy, an observer or a check propagate out of the traversal
     unchanged, even where a conversion combinator would have read them
     as a failure.

     eta_argument policy contracts the rightmost abstraction argument
     that the ChildFirst policy would contract, failing if there is none.
     NORMALIZE_ARGUMENTS policy c t applies c to the arguments of t (or to
     its body, if t is an abstraction) but not to t itself, eta-contracting
     as the policy allows, and repeats until nothing changes.
    ---------------------------------------------------------------------- *)

   type simp_prover_ctxt =
        {stack : term list, context_thms : thm list, recurse : term -> thm}
   type ssolver = {name : string, solve : simp_prover_ctxt -> term -> thm}
   type subgoaler = simp_prover_ctxt -> term -> thm

   (* NONE gives the default *)
   type traverse_config =
        {subgoaler : subgoaler option, solvers : ssolver list,
         cond_depth : int option, term_ord : (term * term -> order) option}
   type xtraverse_data = traverse_data * traverse_config
   val default_config : traverse_config

   type child_first_policy =
        {charge : unit -> unit, keep_abstraction : term -> bool}
   datatype traversal_policy =
            ParentFirst
          | ChildFirst of child_first_policy
   (* A policy calling the function, and keeping no abstraction *)
   val charge_only : (unit -> unit) -> child_first_policy

   val XTRAVERSE : xtraverse_data -> thm list -> conv
   val TRAVERSE_WITH_CONTEXT : traversal_policy -> xtraverse_data ->
       {reducer_context : thm list, solver_context : thm list} -> conv
   val CHILD_FIRST_WITH_OBSERVER : (term -> unit) -> child_first_policy ->
       xtraverse_data ->
       {reducer_context : thm list, solver_context : thm list} -> conv
   val CHILD_FIRST_WITH_ABORT : (unit -> unit) -> (term -> unit) option ->
       child_first_policy -> xtraverse_data ->
       {reducer_context : thm list, solver_context : thm list} -> conv
   val ROOT_REWRITE : xtraverse_data -> thm list -> conv
   val ROOT_REWRITE_WITH_CONTEXT : traversal_policy -> xtraverse_data ->
       {reducer_context : thm list, solver_context : thm list} -> conv
   val eta_argument : child_first_policy -> conv
   val NORMALIZE_ARGUMENTS : child_first_policy -> conv -> conv

end (* sig *)
