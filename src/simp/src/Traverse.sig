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
    * addcontext: routine is invoked every time more context is added
    *   to the current environment by virtue of congruence routines.
    *
    * initial:  The inital context.
    * ---------------------------------------------------------------------*)

  datatype reducer = REDUCER of {
         name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 context: context,
                 stack:term list,
                 relation : (term * (term -> thm))} -> conv
       }

  val dest_reducer : reducer ->
        {name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
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

end (* sig *)
