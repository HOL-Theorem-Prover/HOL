(* =====================================================================
 * FILE          : traverse.sml
 * DESCRIPTION   : A programmable term traversal engine
 *
 * AUTHOR        : Donald Syme
 *                 Based loosely on original HOL rewriting by
 *                 Larry Paulson et al.
 * ===================================================================== *)

(* =====================================================================
 * The Traversal/Reduction Engine.  Its pretty simple really
 *   - start with an intial context
 *   - collect context that arises from congruence rules
 *   - apply reducers where possible, "rewriters" at high priority and
 *     "dprocs" at low.
 * =====================================================================*)


structure Traverse :> Traverse =
struct

open HolKernel Drule Conv Psyntax Abbrev liteLib Trace Travrules Opening;

infix THENQC THENCQC ORELSEC IFCQC

val ERR   = mk_HOL_ERR "Traverse" ;

val equality = boolSyntax.equality;

(* ---------------------------------------------------------------------
 * reducers and contexts
 * ---------------------------------------------------------------------*)

type context = exn   (* well known SML hack to allow any kind of data *)

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

datatype reducer =
  REDUCER of {name : string option,
              initial: context,
              addcontext : context * Thm.thm list -> context,
              apply: {solver:term list -> term -> thm,
                      conv: term list -> term -> thm,
                      context: context,
                      stack: term list, relation : term * (term -> thm)} -> conv
              }
  | CONTEXT_REDUCER of reducer_context_data
  | CONFIG_REDUCER of reducer_config_data

fun reducer_config_data (CONFIG_REDUCER r) = r
  | reducer_config_data (REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,...} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation}}
  | reducer_config_data
      (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=case cond_depth of NONE => !Cond_rewr.stack_limit
                                           | SOME n => n}}

fun reducer_data r =
  let val {name,initial,addcontext,apply} = reducer_config_data r
  in
    {name=name, initial=initial, addcontext=addcontext,
     apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
       apply {solver=solver,conv=conv,context=context,stack=stack,
              relation=relation,term_ord=term_ord,
              cond_depth=SOME cond_depth}}
  end

fun addctxt ths (REDUCER {name,initial,addcontext,apply}) =
    REDUCER{name = name, initial = addcontext(initial,ths), apply = apply,
            addcontext = addcontext}
  | addctxt ths (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
    CONTEXT_REDUCER {name=name, initial=addcontext (initial,ths),
                     addcontext=addcontext, apply=apply}
  | addctxt ths (CONFIG_REDUCER {name,initial,addcontext,apply}) =
    CONFIG_REDUCER {name=name, initial=addcontext (initial,ths),
                    addcontext=addcontext, apply=apply}

(* The traversal loop sees every reducer as a REDUCER, closed over the
   traversal's side-condition depth and term order.  An unset depth
   reaches a CONFIG_REDUCER as NONE: rewrites read Cond_rewr.stack_limit
   themselves, at each application. *)
fun plain_reducer_data _ _ (REDUCER x) = x
  | plain_reducer_data cond_depth term_ord
      (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation} =>
         apply {solver=solver, conv=conv, context=context, stack=stack,
                cond_depth=(case cond_depth of
                                NONE => !Cond_rewr.stack_limit
                              | SOME n => n),
                term_ord=term_ord, relation=relation}}
  | plain_reducer_data cond_depth term_ord
      (CONFIG_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation} =>
         apply {solver=solver, conv=conv, context=context, stack=stack,
                cond_depth=cond_depth, term_ord=term_ord,
                relation=relation}}

fun plain_reducer cond_depth term_ord (r as REDUCER _) = r
  | plain_reducer cond_depth term_ord r =
      REDUCER (plain_reducer_data cond_depth term_ord r)

fun dest_reducer r = plain_reducer_data NONE Cond_rewr.ac_term_ord r

(* ---------------------------------------------------------------------
 * Configured traversals: side-condition provers, child-first order,
 * root-only rewriting, and callbacks.
 * ---------------------------------------------------------------------*)

type simp_prover_ctxt =
  {stack : term list, context_thms : thm list, recurse : term -> thm}
type ssolver = {name : string, solve : simp_prover_ctxt -> term -> thm}
type subgoaler = simp_prover_ctxt -> term -> thm

type child_first_policy =
  {charge : unit -> unit, keep_abstraction : term -> bool}
datatype traversal_policy = ParentFirst | ChildFirst of child_first_policy

fun charge_only charge = {charge=charge, keep_abstraction=fn _ => false}

type traverse_config =
  {subgoaler : subgoaler option, solvers : ssolver list,
   cond_depth : int option, term_ord : (term * term -> order) option}

val default_config : traverse_config =
  {subgoaler=NONE, solvers=[], cond_depth=NONE, term_ord=NONE}

(* How one traversal runs *)
type run_config =
  {policy : traversal_policy, subgoaler : subgoaler option,
   solvers : ssolver list, root_only : bool,
   check_abort : (unit -> unit) option, observer : (term -> unit) option}

val plain_run : run_config =
  {policy = ParentFirst, subgoaler = NONE, solvers = [], root_only = false,
   check_abort = NONE, observer = NONE}


(* ---------------------------------------------------------------------
 * Traversal states
 *    - stores the state of the reducers during the simpl. process
 * ---------------------------------------------------------------------*)

datatype trav_state =
  TSTATE of {relation_info : preorder,
             relation : term,
             contexts1 : context list,
             contexts2 : context list,
             context_thms : thm list,
             freevars : term list};

fun initial_context {rewriters:reducer list,
                     dprocs:reducer list,
                     travrules=TRAVRULES tsdata,
                     relation, limit} =
  TSTATE{contexts1=map (#initial o dest_reducer) rewriters,
         contexts2=map (#initial o dest_reducer) dprocs,
         context_thms=[],
         freevars=[],
         relation_info = find_relation relation (#relations tsdata),
         relation = relation};

(* ---------------------------------------------------------------------
 * add_context
 *
 * ---------------------------------------------------------------------*)

(* With collect_thms, the theorems are also kept for the side-condition
   provers of a configured traversal. *)
(* The side-condition provers see a bounded rewrite without its bound *)
fun unbounded th = #1 (BoundedRewrites.DEST_BOUNDED th) handle HOL_ERR _ => th

fun add_context collect_thms rewriters dprocs = let
  val rewrite_collectors' = map (#addcontext o dest_reducer) rewriters
  val dproc_collectors' = map (#addcontext o dest_reducer) dprocs
  fun doit (context, thms) = let
    val TSTATE {contexts1,contexts2,context_thms,freevars,relation_info,
                relation} = context
  in
    if null thms then context
    else let
        val more_freevars = free_varsl (flatten (map hyp thms))
        val _ = map (fn thm => trace(2,MORE_CONTEXT thm)) thms
        fun mk_privcontext maker privcontext = maker (privcontext,thms)
        val newcontexts1 =
          if null thms then contexts1
          else map2 mk_privcontext rewrite_collectors' contexts1
        val newcontexts2 =
          if null thms then contexts2
          else map2 mk_privcontext dproc_collectors' contexts2
        val newfreevars =
          if null more_freevars then freevars
          else more_freevars@freevars
      in
        TSTATE{contexts1=newcontexts1,
               contexts2=newcontexts2,
               context_thms=if collect_thms then map unbounded thms @
                                                 context_thms
                            else context_thms,
               freevars=newfreevars,
               relation=relation, relation_info = relation_info}
      end
  end
in
  doit
end

(* Theorems for the side-condition provers (and for capture avoidance
   under binders) that the reducers do not see. *)
fun add_solver_context collect_thms (context, thms) =
  if null thms then context
  else
    let
      val TSTATE {contexts1,contexts2,context_thms,freevars,
                  relation_info,relation} = context
      val more_freevars =
        HOLset.listItems (FVL (flatten (map hyp thms)) empty_tmset)
      val _ = map (fn thm => trace(2,MORE_CONTEXT thm)) thms
    in
      TSTATE
        {contexts1=contexts1, contexts2=contexts2,
         context_thms=if collect_thms then context_thms @ thms
                      else context_thms,
         freevars=freevars @ more_freevars,
         relation=relation, relation_info=relation_info}
    end


(* ---------------------------------------------------------------------
 * get_relation
 *
 * ---------------------------------------------------------------------*)

fun get_relation (TRAVRULES{relations,...}) rel =
    let val PREORDER(_,TRANS,refl) = find_relation rel relations
    in PREORDER (rel,TRANS,refl) end

(* ---------------------------------------------------------------------
 * Quick, General conversion routines.  These work for any preorder,
 * not just equality.
 * ---------------------------------------------------------------------*)

fun GEN_THENQC (PREORDER(_,TRANS,_)) (conv1,conv2) tm =
  let val th1 = conv1 tm
  in TRANS th1 (conv2 (rand (concl th1)))
     handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 tm

fun GEN_THENCQC  (PREORDER(_,TRANS,_)) (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2(rand(concl th1))
     in TRANS th1 th2
     end
     handle HOL_ERR _ => th1
  end;;

(* perform continuation with argumnt indicating whether a change occurred *)
fun GEN_IFCQC  (PREORDER(_,TRANS,_)) (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2 true (rand(concl th1))
     in TRANS th1 th2
     end
     handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 false tm;;


fun GEN_REPEATQC rel =
   let val op THENCQC = GEN_THENCQC rel
       fun REPEATQC conv tm =
           (conv THENCQC (REPEATQC conv)) tm
   in REPEATQC
   end;

(* This code is used just once, to do the right thing with the
   application of congruence rules: if a congruence succeeds by not
   changing anything, then don't go onto try other congruences.  Doing
   so will ultimately lead to the standard equality congruences being
   used, and this traversal of the term will result in basically all
   of the succeeding congruence's work being done again.  If the
   sub-terms include further matches for the first congruence (as in p
   ==> q ==> r, say), then you'll get an explosion of work being
   duplicated.

   Note that the exception being caught is exactly that generated by
   Opening.CONGPROC, so there's a tight link between there and here.
   Don't change one without changing the other! *)

fun FIRSTCQC_CONV [] t = failwith "no conversion worked"
  | FIRSTCQC_CONV (c::cs) t = let
    in
      c t
      handle UNCHANGED => failwith "unchanged" (* Need to raise a HOL_ERR *)
           | HOL_ERR _ => FIRSTCQC_CONV cs t
    end

(* And another thing.  The current simplifer doesn't allow users to
   get their hands on the possibility of flipping to relations other
   than equality.  This means that weakenprocs below are always [].
   If this was to change, then the code probably should still use
   FIRST_CONV, and not FIRSTCQC_CONV above because weakening
   congruences should probably all get a bite at the cherry. *)

fun mapfilter2 f (h1::t1) (h2::t2) =
      let val X = mapfilter2 f t1 t2
      in f h1 h2::X handle Interrupt => raise Interrupt | _ => X
      end
  | mapfilter2 f _ _ = [];

(* A function argument written as [\x. f x] names the same head as [f].
   Contracting it before visiting the body keeps that head available to a
   parent rewrite unless the policy keeps the abstraction. *)
fun eta_argument (policy : child_first_policy) tm =
  if is_comb tm then
    if is_abs (rand tm) andalso
       not (boolSyntax.is_exists tm orelse
            boolSyntax.is_forall tm orelse boolSyntax.is_select tm)
       andalso not (#keep_abstraction policy tm)
    then
      (RAND_CONV ETA_CONV ORELSEC RATOR_CONV (eta_argument policy)) tm
    else RATOR_CONV (eta_argument policy) tm
  else NO_CONV tm

(* ---------------------------------------------------------------------
 * TRAVERSE_IN_CONTEXT
 *
 * NOTES
 *   - Rewriters/Dprocs should always fail if unchanged (but not with
 *     UNCHANGED).
 *   - Congruence rule procs should only fail if they do not match.
 *     They can fail with UNCHANGED if nothing changes.
 *   - The depther should only fail with UNCHANGED.
 *   - A plain traversal (parent-first, no abort check, no observer)
 *     cannot abort, and skips the abort bookkeeping on its hot paths.
 *   - With eager, the congruence procedures are built once per context;
 *     otherwise each time a descent is attempted, after the policy's
 *     charge.
 * ---------------------------------------------------------------------*)

fun TRAVERSE_IN_CONTEXT eager (config : run_config) limit rewriters
                        dprocs travrules rel stack ctxt tm = let
  open Uref
  val {policy,subgoaler,solvers,root_only,check_abort=check_external_abort,
       observer} = config
  val TRAVRULES {relations,congprocs,weakenprocs,...} = travrules
  val configured = not (null solvers) orelse isSome subgoaler
  val add_context' = add_context configured rewriters dprocs
  val get_relation' = get_relation travrules
  val lim_r = Uref.new limit
  val plain =
      case (check_external_abort,observer,policy) of
          (NONE,NONE,ParentFirst) => true
        | _ => false
  (* Conditional rewriting can turn a callback's exception into HOL_ERR,
     which reducer dispatch reads as a failed attempt.  Keep the first
     callback exception and raise it at the end. *)
  val aborted = ref (NONE : exn option)
  fun protected callback argument =
    case !aborted of
        SOME e => raise e
      | NONE => callback argument
          handle e => (aborted := SOME e; raise e)
  fun check_abort () =
    case check_external_abort of
        NONE => (case !aborted of NONE => () | SOME e => raise e)
      | SOME check => protected check ()
  val policy =
    case policy of
        ParentFirst => ParentFirst
      | ChildFirst {charge,keep_abstraction} =>
          ChildFirst {charge=charge,
                      keep_abstraction=protected keep_abstraction}
  fun check r = case !r of NONE => ()
    | SOME n => if n <= 0 then
                               (trace(2,TEXT "Limit exhausted");
                                raise ERR "TRAVERSE_IN_CONTEXT"
                                          "Limit exhausted")
                             else ()
  fun dec r = case !r of NONE => ()
    | SOME n => r := SOME (n - 1)
  fun observe tm =
    (check_abort ();
     case observer of
        NONE => ()
      | SOME visit => protected visit tm)
  fun charge tm =
    (check_abort ();
     case policy of
        ParentFirst => ()
      | ChildFirst {charge,...} =>
          (observe tm; protected charge ()))
  (* The root_only entry applies the reducers at the root only; every
     recursive context, side conditions included, uses the full loop. *)
  fun trav_with_rel select_root rel_info stack context  = let
    val PREORDER(relname , _, _) = rel_info
    fun apply_relation f = f relname
    val congprocs' = mapfilter apply_relation congprocs
    val weakenprocs' = mapfilter apply_relation weakenprocs
    val op IFCQC = GEN_IFCQC rel_info
    val op THENCQC = GEN_THENCQC rel_info
    val op THENQC = GEN_THENQC rel_info
    val REPEATQC = GEN_REPEATQC rel_info
    fun mkrefl t = let
        val PREORDER(_, _, irefl) = rel_info
    in
        irefl {Rinst = relname, arg = t}
    end

    fun trav stack context = trav_entry false stack context
    and trav_entry select_root stack context = let
      val TSTATE {contexts1,contexts2,context_thms,freevars,...} = context
      fun trav_with_rel' new_relation stack context =
          if samerel relname new_relation then trav stack context
          else
            trav_with_rel false (get_relation' new_relation) stack context

      (* A side condition is first simplified (by the subgoaler, or the
         traversal itself); what is left that is not T goes to the
         solvers in turn. *)
      fun prove_condition stack tm = let
        fun recurse tm = let
          val _ = check_abort ()
          val old = !lim_r
        in
          trav_with_rel' equality stack context tm
          handle HOL_ERR _ => (lim_r := old; REFL tm)
        end
        val prover_ctxt =
          {stack=stack, context_thms=context_thms, recurse=recurse}
        fun first_solver [] _ =
              raise ERR "TRAVERSE_IN_CONTEXT" "Unsolved condition"
          | first_solver (({solve,...} : ssolver) :: rest) tm =
              (check_abort (); solve prover_ctxt tm)
              handle HOL_ERR _ => first_solver rest tm
        val eq = case subgoaler of
                     NONE => recurse tm
                   | SOME subgoal =>
                       (check_abort (); subgoal prover_ctxt tm)
        val tm' = rand (concl eq)
      in
        if aconv tm' boolSyntax.T then EQT_ELIM eq
        else
          (if plain orelse aconv tm' tm then () else observe tm';
           EQ_MP (SYM eq) (first_solver solvers tm'))
      end
      fun ctxt_solver stack tm = let
        val _ = if plain then () else observe tm
        val old = !lim_r
      in
        (if configured then prove_condition stack tm
         else EQT_ELIM (trav_with_rel' equality stack context tm))
        handle e as HOL_ERR _ => (lim_r := old ; raise e)
      end
      fun ctxt_conv stack tm = let
        val old = !lim_r
      in
        trav_with_rel' equality stack context tm
        handle e as HOL_ERR _ => (lim_r := old ; raise e)
      end
      fun apply_reducer (REDUCER rdata) context tm =
          ((if plain then () else charge tm);
           (#apply rdata) {solver=ctxt_solver,
                           conv=ctxt_conv,
                           context=context,
                           stack=stack, relation=(relname, mkrefl)}
                          tm before
           dec lim_r)
        | apply_reducer _ _ _ =
            raise ERR "TRAVERSE_IN_CONTEXT" "not a plain reducer"
      fun high_priority tm =
          (check lim_r;
           FIRST_CONV (mapfilter2 apply_reducer rewriters contexts1) tm)
      fun low_priority tm =
          (check lim_r ;
           FIRST_CONV (mapfilter2 apply_reducer dprocs contexts2) tm)
      fun depther (thms,relation) =
          ((if plain then () else check_abort ());
           trav_with_rel' relation stack (add_context' (context,thms)))
      val congproc_args =
          {solver=(fn tm => ctxt_solver stack tm), (* do not eta-convert! *)
           depther=depther,
           freevars=freevars}
      fun apply_congproc congproc =
        if plain then congproc congproc_args
        else let
          val _ = check_abort ()
          val conversion = congproc congproc_args
        in
          (* FIRSTCQC_CONV reads HOL_ERR as a rejection, so check before
             each use of a procedure built earlier. *)
          fn tm => (check_abort (); conversion tm)
        end
      val (descend,weaken) =
        if eager then
          (FIRSTCQC_CONV (mapfilter apply_congproc congprocs'),
           FIRST_CONV (mapfilter apply_congproc weakenprocs'))
        else
          (fn tm =>
             ((if plain then () else charge tm);
              FIRSTCQC_CONV (mapfilter apply_congproc congprocs') tm),
           fn tm =>
             ((if plain then () else charge tm);
              FIRST_CONV (mapfilter apply_congproc weakenprocs') tm))

      fun loop tm = let
        val conv =
          case policy of
              ParentFirst =>
                REPEATQC high_priority THENQC
                (descend IFCQC
                  (fn change =>
                    ((if change then high_priority else NO_CONV) ORELSEC
                     low_priority ORELSEC weaken) THENCQC loop))
               (* THENCQC above causes the loop to happen only if
                  the stuff before it hasn't raised an exception *)
            | ChildFirst child_policy =>
                let
                  val after_children =
                    descend IFCQC
                      (fn _ =>
                        (high_priority ORELSEC low_priority ORELSEC weaken)
                        THENCQC loop)
                  fun preserve_head t =
                    (charge t; eta_argument child_policy t)
                in
                  if is_comb tm then
                    (preserve_head THENCQC loop) ORELSEC after_children
                  else after_children
                end
      in
        ((if plain then () else check_abort ());
         trace(4,REDUCE ("Reducing",tm)); conv tm)
      end;
    in
      if select_root then high_priority ORELSEC low_priority else loop
    end
  in
    trav_entry select_root stack context
  end
  val entry = trav_with_rel root_only (get_relation' rel) stack ctxt
in
  if plain then entry tm
  else
    let
      val th = entry tm
    in
      case !aborted of NONE => th | SOME e => raise e
    end
    handle e =>
      (case !aborted of NONE => raise e | SOME original => raise original)
end

(* ---------------------------------------------------------------------
 * TRAVERSE
 *
 * ---------------------------------------------------------------------*)
type traverse_data = {limit : int option,
                      rewriters: reducer list,
                      dprocs: reducer list,
                      travrules: Travrules.travrules,
                      relation: term};
type xtraverse_data = traverse_data * traverse_config

fun plain_data
      ({limit,rewriters,dprocs,travrules,relation} : traverse_data)
      ({cond_depth,term_ord,...} : traverse_config) : traverse_data =
  let
    val term_ord = Option.getOpt (term_ord, Cond_rewr.ac_term_ord)
    val convert = map (plain_reducer cond_depth term_ord)
  in
    {rewriters=convert rewriters, dprocs=convert dprocs, limit=limit,
     travrules=travrules, relation=relation}
  end

(* TRAVERSE adds the theorems to the contexts once, before returning a
   conversion, and builds the congruence procedures eagerly. *)
fun TRAVERSE data thms =
   let
     val data as {limit,dprocs,rewriters,travrules,relation} =
         plain_data data default_config
     val context' =
         add_context false rewriters dprocs (initial_context data,thms)
   in
     TRAVERSE_IN_CONTEXT true plain_run limit rewriters dprocs travrules
                         relation [] context'
   end;

(* The configured entry points add the theorems to the contexts at each
   application. *)
fun GEN_TRAVERSE_WITH_CONTEXT check_abort observer policy root_only
      ((data,config as {subgoaler,solvers,...}) : xtraverse_data)
      {reducer_context,solver_context} =
   let
     val run = {policy=policy, subgoaler=subgoaler, solvers=solvers,
                root_only=root_only, check_abort=check_abort,
                observer=observer}
     val data as {limit,dprocs,rewriters,travrules,relation} =
         plain_data data config
     val collect = not (null solvers) orelse isSome subgoaler
   in
     fn tm =>
       let
         val _ = case check_abort of NONE => () | SOME check => check ()
         val context' =
           add_solver_context collect
             (add_context collect rewriters dprocs
                (initial_context data,reducer_context),
              solver_context)
       in
         TRAVERSE_IN_CONTEXT false run limit rewriters dprocs travrules
                             relation [] context' tm
       end
   end

fun GEN_TRAVERSE policy root_only xdata thms =
  GEN_TRAVERSE_WITH_CONTEXT NONE NONE policy root_only xdata
    {reducer_context=thms,solver_context=[]}

val XTRAVERSE = GEN_TRAVERSE ParentFirst false
val ROOT_REWRITE = GEN_TRAVERSE ParentFirst true
fun TRAVERSE_WITH_CONTEXT policy =
  GEN_TRAVERSE_WITH_CONTEXT NONE NONE policy false
fun CHILD_FIRST_WITH_ABORT check_abort observer policy =
  GEN_TRAVERSE_WITH_CONTEXT (SOME check_abort) observer (ChildFirst policy)
    false
fun CHILD_FIRST_WITH_OBSERVER observe policy =
  GEN_TRAVERSE_WITH_CONTEXT NONE (SOME observe) (ChildFirst policy) false
val ROOT_REWRITE_WITH_CONTEXT =
  GEN_TRAVERSE_WITH_CONTEXT NONE NONE ParentFirst true

fun NORMALIZE_ARGUMENTS (policy : child_first_policy) child tm =
  let
    (* TRY_CONV and eta fallback treat HOL_ERR as conversion failure, not
       as a policy abort. Keep policy failures across those combinators.
       This state belongs to one application, including reentrant calls. *)
    val aborted = ref (NONE : exn option)
    fun protected callback argument =
      case !aborted of
          SOME e => raise e
        | NONE => callback argument
            handle e => (aborted := SOME e; raise e)
    val policy = {charge=protected (#charge policy),
                  keep_abstraction=protected (#keep_abstraction policy)}
    fun check_abort () =
      case !aborted of NONE => () | SOME e => raise e
    fun guarded_child tm = (check_abort (); child tm)
    fun arguments tm =
      (check_abort ();
       if is_comb tm then
         Conv.THENC (RATOR_CONV arguments,
                     RAND_CONV (TRY_CONV guarded_child)) tm
       else if is_abs tm then ABS_CONV (TRY_CONV guarded_child) tm
       else REFL tm)
    fun normalize tm =
      let
        val _ = #charge policy ()
        val eta = QCONV (TRY_CONV (eta_argument policy)) tm
        val result = TRANS eta (QCONV arguments (rand (concl eta)))
        val next = rand (concl result)
      in
        if aconv tm next then result
        else TRANS result (normalize next)
      end
  in
    let val theorem = normalize tm
    in case !aborted of NONE => theorem | SOME e => raise e end
    handle e =>
      (case !aborted of NONE => raise e | SOME original => raise original)
  end


end (* struct *)
