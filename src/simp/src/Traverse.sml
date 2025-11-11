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

open HolKernel boolLib Drule BBConv Conv Psyntax Abbrev liteLib
     Trace Travrules Opening;

infix THENQC THENCQC ORELSEBBC IFCQC

val ERR   = mk_HOL_ERR "Traverse" ;

val equality = boolSyntax.equality;

(* ---------------------------------------------------------------------
 * reducers and contexts
 * ---------------------------------------------------------------------*)

type context = exn   (* well known SML hack to allow any kind of data *)

type reducer_info = {
  name : string option,
  initial: context,
  addcontext : context * thm list -> context,
  apply: {solver:term list -> conv,
          conv: term list -> bbconv,
          context: context,
          stack:term list,
          relation : (term * (term -> thm))} -> bbconv
}
datatype reducer = REDUCER of reducer_info
fun dest_reducer (REDUCER ri) = ri

fun addctxt ths (REDUCER {name,initial,addcontext,apply}) =
    REDUCER{name = name, initial = addcontext(initial,ths), apply = apply,
            addcontext = addcontext}


(* ---------------------------------------------------------------------
 * Traversal states
 *    - stores the state of the reducers during the simpl. process
 * ---------------------------------------------------------------------*)

datatype trav_state =
  TSTATE of {relation_info : preorder,
             relation : term,
             contexts1 : context list,
             contexts2 : context list,
             freevars : term list};

fun tstate_refl (TSTATE{relation_info,relation,...}) t =
    let
      val PREORDER(_, _, irefl) = relation_info
    in
      irefl {Rinst = relation, arg = t}
    end


fun initial_context {rewriters:reducer list,
                     dprocs:reducer list,
                     travrules=TRAVRULES tsdata,
                     relation, limit} =
  TSTATE{contexts1=map (#initial o dest_reducer) rewriters,
         contexts2=map (#initial o dest_reducer) dprocs,
         freevars=[],
         relation_info = find_relation relation (#relations tsdata),
         relation = relation};

(* ---------------------------------------------------------------------
 * add_context
 *
 * ---------------------------------------------------------------------*)

fun add_context rewriters dprocs = let
  val rewrite_collectors' = map (#addcontext o dest_reducer) rewriters
  val dproc_collectors' = map (#addcontext o dest_reducer) dprocs
  fun doit (context, thms) = let
    val TSTATE {contexts1,contexts2,freevars,relation_info, relation} = context
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
               freevars=newfreevars,
               relation=relation, relation_info = relation_info}
      end
  end
in
  doit
end


(* ---------------------------------------------------------------------
 * change_relation
 *
 * ---------------------------------------------------------------------*)

fun change_relation (TRAVRULES{relations,...}) (context, rel) = let
  val TSTATE {contexts1,contexts2,freevars, relation_info, relation} = context
  val PREORDER(oldrelname,_,_) = relation_info
in
  if samerel oldrelname rel then
    TSTATE{contexts1=contexts1, contexts2=contexts2, freevars=freevars,
           relation_info=relation_info, relation = rel}
  else
    TSTATE{contexts1=contexts1,
           contexts2=contexts2,
           freevars=freevars,
           relation_info=find_relation rel relations, relation = rel}
end

(* ----------------------------------------------------------------------
    Quick, General conversion routines.  These work for any preorder, not
    just equality.  "Conversions" are assumed to embody their transitivity
    reasoning; they are passed a theorem of form |- t0 ≈ t, work on the
    term t and return a "new" theorem of form |- t0 ≈ t'
   ---------------------------------------------------------------------- *)

fun GEN_THENQC (conv1,conv2) th =
  (* th says |- t0 ≈ t *)
  let
    val th1 = conv1 th (* |- t0 ≈ t1 *)
  in
    conv2 th1 (* |-> t0 ≈ t2 *)
    handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 th (* either another exn, or |- t0 ≈ t2' *)

fun GEN_THENCQC (conv1,conv2) th0 (* |- t ≈ t0 *) =
  let
    val th1 = conv1 th0 (* |- t ≈ t1 *)
  in
    conv2 th1 (* |- t ≈ t2 *)
    handle HOL_ERR _ => th1
  end

(* perform continuation with argument indicating whether a change occurred *)
fun GEN_IFCQC (conv1,conv2) th (* |- t0 ≈ t *) =
  let
    val th1 = conv1 th (* |- t0 ≈ t1 *)
  in
    conv2 true th1 handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 false th


fun GEN_REPEATQC conv th = GEN_THENCQC (conv, GEN_REPEATQC conv) th

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

fun FIRSTCQC_CONV [] th = failwith "no conversion worked"
  | FIRSTCQC_CONV (c::cs) th = let
    in
      c th
      handle UNCHANGED => failwith "unchanged" (* Need to raise a HOL_ERR *)
           | HOL_ERR _ => FIRSTCQC_CONV cs th
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

(* ---------------------------------------------------------------------
 * TRAVERSE_IN_CONTEXT
 *
 * NOTES
 *   - Rewriters/Dprocs should always fail if unchanged (but not with
 *     UNCHANGED).
 *   - Congruence rule procs should only fail if they do not match.
 *     They can fail with UNCHANGED if nothing changes.
 *   - The depther should only fail with UNCHANGED.
 * ---------------------------------------------------------------------*)

fun TRAVERSE_IN_CONTEXT limit rewriters dprocs travrules stack ctxt (tm:term) = let
  open Uref
  val TRAVRULES {relations,congprocs,weakenprocs,...} = travrules
  val add_context' = add_context rewriters dprocs
  val change_relation' = change_relation travrules
  val lim_r = Uref.new limit
  fun check r = case !r of NONE => ()
    | SOME n => if n <= 0 then
                               (trace(2,TEXT "Limit exhausted");
                                raise ERR "TRAVERSE_IN_CONTEXT"
                                          "Limit exhausted")
                             else ()
  fun dec r = case !r of NONE => ()
    | SOME n => r := SOME (n - 1)

  fun trav stack context  = let
    val TSTATE {contexts1,contexts2, freevars,
                relation_info = relation, relation = relname} = context
    fun ctxt_solver stack tm = let
      val old = !lim_r
    in
      EQT_ELIM (
        trav stack
             (change_relation' (context,equality))
             (REFL tm)
      ) handle e as HOL_ERR _ => (lim_r := old ; raise e)
    end
    fun ctxt_conv stack th = let
      val old = !lim_r
    in
      trav stack (change_relation' (context,equality)) th
      handle e as HOL_ERR _ => (lim_r := old ; raise e)
    end
    fun mkrefl t = let
      val PREORDER(_, _, irefl) = relation
    in
      irefl {Rinst = relname, arg = t}
    end
    fun apply_reducer (REDUCER rdata) context th =
        (#apply rdata) {solver=ctxt_solver,
                        conv=ctxt_conv,
                        context=context,
                        stack=stack, relation=(relname, mkrefl)}
                       th before
        dec lim_r
    fun high_priority th =
        (check lim_r;
         FIRST_BBCONV (mapfilter2 apply_reducer rewriters contexts1) th)
    fun low_priority th =
        (check lim_r ;
         FIRST_BBCONV (mapfilter2 apply_reducer dprocs contexts2) th)
    fun depther (thms,relation) tm =
        let
          val tstate = change_relation' (add_context' (context,thms), relation)
        in
          trav stack tstate (tstate_refl tstate tm)
        end
    val congproc_args =
        {relation=relname,
         solver=(fn tm => ctxt_solver stack tm), (* do not eta-convert! *)
         depther=depther,
         freevars=freevars}
    fun apply_congproc congproc = congproc congproc_args
    val descend = FIRSTCQC_CONV (mapfilter apply_congproc congprocs)
    val weaken = FIRST_BBCONV (mapfilter apply_congproc weakenprocs)
    val op IFCQC = GEN_IFCQC
    val op THENCQC = GEN_THENCQC
    val op THENQC = GEN_THENQC
    val REPEATQC = GEN_REPEATQC
    fun rcon th = rator (concl th)

    fun loop thm = let
      val conv =
          REPEATQC high_priority THENQC
          (descend IFCQC
              (fn change =>
                ((if change then high_priority else NO_BBCONV) ORELSEBBC
                 low_priority ORELSEBBC weaken) THENCQC loop))
             (* THENCQC above causes the loop to happen only if
                the stuff before it hasn't raised an exception *)
    in
      (trace(4,REDUCE ("Reducing",rcon thm)); conv thm)
    end;
  in
    loop
  end
in
  trav stack ctxt (REFL tm)
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

fun TRAVERSE (data as {limit,dprocs,rewriters,travrules,relation}) thms =
   let val context' = add_context rewriters dprocs (initial_context data,thms)
   in TRAVERSE_IN_CONTEXT limit rewriters dprocs travrules [] context'
   end;

end (* struct *)
