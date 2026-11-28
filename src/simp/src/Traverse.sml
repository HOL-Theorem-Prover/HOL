(* =====================================================================
 * FILE          : traverse.sml
 * DESCRIPTION   : A programmable term traversal engine
 *
 * AUTHOR        : Donald Syme
 *                 Based loosely on original HOL rewriting by
 *                 Larry Paulson et al.
 * ===================================================================== *)

(* =====================================================================
 * The Traversal/Reduction Engine itself lives in TraverseCore, which
 * TraverseExt shares; this structure supplies the ordinary reducers.
 * =====================================================================*)


structure Traverse :> Traverse =
struct

open Abbrev

(* ---------------------------------------------------------------------
 * reducers and contexts
 * ---------------------------------------------------------------------*)

type context = TraverseCore.context

datatype reducer =
  REDUCER of {name : string option,
              initial: context,
              addcontext : context * Thm.thm list -> context,
              apply: TraverseCore.apply_args -> conv
              };
fun dest_reducer (REDUCER x) = x

fun addctxt ths (REDUCER {name,initial,addcontext,apply}) =
    REDUCER{name = name, initial = addcontext(initial,ths), apply = apply,
            addcontext = addcontext}

(* ---------------------------------------------------------------------
 * TRAVERSE
 *
 * ---------------------------------------------------------------------*)

type traverse_data = {limit : int option,
                      rewriters: reducer list,
                      dprocs: reducer list,
                      travrules: Travrules.travrules,
                      relation: term};

fun initial (REDUCER {initial,...}) = initial
fun addcontext (REDUCER {addcontext,...}) = addcontext
fun apply (REDUCER {apply,...}) = apply

fun TRAVERSE ({limit,dprocs,rewriters,travrules,relation} : traverse_data) =
    TraverseCore.TRAVERSE
      {rewriters=rewriters, dprocs=dprocs, limit=limit, travrules=travrules,
       relation=relation, initial=initial, addcontext=addcontext,
       apply=apply, subgoaler=NONE, solvers=[]}

end (* struct *)
