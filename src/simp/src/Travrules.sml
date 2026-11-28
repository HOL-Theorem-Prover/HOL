(* =====================================================================
 * FILE          : $Id$
 * DESCRIPTION   : A programmable term traversal engine for hol90
 *
 * AUTHOR        : Donald Syme
 *                 Based loosely on original HOL rewriting by
 *                 Larry Paulson et al.
 * ===================================================================== *)


(* =====================================================================
 * Traversal (opening) Rules
 * =====================================================================*)

structure Travrules :> Travrules =
struct

open Abbrev

local
open Feedback Lib Term Thm Drule Psyntax liteLib Opening
in

val samerel = Opening.samerel

fun WRAP x = STRUCT_WRAP "Travrules" x;
fun ERR x = STRUCT_ERR "Travrules" x;


   (* ---------------------------------------------------------------------
    * preorders
    * ---------------------------------------------------------------------*)

  val equality = boolSyntax.equality;

  datatype preorder = PREORDER of term
                                  * (thm -> thm -> thm)
                                  * ({Rinst:term,arg:term} -> thm);

   fun find_relation rel  = let
     fun f ((h as PREORDER (cid,_,_))::t) = if Opening.samerel cid rel then h
                                            else f t
       | f [] = ERR("find_relation","relation not found")
   in
     f
   end;

   fun ARB_TRANS thm c1 c2 = MATCH_MP thm (CONJ c1 c2);

   fun mk_preorder (TRANS_THM,REFL_THM) = let
     fun refl {Rinst,arg} = PART_MATCH rator REFL_THM (mk_comb(Rinst,arg))
   in
     PREORDER (rator(rator(snd(boolSyntax.strip_forall(concl REFL_THM)))),
               ARB_TRANS TRANS_THM,
               refl)
   end

   (* ---------------------------------------------------------------------
    * travrules objects and basic operations on them
    * merge_travrules:
    * The order of congprocs is v. significant - the list in the object
    * gets applied left to right.  Congprocs from
    * the second of two travsets have
    * priority - hence the "foldl" below.
    * ---------------------------------------------------------------------*)

   datatype travrules = TRAVRULES of {
       relations : preorder list,
       congprocs : congproc list,
       weakenprocs : congproc list
    };

   fun dest(TRAVRULES x)  = x;
   val gen_mk_travrules = TRAVRULES

   fun rel_of_preorder (PREORDER(r,_,_)) = r

   fun merge_travrules tl = let
     val ts = map dest tl
     fun sort_unique l = let
       val sorted = Listsort.sort (inv_img_cmp rel_of_preorder Term.compare) l
       fun recurse acc [] = acc
         | recurse acc [h] = h::acc
         | recurse acc (h1::(rest as h2::t)) =
           if samerel (rel_of_preorder h1) (rel_of_preorder h2) then
             recurse acc rest
           else
             recurse (h1::acc) rest
     in
       recurse [] sorted
     end
     (* Appending an ordinary equality-only fragment supplies the same
        preorder twice. Keep the fresh singleton produced by the merge. *)
     fun uniquify (l as [p,q]) =
           if Portable.pointer_eq (p,q) then [q] else sort_unique l
       | uniquify l = sort_unique l
   in
     TRAVRULES {relations=uniquify (flatten (map #relations ts)),
                congprocs=foldl (op @) [] (map #congprocs ts),
                weakenprocs=flatten (map #weakenprocs ts)}
     end;


(* ---------------------------------------------------------------------
 * equality_travrules
 * ---------------------------------------------------------------------*)

val EQ_preorder = let
  fun eqrefl {Rinst,arg} = REFL arg
in
  PREORDER(boolSyntax.equality,TRANS,eqrefl)
end
val EQ_tr = gen_mk_travrules
  {relations=[EQ_preorder],
   congprocs=[Opening.EQ_CONGPROC],
   weakenprocs=[]}

fun gen_cong2proc mk_congproc rels th = let
  open Opening
  val r = rel_of_congrule th
  val PREORDER(_,_,refl) = find_relation r rels
in
  mk_congproc refl th
end
val cong2proc = gen_cong2proc Opening.CONGPROC

fun gen_mk_travrules0 mk_congproc relns congs =
    TRAVRULES {relations=relns,
               congprocs=map (gen_cong2proc mk_congproc relns) congs,
               weakenprocs=[]}
val mk_travrules = gen_mk_travrules0 Opening.CONGPROC
val mk_threaded_travrules = gen_mk_travrules0 Opening.THREADED_CONGPROC

end

end (* struct *)
