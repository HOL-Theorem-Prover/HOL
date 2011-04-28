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

open HolKernel Drule Psyntax liteLib Trace Opening;

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
     fun uniquify l = let
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

fun cong2proc rels th = let
  open Opening
  val r = rel_of_congrule th
  val PREORDER(_,_,refl) = find_relation r rels
in
  CONGPROC refl th
end

fun mk_travrules relns congs =
    TRAVRULES {relations=relns,
               congprocs=map (cong2proc relns) congs,
               weakenprocs=[]}


end (* struct *)
