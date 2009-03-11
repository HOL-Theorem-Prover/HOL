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
                                  * (term -> thm);

   fun find_relation rel  = let
     fun f ((h as PREORDER (cid,_,_))::t) = if Opening.samerel rel cid then h
                                            else f t
       | f [] = ERR("find_relation","relation not found")
   in
     f
   end;

   fun ARB_TRANS thm c1 c2 = MATCH_MP thm (CONJ c1 c2);

   fun mk_preorder (TRANS_THM,REFL_THM) =
       PREORDER (rator(rator(snd(dest_forall(concl REFL_THM)))),
		 ARB_TRANS TRANS_THM,
		 fn x => ISPEC x REFL_THM);

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

val equality = [PREORDER(boolSyntax.equality,TRANS,REFL)];
val EQ_tr = gen_mk_travrules
  {relations=equality,
   congprocs=[Opening.EQ_CONGPROC],
   weakenprocs=[]};

fun mk_travrules congs = TRAVRULES
  {relations=equality,
   congprocs=map (CONGPROC (fn t => REFL)) congs,
   weakenprocs=[]};


end (* struct *)
