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

open HolKernel Parse Drule Conv Psyntax 
      liteLib Trace Resolve Opening;

    infix 8 |>
    fun WRAP x = STRUCT_WRAP "Travrules" x;
    fun ERR x = STRUCT_ERR "Travrules" x;

type term = Term.term
type thm = Thm.thm;

   (* ---------------------------------------------------------------------
    * preorders
    * ---------------------------------------------------------------------*)

   val equality = (--`$= : 'a ->'a -> bool`--);

  datatype preorder = PREORDER of string * (thm -> thm -> thm) * (term -> thm);
       
   fun find_relation rel  =
       let val relcid = (name_of_const rel)
	   fun f ((h as PREORDER (cid,_,_))::t) = 
	       if relcid = cid then h else f t
	     | f [] = ERR("find_relation","relation not found")
       in f
       end;

   fun ARB_TRANS thm c1 c2 = MATCH_MP thm (CONJ c1 c2);
       
   fun mk_preorder (TRANS_THM,REFL_THM) = 
       PREORDER (name_of_const(rator(rator(snd(dest_forall(concl REFL_THM))))),
		 ARB_TRANS TRANS_THM, 
		 fn x => SPEC x REFL_THM);

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
   val gen_mk_travrules = TRAVRULES;

   fun merge_travrules tl =
     let val ts = map dest tl
     in TRAVRULES {relations=flatten (map #relations ts),
                   congprocs=foldl (op @) [] (map #congprocs ts),
                   weakenprocs=flatten (map #weakenprocs ts)} 
     end;
    

(* ---------------------------------------------------------------------
 * equality_travrules
 * ---------------------------------------------------------------------*)
   
val equality = [PREORDER("=",TRANS,REFL)];
val EQ_tr = gen_mk_travrules 
  {relations=equality,
   congprocs=[Opening.EQ_CONGPROC],
   weakenprocs=[]};

fun mk_travrules congs = TRAVRULES 
  {relations=equality,
   congprocs=map (CONGPROC REFL) congs,
   weakenprocs=[]};

	 
end (* struct *)
