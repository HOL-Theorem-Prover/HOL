(* ===================================================================== *)
(* FILE          : resolve.sml                                           *)
(* DESCRIPTION   : HOL-style resolution (MP + pattern matching).         *)
(*                 Translated from hol88 version 1.12.                   *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* UPDATED       : (to 2.01); change to RES_CANON                        *)
(* ===================================================================== *)

structure Resolve :> Resolve =
struct
open HolKernel Parse;
open Tactical Drule;
  infix THEN THENL ORELSE |->;
  
type tactic = Abbrev.tactic;


fun RESOLVE_ERR function message =
    Exception.HOL_ERR{origin_structure = "Resolve",
		      origin_function = function,
		      message = message}

(* ---------------------------------------------------------------------*)
(* Search among a list of implications to perform Modus Ponens		*)
(* Used nowhere --- deleted until found useful [TFM 90.04.24]		*)
(* let MULTI_MP impl ante =						*)
(*     tryfind (\imp. MATCH_MP imp ante) impl  ?  failwith `MULTI_MP`;  *)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Forwards chaining by Modus Ponens					*)
(* Used nowhere --- deleted until found useful [TFM 90.04.24]		*)
(* let MP_CHAIN = REDEPTH_CHAIN o MULTI_MP;				*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Accept a theorem that, properly instantiated, satisfies the goal     *)
(* ---------------------------------------------------------------------*)
fun MATCH_ACCEPT_TAC thm : tactic =
  let val fmatch = Conv.PART_MATCH Lib.I thm 
      fun atac (asl,w) = ([], Lib.K (fmatch w))
  in
     REPEAT Tactic.GEN_TAC THEN atac
  end
  handle HOL_ERR _ => raise RESOLVE_ERR "MATCH_ACCEPT_TAC" "";

(* ---------------------------------------------------------------------*)
(* Basic unit for resolution tactics					*)
(* DELETED: TFM 88.03.31 (not used anywhere)				*)
(*									*)
(* let MATCH_MP_TAC impth = STRIP_ASSUME_TAC o (MATCH_MP impth);	*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Resolve implicative assumptions with an antecedent			*)
(* ---------------------------------------------------------------------*)
fun ANTE_RES_THEN ttac ante : tactic =
  ASSUM_LIST
     (EVERY o (mapfilter (fn imp => ttac (Conv.MATCH_MP imp ante))));

(* ---------------------------------------------------------------------*)
(* Old versions of RESOLVE_THEN etc.			[TFM 90.04.24]  *)
(* 									*)
(* letrec RESOLVE_THEN antel ttac impth : tactic =			*)
(*     let answers = mapfilter (MATCH_MP impth) antel in		*)
(*     EVERY (mapfilter ttac answers)					*)
(*     THEN								*)
(*     (EVERY (mapfilter (RESOLVE_THEN antel ttac) answers));		*)
(* 									*)
(* let OLD_IMP_RES_THEN ttac impth =					*)
(*  ASSUM_LIST								*)
(*     (\asl. EVERY (mapfilter (RESOLVE_THEN asl ttac) 			*)
(*		  	      (IMP_CANON impth)));			*)
(* 									*)
(* let OLD_RES_THEN ttac = 						*)
(*     ASSUM_LIST (EVERY o (mapfilter (OLD_IMP_RES_THEN ttac)));	*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* A trick tactic for solving existential/disjunctive goals		*)
(* Too tricky, and depends on obsolete version of IMP_RES_THEN		*)
(* Deleted: TFM 90.04.24						*)
(* let SELF_RES_TAC (asl,w) = 						*)
(*    OLD_IMP_RES_THEN ACCEPT_TAC					*)
(*       (DISCH w (itlist ADD_ASSUM asl (ASSUME w))) (asl,w);		*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Resolution tactics from LCF - uses IMP_CANON and GSPEC 		*)
(* 									*)
(* Deleted: TFM 90.04.24						*)
(*									*)
(* let OLD_IMP_RES_TAC = OLD_IMP_RES_THEN STRIP_ASSUME_TAC;		*)
(* let OLD_RES_TAC = OLD_RES_THEN STRIP_ASSUME_TAC;			*)
(* ---------------------------------------------------------------------*)

(* =====================================================================*)
(* Resolution tactics for HOL - uses RES_CANON and SPEC_ALL 		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Put a theorem 							*)
(*									*)
(*	 |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 			*)
(*									*)
(* into canonical form for resolution by splitting conjunctions apart   *)
(* (like IMP_CANON but without the stripping out of quantifiers and only*)
(* outermost negations being converted to implications).		*)
(*									*)
(*   ~t            --->          t ==> F        (at outermost level)	*)
(*   t1 /\ t2	  --->		t1,   t2				*)
(*   (t1/\t2)==>t  --->		t1==> (t2==>t)				*)
(*   (t1\/t2)==>t  --->		t1==>t, t2==>t				*)
(*									*)
(*									*)
(* Modification provided by David Shepherd of Inmos to make resolution  *)
(* work with equalities as well as implications. HOL88.1.08,23 jun 1989.*)
(*									*)
(*   t1 = t2      --->          t1=t2, t1==>t2, t2==>t1			*)
(*									*)
(* Modification provided by T Melham to deal with the scope of 		*)
(* universal quantifiers. [TFM 90.04.24]				*)
(*									*)
(*   !x. t1 ==> t2  --->  t1 ==> !x.t2   (x not free in t1)		*)
(*									*)
(* The old code is given below:						*)
(* 									*)
(*    letrec RES_CANON_FUN th =						*)
(*     let w = concl th in						*)
(*     if is_conj w 							*)
(*     then RES_CANON_FUN(CONJUNCT1 th)@RES_CANON_FUN(CONJUNCT2 th)	*)
(*     else if is_imp w & not(is_neg w) then				*)
(* 	let ante,conc = dest_imp w in					*)
(* 	if is_conj ante then						*)
(* 	    let a,b = dest_conj ante in					*)
(* 	    RES_CANON_FUN 						*)
(* 	    (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))	*)
(* 	else if is_disj ante then					*)
(* 	    let a,b = dest_disj ante in					*)
(* 	    RES_CANON_FUN (DISCH a (MP th (DISJ1 (ASSUME a) b))) @	*)
(* 	    RES_CANON_FUN (DISCH b (MP th (DISJ2 a (ASSUME b))))	*)
(* 	else								*)
(* 	map (DISCH ante) (RES_CANON_FUN (UNDISCH th))			*)
(*     else [th];							*)
(* 									*)
(* This version deleted for HOL 1.12 (see below)	[TFM 91.01.17]  *)
(*									*)
(* let RES_CANON = 							*)
(*     letrec FN th = 							*)
(*       let w = concl th in						*)
(*       if (is_conj w) then FN(CONJUNCT1 th) @ FN(CONJUNCT2 th) else	*)
(*       if ((is_imp w) & not(is_neg w)) then				*)
(*       let ante,conc = dest_imp w in					*)
(*       if (is_conj ante) then						*)
(*          let a,b = dest_conj ante in					*)
(* 	    let ath = ASSUME a and bth = ASSUME b			*)
(*          in FN (DISCH a (DISCH b (MP th (CONJ ath bth)))) else       *)
(*       if is_disj ante then                                           *)
(*         let a,b = dest_disj ante in					*)
(*         let ath = ASSUME a and bth = ASSUME b 			*)
(* 	   in FN (DISCH a (MP th (DISJ1 ath b))) @			*)
(*            FN (DISCH b (MP th (DISJ2 a bth)))                        *)
(*       else map (GEN_ALL o (DISCH ante)) (FN (UNDISCH th))    	*)
(*       else if is_eq w then						*)
(*        let l,r = dest_eq w in					*)
(*            if (type_of l = ":bool")                                  *)
(*            then let (th1,th2) = EQ_IMP_RULE th                       *)
(*                 in (GEN_ALL th) . ((FN  th1) @ (FN  th2)) 		*)
(*            else [GEN_ALL th]                                         *)
(*        else [GEN_ALL th] in                                          *)
(*     \th. (let vars,w = strip_forall(concl th) in			*)
(*           let th1 = if (is_neg w)	 				*)
(* 	  		then NOT_ELIM(SPEC_ALL th) 			*)
(* 			else (SPEC_ALL th) in				*)
(*               map GEN_ALL (FN th1) ? failwith `RES_CANON`);		*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* New RES_CANON for version 1.12.			 [TFM 90.12.07] *)
(* 									*)
(* The complete list of transformations is now:				*)
(*									*)
(*   ~t              --->       t ==> F        (at outermost level)	*)
(*   t1 /\ t2	     --->	t1, t2	       (at outermost level)	*)
(*   (t1/\t2)==>t    --->	t1==>(t2==>t), t2==>(t1==>t)		*)
(*   (t1\/t2)==>t    --->	t1==>t, t2==>t				*)
(*   t1 = t2         --->       t1==>t2, t2==>t1			*)
(*   !x. t1 ==> t2   --->       t1 ==> !x.t2   (x not free in t1)	*)
(*   (?x.t1) ==> t2  --->	!x'. t1[x'/x] ==> t2			*)
(*									*)
(* The function now fails if no implications can be derived from the 	*)
(* input theorem.							*)
(* ---------------------------------------------------------------------*)


local fun not_elim th = 
       if is_neg(concl th) then (true, NOT_ELIM th) else (false,th)
fun canon (fl,th) = 
   let val w = concl th 
   in
   if (is_conj w) then 
     let val (th1,th2) = CONJ_PAIR th 
     in 
        (canon(fl,th1) @ canon(fl,th2)) 
     end else 
   if (is_imp w andalso not(is_neg w)) then 
     let val {ant,...} = Dsyntax.dest_imp w 
     in
        if (is_conj ant) 
        then let val {conj1,conj2} = dest_conj ant 
                 val cth = MP th (CONJ (ASSUME conj1) (ASSUME conj2)) 
                 val th1 = DISCH conj2 cth 
                 and th2 = DISCH conj1 cth 
             in
                canon(true,DISCH conj1 th1) @ canon(true,DISCH conj2 th2)
             end else 
        if (is_disj ant) 
        then let val {disj1,disj2} = dest_disj ant 
                 val ath = DISJ1 (ASSUME disj1) disj2 
                 and bth = DISJ2 disj1 (ASSUME disj2) 
                 val th1 = DISCH disj1 (MP th ath)
                 and th2 = DISCH disj2 (MP th bth) 
             in
                 canon(true,th1) @ canon(true,th2)
             end else 
        if (is_exists ant) 
        then let val {Bvar,Body} = dest_exists ant 
                 val newv = variant(thm_free_vars th) Bvar
                 val newa = subst [Bvar |-> newv] Body 
                 val th1  = MP th (EXISTS (ant,newv) (ASSUME newa))
             in
               canon(true,DISCH newa th1)
             end
        else map (GEN_ALL o (DISCH ant)) (canon (true,UNDISCH th))
     end else 
   if (is_eq w andalso (type_of (rand w) = Type.bool)) then 
     let val (th1,th2) = EQ_IMP_RULE th 
     in
        (if fl then [GEN_ALL th] else []) 
        @ canon(true,th1) @ canon(true,th2)
     end else 
   if is_forall w then 
     let val (vs,_) = strip_forall w 
         val fvs = mk_set (free_varsl(hyp th) @ free_vars (concl th))
         val nvs = itlist (fn v => fn nv => variant (nv @ fvs) v::nv) vs []
     in 
        canon (fl, SPECL nvs th) 
     end else 
   if fl then [GEN_ALL th] else [] 
   end
in
fun RES_CANON th =
   let val conjlist = CONJUNCTS (SPEC_ALL th)
       fun operate th accum = 
            let val thl = map GEN_ALL (canon (not_elim (SPEC_ALL th)))
            in 
             accum @  thl
            end
       val imps = Lib.rev_itlist operate conjlist []
   in
      Lib.assert ((op not) o null) imps
   end
   handle HOL_ERR _ => raise RESOLVE_ERR "RES_CANON"
                         "No implication is derivable from input thm"
end;


(* --------------------------------------------------------------------- *)
(* Definitions of the primitive:					*)
(*									*)
(* IMP_RES_THEN: Resolve all assumptions against an implication.	*)
(*									*)
(* The definition uses two auxiliary (local)  functions:		*)
(*									*)
(*     MATCH_MP     : like the built-in version, but doesn't use GSPEC.	*)
(*     RESOLVE_THEN : repeatedly resolve an implication			*)
(* 									*)
(* This version deleted for HOL version 1.12   		 [TFM 91.01.17]	*)
(*									*)
(* begin_section IMP_RES_THEN;						*)
(*									*)
(* let MATCH_MP impth =							*)
(*     let sth = SPEC_ALL impth in					*)
(*     let pat = fst(dest_imp(concl sth)) in				*)
(*     let matchfn = match pat in					*)
(*        (\th. MP (INST_TY_TERM (matchfn (concl th)) sth) th);		*)
(* 									*)
(* letrec RESOLVE_THEN antel ttac impth : tactic =			*)
(*        let answers = mapfilter (MATCH_MP impth) antel in		*)
(*            EVERY (mapfilter ttac answers) THEN			*)
(*           (EVERY (mapfilter (RESOLVE_THEN antel ttac) answers));	*)
(* 									*)
(* let IMP_RES_THEN ttac impth =					*)
(*     ASSUM_LIST (\asl. 						*)
(*      EVERY (mapfilter (RESOLVE_THEN asl ttac) (RES_CANON impth))) ? 	*)
(*     failwith `IMP_RES_THEN`;						*)
(*									*)
(* IMP_RES_THEN;							*)
(* 									*)
(* end_section IMP_RES_THEN;						*)
(* 									*)
(* let IMP_RES_THEN = it;						*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Definition of the primitive:						*)
(*									*)
(* IMP_RES_THEN: Resolve all assumptions against an implication.	*)
(*									*)
(* The definition uses an auxiliary (local) function, MATCH_MP, which is*)
(* just like the built-in version, but doesn't use GSPEC.		*)
(* 									*)
(* New implementation for version 1.12: fails if no MP-consequences can *)
(* be drawn, and does only one-step resolution.		[TFM 90.12.07]  *)
(* ---------------------------------------------------------------------*)

fun MATCH_MP impth =
   let val sth = SPEC_ALL impth 
       val matchfn = Term.match_term (#ant(Dsyntax.dest_imp(concl sth))) 
   in
   fn th => MP (Conv.INST_TY_TERM (matchfn (concl th)) sth) th
   end;

(* ---------------------------------------------------------------------*)
(* check ex l : Fail with ex if l is empty, otherwise return l.		*)
(* ---------------------------------------------------------------------*)

fun check ex [] = raise ex
  | check ex l = l;

(* ---------------------------------------------------------------------*)
(* IMP_RES_THEN  : Resolve an implication against the assumptions.	*)
(* ---------------------------------------------------------------------*)

fun IMP_RES_THEN ttac impth =
 let val ths = RES_CANON impth 
      handle HOL_ERR _ => raise RESOLVE_ERR "IMP_RES_THEN" "No implication"
 in
  ASSUM_LIST 
   (fn asl => 
     let val l = itlist (fn th => append (mapfilter(MATCH_MP th) asl)) ths [] 
         val res  = check (RESOLVE_ERR "IMP_RES_THEN" "No resolvents") l 
         val tacs = check (RESOLVE_ERR "IMP_RES_THEN" "No tactics")
                          (Lib.mapfilter ttac res) 
     in
        Tactical.EVERY tacs
     end)
 end;

(* ---------------------------------------------------------------------*)
(* RES_THEN    : Resolve all implicative assumptions against the rest.	*)
(* ---------------------------------------------------------------------*)
fun RES_THEN ttac (asl,g) =
 let open Conv
     val aas  = map ASSUME asl 
     val ths  = itlist append (mapfilter RES_CANON aas) [] 
     val imps = check (RESOLVE_ERR "RES_THEN" "No implication") ths 
     val l    = itlist (fn th => append (mapfilter (MATCH_MP th) aas)) imps [] 
     val res  = check (RESOLVE_ERR "RES_THEN" "No resolvents") l 
     val tacs = check (RESOLVE_ERR "RES_THEN" "No tactics")
                         (Lib.mapfilter ttac res) 
 in
   Tactical.EVERY tacs (asl,g)
 end;

(* ---------------------------------------------------------------------*)
(* Definition of the standard resolution tactics IMP_RES_TAC and RES_TAC*)
(*									*)
(* The function SA is like STRIP_ASSUME_TAC, except that it does not    *)
(* strip off existential quantifiers. And ST is like STRIP_THM_THEN, 	*)
(* except that it also does not strip existential quantifiers.		*)
(*									*)
(* Old version: deleted for HOL version 1.12 		 [TFM 91.01.17]	*)
(*									*)
(* let (IMP_RES_TAC,RES_TAC) = 						*)
(*    let ST = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN] in		*)
(*    let SA = (REPEAT_TCL ST) CHECK_ASSUME_TAC in			*)
(*        (IMP_RES_THEN SA, RES_THEN SA);				*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* New versions of IMP_RES_TAC and RES_TAC: repeatedly resolve, and then*)
(* add FULLY stripped, final, result(s) to the assumption list.		*)
(* ---------------------------------------------------------------------*)

fun IMP_RES_TAC th g =
   IMP_RES_THEN (Thm_cont.REPEAT_GTCL IMP_RES_THEN Tactic.STRIP_ASSUME_TAC) 
                th g 
   handle HOL_ERR _ => ALL_TAC g;

fun RES_TAC g =
    RES_THEN (Thm_cont.REPEAT_GTCL IMP_RES_THEN Tactic.STRIP_ASSUME_TAC) g 
    handle HOL_ERR _ => ALL_TAC g;

(* ---------------------------------------------------------------------*)
(* Used to be for compatibility with the old system. 			*)
(* Deleted: TFM 90.04.24						*)
(* let HOL_IMP_RES_THEN = IMP_RES_THEN					*)
(* and HOL_RES_THEN     = RES_THEN;					*)
(* ---------------------------------------------------------------------*)


(* ---------------------------------------------------------------------*)
(* MATCH_MP_TAC: Takes a theorem of the form 				*)
(*									*)
(*       |- !x1..xn. A ==> !y1 ... ym. B 				*)
(* 									*)
(* and matches B to the goal, reducing it to the subgoal consisting of 	*)
(* some existentially-quantified instance of A:				*)
(*									*)
(*      !v1...vi. B							*)
(* ======================= MATCH_MP_TAC |- !x1...1n. A ==> !y1...ym. B  *)
(*      ?z1...zp. A							*)
(* 									*)
(* where {z1,...,zn} is the subset of {x1,...,xn} whose elements do not *)
(* appear free in B.							*)
(*									*)
(* Added: TFM 88.03.31							*)
(* Revised: TFM 91.04.20						*)
(*									*)
(* Old version:								*)
(*									*)
(* let MATCH_MP_TAC thm:tactic (gl,g) =					*)
(*     let imp = ((PART_MATCH (snd o dest_imp) thm) g) ? 		*)
(* 	       failwith `MATCH_MP_TAC` in				*)
(*     ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl));	*)
(* ---------------------------------------------------------------------*)
local fun efn v (tm,th) =
        let val ntm = Dsyntax.mk_exists{Bvar=v, Body=tm} 
        in (ntm,CHOOSE (v, ASSUME ntm) th)
        end
in
fun MATCH_MP_TAC thm :tactic =
 let val (gvs,imp) = strip_forall (concl thm) 
     val {ant,conseq} = dest_imp imp handle HOL_ERR _ 
           => raise RESOLVE_ERR"MATCH_MP_TAC" "Not an implication"
     val (cvs,con) = strip_forall conseq
     val th1       = SPECL cvs (UNDISCH (SPECL gvs thm))
     val (vs,evs)  = partition (C Term.free_in con) gvs 
     val th2       = uncurry DISCH (itlist efn evs (ant,th1))
 in
 fn (A,g) => 
  let val (vs,gl) = strip_forall g
      val ins = match_term con gl 
      handle HOL_ERR _ => raise RESOLVE_ERR "MATCH_MP_TAC" "No match"
      val ith = Conv.INST_TY_TERM ins th2 
      val gth = GENL vs (UNDISCH ith) 
      handle HOL_ERR _ => raise RESOLVE_ERR"MATCH_MP_TAC" "Generalized var(s)."
      val ant = #ant(dest_imp(concl ith)) 
  in
     ([(A,ant)], fn thl => MP (DISCH ant gth) (hd thl))
  end
 end
end;


end; (* Resolve *)
