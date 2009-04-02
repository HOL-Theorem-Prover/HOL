(* ===================================================================== *)
(* FILE          : Thm_cont.sml                                          *)
(* DESCRIPTION   : Larry Paulson's theorem continuations for HOL.        *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* "Theorem continuations"                                               *)
(*                                                                       *)
(* Many inference rules, particularly those involving disjunction and    *)
(* existential quantifiers, produce intermediate results that are needed *)
(* only briefly.  One approach is to treat the assumption list like a    *)
(* stack, pushing and popping theorems from it.  However, it is          *)
(* traditional to regard the assumptions as unordered;  also, stack      *)
(* operations are crude.                                                 *)
(*                                                                       *)
(* Instead, we adopt a continuation approach:  a continuation is a       *)
(* function that maps theorems to tactics.  It can put the theorem on    *)
(* the assumption list, produce a case split, throw it away, etc.  The	 *)
(* text of a large theorem continuation should be a readable description *)
(* of the flow of inference.						 *)
(*                                                                       *)
(* AUTHORS       : (c) Larry Paulson and others,                         *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Thm_cont :> Thm_cont =
struct

open Feedback HolKernel Drule boolSyntax Abbrev;

val ERR = mk_HOL_ERR "Thm_cont";

fun (ttcl1:thm_tactical) THEN_TCL (ttcl2:thm_tactical) =  fn ttac =>
     ttcl1 (ttcl2 ttac);

fun (ttcl1:thm_tactical) ORELSE_TCL (ttcl2:thm_tactical) = fn ttac => fn th =>
    (ttcl1 ttac th)  handle HOL_ERR _ => (ttcl2 ttac th);

fun REPEAT_TCL ttcl ttac th =
    ((ttcl  THEN_TCL  (REPEAT_TCL ttcl))  ORELSE_TCL  I) ttac th;

(* --------------------------------------------------------------------- *)
(* New version of REPEAT for ttcl's.  Designed for use with IMP_RES_THEN.*)
(* TFM 91.01.20.                                                         *)
(* --------------------------------------------------------------------- *)

fun REPEAT_GTCL (ttcl: thm_tactical) ttac th (A,g) =
    ttcl (REPEAT_GTCL ttcl ttac) th (A,g)
    handle HOL_ERR _ => ttac th (A,g);

val ALL_THEN :thm_tactical = I;
val NO_THEN:thm_tactical = fn ttac => fn th => raise ERR "NO_THEN" "";

(*---------------------------------------------------------------------------
 * Uses every theorem tactical.
 *
 *   EVERY_TCL [ttcl1;...;ttcln] =  ttcl1  THEN_TCL  ...  THEN_TCL  ttcln
 *---------------------------------------------------------------------------*)

fun EVERY_TCL ttcll = itlist (curry (op THEN_TCL)) ttcll ALL_THEN;


(*---------------------------------------------------------------------------
 * Uses first successful theorem tactical.
 *
 *  FIRST_TCL [ttcl1;...;ttcln] =  ttcl1  ORELSE_TCL  ...  ORELSE_TCL  ttcln
 *---------------------------------------------------------------------------*)

fun FIRST_TCL ttcll = itlist (curry (op ORELSE_TCL)) ttcll NO_THEN;


(*---------------------------------------------------------------------------
 * Conjunction elimination
 *
 *	C
 *   ==============       |- A1 /\ A2
 *	C
 *      ===== ttac1 |-A1
 *       ...
 *      ===== ttac2 |-A2
 *       ...
 *---------------------------------------------------------------------------*)

fun CONJUNCTS_THEN2 ttac1 ttac2 = fn cth =>
  let val (th1,th2) = CONJ_PAIR cth
  in
    Tactical.THEN (ttac1 th1, ttac2 th2)
  end
  handle HOL_ERR _ => raise ERR "CONJUNCTS_THEN2" "";


val CONJUNCTS_THEN :thm_tactical = fn ttac => CONJUNCTS_THEN2 ttac ttac;;

(*---------------------------------------------------------------------------
 * Disjunction elimination
 *
 *	         C
 *   =============================       |- A1 \/ A2
 *      C                     C
 *    ===== ttac1 A1|-A1    ===== ttac2 A2|-A2
 *     ...		   ...
 *---------------------------------------------------------------------------*)

(* -------------------------------------------------------------------------*)
(* REVISED 22 Oct 1992 by TFM. Bugfix.					    *)
(*									    *)
(* The problem was, for example:					    *)
(*									    *)
(*  th = |- ?n. ((?n. n = SUC 0) \/ F) /\ (n = 0)			    *)
(*  set_goal ([], "F");;						    *)
(*  expandf (STRIP_ASSUME_TAC th);;				 	    *)
(*  OK..								    *)
(*  "F"									    *)
(*     [ "n = SUC 0" ] (n.b. should be n')				    *)
(*     [ "n = 0" ]						            *)
(* 								            *)
(* let DISJ_CASES_THEN2 ttac1 ttac2 disth :tactic  =			    *)
(*     let a1,a2 = dest_disj (concl disth) ? failwith `DISJ_CASES_THEN2` in *)
(*     \(asl,w).							    *)
(*      let gl1,prf1 = ttac1 (ASSUME a1) (asl,w)			    *)
(*      and gl2,prf2 = ttac2 (ASSUME a2) (asl,w)			    *)
(*      in							            *)
(*      gl1 @ gl2,							    *)
(*      \thl. let thl1,thl2 = chop_list (length gl1) thl in		    *)
(*            DISJ_CASES disth (prf1 thl1) (prf2 thl2);;		    *)
(* -------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
  foo needs to return a theorem with M as conclusion, and M as one
   of the assumptions, and all of the assumptions of th as well:

     foo th M = mk_thm(M::Thm.hyp th, M)
 ---------------------------------------------------------------------------*)

fun foo th M = MP (DISCH (concl th) (ASSUME M)) th


fun DISJ_CASES_THEN2 ttac1 ttac2 = fn disth =>
   let val (disj1,disj2) = dest_disj (Thm.concl disth)
   in fn (g as (asl,w))
     =>
    let val (gl1,prf1) = ttac1 (foo disth disj1) g
(*               ttac1 (itlist ADD_ASSUM (Thm.hyp disth) (ASSUME disj1)) g *)
          and (gl2,prf2) = ttac2 (foo disth disj2) g
(*              ttac2 (itlist ADD_ASSUM (Thm.hyp disth) (ASSUME disj2)) g *)
      in
      ((gl1 @ gl2),
       (fn thl =>
         let val (thl1,thl2) = split_after (length gl1) thl
         in DISJ_CASES disth (prf1 thl1) (prf2 thl2) end))
      end
   end
   handle HOL_ERR _ => raise ERR "DISJ_CASES_THEN2" "";


(*---------------------------------------------------------------------------*
 * Single-, multi-tactic versions                                            *
 *---------------------------------------------------------------------------*)

val DISJ_CASES_THEN  : thm_tactical = fn ttac => DISJ_CASES_THEN2 ttac ttac;
val DISJ_CASES_THENL : thm_tactic list -> thm_tactic
     = end_itlist DISJ_CASES_THEN2 ;


(*---------------------------------------------------------------------------
 * Implication introduction
 *
 *	A ==> B
 *    ==============
 *	  B
 *    ==============  ttac |-A
 *	. . .
 *
 * DISCH changed to NEG_DISCH for HOL
 *
 * Deleted: TFM 88.03.31
 *
 * let DISCH_THEN ttac :tactic (asl,w) =
 *     let ante,conc = dest_imp w ? failwith `DISCH_THEN` in
 *     let gl,prf = ttac (ASSUME ante) (asl,conc) in
 *     gl, (NEG_DISCH ante) o prf;;
 * Added: TFM 88.03.31  (bug fix)
 *---------------------------------------------------------------------------*)


fun DISCH_THEN ttac (asl,w) =
   let val (ant,conseq) = dest_imp w
       val (gl,prf) = ttac (ASSUME ant) (asl,conseq)
   in
   (gl, (if is_neg w then NEG_DISCH ant else DISCH ant) o prf)
   end
   handle HOL_ERR _ => raise ERR "DISCH_THEN" "";

(*---------------------------------------------------------------------------*
 * DISCH_THEN's "dual"                                                       *
 *                                                                           *
 * ported from John Harrison's HOL Light                                     *
 *        -- Michael Norrish 30 June 1999                                    *
 *---------------------------------------------------------------------------*)

fun UNDISCH_THEN tm ttac (asl, w) =
 let val (_, asl') = with_exn (Lib.pluck (aconv tm)) asl
                     (ERR "UNDISCH_THEN" "Term given not an assumption")
 in ttac (ASSUME tm) (asl', w)
 end;


(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *	    B
 *    ==================   |- ?x. A(x)
 *            B
 *    ==================    ttac A(y)
 *	   ...
 * explicit version for tactic programming
 *---------------------------------------------------------------------------*)

fun X_CHOOSE_THEN y (ttac:thm_tactic) : thm_tactic = fn xth =>
   let val (Bvar,Body) = dest_exists (Thm.concl xth)
   in fn (asl,w) =>
      let val th = foo xth (subst[Bvar |-> y] Body)
(* itlist ADD_ASSUM (hyp xth)
                          (ASSUME (subst[Bvar |-> y] Body)) *)
        val (gl,prf) = ttac th (asl,w)
    in
        (gl, (CHOOSE (y,xth)) o prf)
    end
   end
   handle HOL_ERR _ => raise ERR "X_CHOOSE_THEN" "";


(*---------------------------------------------------------------------------
 * Chooses a variant for the user.
 *---------------------------------------------------------------------------*)

val CHOOSE_THEN :thm_tactical = fn ttac => fn xth =>
   let val (hyp,conc) = dest_thm xth
       val (Bvar,_) = dest_exists conc
   in fn (asl,w) =>
     let val y = gen_variant Parse.is_constname
                             ""
                             (free_varsl ((conc::hyp)@(w::asl)))
                             Bvar
     in X_CHOOSE_THEN y ttac xth (asl,w)
     end
   end handle HOL_ERR _ => raise ERR "CHOOSE_THEN" "";


(*----------  Cases tactics   -------------*)

(*---------------------------------------------------------------------------
 * For a generalized disjunction |-(?xl1.B1(xl1)) \/...\/ (?xln.Bn(xln))
 * where the xl1...xln are vectors of zero or more variables, and the
 * variables in each of yl1...yln have the same types as the
 * corresponding xli do
 *
 *                       A
 *  =============================================
 *     A                                     A
 *  ======= ttac1 |-B1(yl1)     ...       ======= ttacn |-Bn(yln)
 *    ...                                   ...
 *
 *---------------------------------------------------------------------------*)

fun X_CASES_THENL varsl (ttacl:thm_tactic list) =
    DISJ_CASES_THENL
       (map (fn (vars,ttac) => EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
            (varsl zip ttacl));


fun X_CASES_THEN varsl ttac =
    DISJ_CASES_THENL
       (map (fn vars => EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);


(*---------------------------------------------------------------------------*
 * Version that chooses the y's as variants of the x's.                      *
 *---------------------------------------------------------------------------*)

fun CASES_THENL ttacl = DISJ_CASES_THENL (map (REPEAT_TCL CHOOSE_THEN) ttacl);


(*---------------------------------------------------------------------------*
 * Tactical to strip off ONE disjunction, conjunction, or existential.       *
 *---------------------------------------------------------------------------*)

val STRIP_THM_THEN = FIRST_TCL [CONJUNCTS_THEN, DISJ_CASES_THEN, CHOOSE_THEN];



(* ---------------------------------------------------------------------*)
(* Resolve implicative assumptions with an antecedent			*)
(* ---------------------------------------------------------------------*)

fun ANTE_RES_THEN ttac ante : tactic =
  Tactical.ASSUM_LIST
     (Tactical.EVERY o (mapfilter (fn imp => ttac (MATCH_MP imp ante))));

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

local
  fun MATCH_MP impth = let
    val sth = SPEC_ALL impth
    val hyptyvars = HOLset.listItems (hyp_tyvars sth)
    val lconstants = HOLset.intersection
                         (FVL [concl sth] empty_tmset, hyp_frees sth)
    val matchfn =
        match_terml hyptyvars lconstants (fst(dest_imp(concl sth)))
  in fn th => MP (INST_TY_TERM (matchfn (concl th)) sth) th
  end;

(* ---------------------------------------------------------------------*)
(* check ex l : Fail with ex if l is empty, otherwise return l.		*)
(* ---------------------------------------------------------------------*)

fun check ex [] = raise ex
  | check ex l = l;

(* ---------------------------------------------------------------------*)
(* IMP_RES_THEN  : Resolve an implication against the assumptions.	*)
(* ---------------------------------------------------------------------*)
in
fun IMP_RES_THEN ttac impth =
 let val ths = RES_CANON impth
      handle HOL_ERR _ => raise ERR "IMP_RES_THEN" "No implication"
 in
  Tactical.ASSUM_LIST
   (fn asl =>
     let val l = itlist (fn th => append (mapfilter(MATCH_MP th) asl)) ths []
         val res  = check (ERR "IMP_RES_THEN" "No resolvents") l
         val tacs = check (ERR "IMP_RES_THEN" "No tactics")
                          (Lib.mapfilter ttac res)
     in
        Tactical.EVERY tacs
     end)
 end;

(* ---------------------------------------------------------------------*)
(* RES_THEN    : Resolve all implicative assumptions against the rest.	*)
(* ---------------------------------------------------------------------*)

fun RES_THEN ttac (asl,g) =
 let val aas  = map ASSUME asl
     val ths  = itlist append (mapfilter RES_CANON aas) []
     val imps = check (ERR "RES_THEN" "No implication") ths
     val l    = itlist (fn th => append (mapfilter (MATCH_MP th) aas)) imps []
     val res  = check (ERR "RES_THEN" "No resolvents") l
     val tacs = check (ERR "RES_THEN" "No tactics")
                         (Lib.mapfilter ttac res)
 in
   Tactical.EVERY tacs (asl,g)
 end
end;

end
