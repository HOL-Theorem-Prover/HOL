(* ===================================================================== *)
(* FILE          : dep_rewrite.sml                                       *)
(* VERSION       : 1.1                                                   *)
(* DESCRIPTION   : Dependent Rewriting Tactics (general purpose)         *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : May 7, 2002                                           *)
(* COPYRIGHT     : Copyright (c) 2002 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

(* ================================================================== *)
(* ================================================================== *)
(*                     DEPENDENT REWRITING TACTICS                    *)
(* ================================================================== *)
(* ================================================================== *)
(*                                                                    *)
(* This file contains new tactics for dependent rewriting,            *)
(* a generalization of the rewriting tactics of standard HOL.         *)
(*                                                                    *)
(* The main tactics are named DEP_REWRITE_TAC[thm1,...], etc., with   *)
(* the standard variations (PURE,ONCE,ASM).  In addition, tactics     *)
(* with LIST instead of ONCE are provided, making 12 tactics in all.  *)
(*                                                                    *)
(* The argument theorems thm1,... are typically implications.         *)
(* These tactics identify the consequents of the argument theorems,   *)
(* and attempt to match these against the current goal.  If a match   *)
(* is found, the goal is rewritten according to the matched instance  *)
(* of the consequent, after which the corresponding hypotheses of     *)
(* the argument theorems are added to the goal as new conjuncts on    *)
(* the left.                                                          *)
(*                                                                    *)
(* Care needs to be taken that the implications will match the goal   *)
(* properly, that is, instances where the hypotheses in fact can be   *)
(* proven.  Also, even more commonly than with REWRITE_TAC,           *)
(* the rewriting process may diverge.                                 *)
(*                                                                    *)
(* Each implication theorem for rewriting may have a layer of         *)
(* universal quantifications, under which is the base, which will     *)
(* either be an equality, a negation, or a general term.  The pattern *)
(* for matching will be the left-hand-side of an equality, the term   *)
(* negated of a negation, or the term itself in the third case.  The  *)
(* search is top-to-bottom, left-to-right, depending on the           *)
(* quantifications of variables.                                      *)
(*                                                                    *)
(* To assist in focusing the matching to useful cases, the goal is    *)
(* searched for a subterm matching the pattern.  The matching of the  *)
(* pattern to subterms is performed by higher-order matching, so for  *)
(* example, ``!x. P x`` will match the term ``!n. (n+m) < 4*n``.      *)
(*                                                                    *)
(* The argument theorems may each be either an implication or not.    *)
(* For those which are implications, the hypotheses of the instance   *)
(* of each theorem which matched the goal are added to the goal as    *)
(* conjuncts on the left side.  For those argument theorems which     *)
(* are not implications, the goal is simply rewritten with them.      *)
(* This rewriting is also higher order.                               *)
(*                                                                    *)
(* As much as possible, the newly added hypotheses are analyzed to    *)
(* remove duplicates; thus, several theorems with the same            *)
(* hypothesis, or several uses of the same theorem, will generate     *)
(* a minimal additional proof burden.                                 *)
(*                                                                    *)
(* The new hypotheses are added as conjuncts rather than as a         *)
(* separate subgoal to reduce the user's burden of subgoal splits     *)
(* when creating tactics to prove theorems.  If a separate subgoal    *)
(* is desired, simply use CONJ_TAC after the dependent rewriting to   *)
(* split the goal into two, where the first contains the hypotheses   *)
(* and the second contains the rewritten version of the original      *)
(* goal.                                                              *)
(*                                                                    *)
(* The tactics including PURE in their name will only use the         *)
(* listed theorems for all rewriting; otherwise, the standard         *)
(* rewrites are used for normal rewriting, but they are not           *)
(* considered for dependent rewriting.                                *)
(*                                                                    *)
(* The tactics including ONCE in their name attempt to use each       *)
(* theorem in the list, only once, in order, left to right.           *)
(* The hypotheses added in the process of dependent rewriting are     *)
(* not rewritten by the ONCE tactics.  This gives a more restrained   *)
(* version of dependent rewriting.                                    *)
(*                                                                    *)
(* The tactics with LIST take a list of lists of theorems, and        *)
(* uses each list of theorems once in order, left-to-right.  For      *)
(* each list of theorems, the goal is rewritten as much as possible,  *)
(* until no further changes can be achieved in the goal.  Hypotheses  *)
(* are collected from all rewriting and added to the goal, but they   *)
(* are not themselves rewritten.                                      *)
(*                                                                    *)
(* The tactics without ONCE or LIST attempt to reuse all theorems     *)
(* repeatedly, continuing to rewrite until no changes can be          *)
(* achieved in the goal.  Hypotheses are rewritten as well, and       *)
(* their hypotheses as well, ad infinitum.                            *)
(*                                                                    *)
(* The tactics with ASM in their name add the assumption list to      *)
(* the list of theorems used for dependent rewriting.                 *)
(*                                                                    *)
(* There are also three more general tactics provided,                *)
(* DEP_FIND_THEN, DEP_ONCE_FIND_THEN, and DEP_LIST_FIND_THEN,         *)
(* from which the others are constructed.                             *)
(*                                                                    *)
(* The differences among these is that DEP_ONCE_FIND_THEN uses        *)
(* each of its theorems only once, in order left-to-right as given,   *)
(* whereas DEP_FIND_THEN continues to reuse its theorems repeatedly   *)
(* as long as forward progress and change is possible.  In contrast   *)
(* to the others, DEP_LIST_FIND_THEN takes as its argument a list     *)
(* of lists of theorems, and processes these in order, left-to-right. *)
(* For each list of theorems, the goal is rewritten as many times     *)
(* as they apply.  The hypotheses for all these rewritings are        *)
(* collected into one set, added to the goal after all rewritings.    *)
(*                                                                    *)
(* DEP_ONCE_FIND_THEN and DEP_LIST_FIND_THEN will not attack the      *)
(* hypotheses generated as a byproduct of the dependent rewriting;    *)
(* in contrast, DEP_FIND_THEN will.  DEP_ONCE_FIND_THEN and           *)
(* DEP_LIST_FIND_THEN might be fruitfully applied again to their      *)
(* results; DEP_FIND_THEN will complete any possible rewriting,       *)
(* and need not be reapplied.                                         *)
(*                                                                    *)
(* These take as argument a thm_tactic, a function which takes a      *)
(* theorem and yields a tactic.  It is this which is used to apply    *)
(* the instantiated consequent of each successfully matched           *)
(* implication to the current goal.  Usually this is something like   *)
(* (fn th => REWRITE_TAC[th]), but the user is free to supply any     *)
(* thm_tactic he wishes.                                              *)
(*                                                                    *)
(* One significant note: because of the strategy of adding new        *)
(* hypotheses as conjuncts to the current goal, it is not fruitful    *)
(* to add *any* new assumptions to the current goal, as one might     *)
(* think would happen from using, say, ASSUME_TAC.                    *)
(*                                                                    *)
(* Rather, any such new assumptions introduced by thm_tactic are      *)
(* specifically removed.  Instead, one might wish to try MP_TAC,      *)
(* which will have the effect of ASSUME_TAC and then undischarging    *)
(* that assumption to become an antecedent of the goal.  Other        *)
(* thm_tactics may be used, and they may even convert the single      *)
(* current subgoal into multiple subgoals.  If this happens, it is    *)
(* fine, but note that the control strategy of DEP_FIND_THEN will     *)
(* continue to attack only the first of the multiple subgoals.        *)
(*                                                                    *)
(* ================================================================== *)
(* ================================================================== *)


structure dep_rewrite :> dep_rewrite =
struct

open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;

type term = Term.term
type fixity = Parse.fixity
type thm = Thm.thm;



local

val show_rewrites = ref false; (* normally false, set true for tracing   *)

val debug         = false;  (* normally false, set to true for debugging *)
val debug_fail    = false;  (* normally false, set to true for debugging *)
val debug_match   = false;  (* normally false, set to true for debugging *)
val debug_matches = false;  (* normally false, set to true for debugging *)

(* Printing functions: (only needed for debugging) *)
val print_string = TextIO.print;
fun print_newline() = print_string "\n";
fun print_strings []        = ()
   | print_strings (t :: []) = print_string t
   | print_strings (t :: ts) = (print_string t; print_string ",";
                                print_strings ts);
fun print_theorem th = (print_string (thm_to_string th); print_newline());
fun print_terms []        = ()
   | print_terms (t :: []) = print_term t
   | print_terms (t :: ts) = (print_term t; print_string ","; print_terms ts);
fun print_all_thm th =
   let val (ant,conseq) = dest_thm th
   in (print_string "["; print_terms ant; print_string "] |- ";
       print_term conseq; print_newline() )
   end;
fun print_theorems []        = ()
   | print_theorems (t :: ts) = (print_theorem t; print_string "\n";
                                 print_theorems ts);
fun print_goal (asl,gl) = (print_term gl; print_newline());
fun pthm th = (print_all_thm th; th);
(**)

fun TACTIC_ERR{function,message} =
    Feedback.HOL_ERR{origin_structure = "Tactic",
                      origin_function = function,
                      message = message};

fun failwith function = 
   ( (**) if debug_fail then
         print_string ("Failure in dep_rewrite: "^function^"\n")
     else (); (**)
    raise TACTIC_ERR{function = function,message = "Failure in dep_rewrite"});



fun UNDER_FORALL_CONV conv tm =
    if is_forall tm then 
       RAND_CONV (ABS_CONV (UNDER_FORALL_CONV conv)) tm
    else
       conv tm ;

(* Does multiple conversions of ==> to /\:
val assemble_ants =
      CONV_RULE (REPEATC (UNDER_FORALL_CONV RIGHT_IMP_FORALL_CONV)
                 THENC UNDER_FORALL_CONV (REPEATC (REWR_CONV AND_IMP_INTRO)));
*)

val assemble_ants =
      CONV_RULE (REPEATC (UNDER_FORALL_CONV RIGHT_IMP_FORALL_CONV)
                 THENC UNDER_FORALL_CONV (TRY_CONV (REWR_CONV AND_IMP_INTRO)));

(*
assemble_ants EQ_LIST;
*)

(*
val DEP_PENETRATE_CONV =
    TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV
    THENC PURE_REWRITE_CONV[AND_IMP_INTRO];

val DEP_PENETRATE_RULE = CONV_RULE DEP_PENETRATE_CONV;

val DEP_PENETRATE_ASSUM_TAC =
    RULE_ASSUM_TAC DEP_PENETRATE_RULE;

val DEP_PENETRATE_TAC =
    CONV_TAC DEP_PENETRATE_CONV
    THEN DEP_PENETRATE_ASSUM_TAC;
*)


fun UNDISCH_NOT_NEG th =
  MP th (ASSUME(fst(dest_imp_only(concl th))))
  handle HOL_ERR  _ => failwith "UNDISCH_NOT_NEG";

fun UNDISCH_ALL_NOT_NEG th =
    if is_imp_only(concl th)
       then UNDISCH_ALL_NOT_NEG (UNDISCH_NOT_NEG th)
       else th;


fun DEP_FIND_matches th =
   let 
       val tha = (* CONV_RULE (REPEATC
                     (UNDER_FORALL_CONV RIGHT_IMP_FORALL_CONV)) *) th;
       val tm = concl tha
       val (avs,bod) = strip_forall tm
       val (ants,conseq) = strip_imp_only bod
       val th1 = SPECL avs (ASSUME tm)
       val th2 = UNDISCH_ALL_NOT_NEG th1
       val evs = filter(fn v => all (free_in v) ants
                        andalso not(free_in v conseq)) avs
       val th3 = itlist SIMPLE_CHOOSE evs (DISCH tm th2)
       val hs = hyp th3
       fun DISCH_ALL hyps th = itlist DISCH hyps th
       val sth = MP (DISCH tm (GEN_ALL (DISCH_ALL hs (UNDISCH th3)))) tha
       val term_to_match =
              (lhs conseq
               handle _ =>
               dest_neg conseq
               handle _ =>
               conseq)
  (*   val _ = (if !show_rewrites then
                  (print_string "Searching for ";
                   print_term term_to_match;
                   print_string "\n")
                  else ())   *)
       val match_fn =
           (HO_PART_MATCH (lhs o snd o strip_imp_only) sth
            handle _ =>
            HO_PART_MATCH (dest_neg o snd o strip_imp_only) sth
            handle _ =>
            HO_PART_MATCH (snd o strip_imp_only) sth)
   in
      match_fn
   end
   handle _ => failwith "DEP_FIND_matches: bad theorem";

fun SUB_matches (f:term->'a) tm =
   ( (* if debug_matches then (print_string "SUB_matches: ";
                    print_term tm; print_newline()) else (); *)
    if is_comb tm then
       (let val {Rator,Rand} = Rsyntax.dest_comb tm in
        (f Rator handle _ => f Rand)
        end)
    else
    if is_abs tm then
       let val {Bvar,Body} = Rsyntax.dest_abs tm in
           f Body
       end
    else failwith "SUB_matches");

fun ONCE_DEPTH_matches (f:term->'a) tm =
     ( (* if debug_matches then
        (print_string "ONCE_DEPTH_matches: "; print_term tm; print_newline())
      else (); *)
       (f tm handle _ => (SUB_matches (ONCE_DEPTH_matches f) tm)));




(* ================================================================== *)
(* APPLY_IMP_THEN ttac th is a dependent rewriting function,          *)
(* which takes a goal and produce a 5-tuple containing:               *)
(*                                                                    *)
(*     assumption list,                                               *)
(*     list of hypotheses,                                            *)
(*     list of justification functions for those hypotheses,          *)
(*     list of goals,                                                 *)
(*     and list of justification functions for those goals.           *)
(* ================================================================== *)

local

fun UNDISCH_ALL_NON_NEG th =
   if (is_imp (concl th) andalso not(is_neg(concl th)))
   then UNDISCH_ALL_NON_NEG (UNDISCH th)
   else th;

fun print_goals gl =
   if gl = [] then print_string "proved\n"
   else (map print_goal gl; ());

fun repeat_apply (f:'a->'b) step stop x =
      f x
    handle e =>
      let val x' = step x in
        if stop x x' then raise e
        else repeat_apply f step stop x'
      end;

in

fun APPLY_IMP_THEN ttac th (asl,gl) =
    let val _ = if !show_rewrites then
                   (print_string "Trying ";
                    print_theorem th)
                   else (); (**)
        val matched =
               repeat_apply
                  (fn th => ONCE_DEPTH_matches (DEP_FIND_matches th) gl)
                  assemble_ants
                  (fn th1 => fn th2 => concl th1 = concl th2)
                  th;
(*
ONCE_DEPTH_matches (DEP_FIND_matches th) gl
              handle e =>
               let val th' = assemble_ants th in
                if concl th' = concl th then raise e
                else
                  let val mtchd = ONCE_DEPTH_matches (DEP_FIND_matches th') gl
                  in (if !show_rewrites then
                        print_string "Found deeper match\n"
                      else ();
                      mtchd)
                  end
               end;
*)
(*      val _ = if !show_rewrites then
                      (print_string "match found:\n";
                       print_theorem matched)
                   else (); *)
        val base = UNDISCH_ALL_NON_NEG matched;
        val subgoal = concl base;
(**)    val _ = if !show_rewrites then
                       (print_string "Rewriting ";
                        print_term subgoal;
                        print_string "\n")
                   else (); (**)
        val (gl1,p1) = ( (*REPEAT GEN_TAC THEN*)
                          MATCH_MP_TAC matched) (asl,subgoal)
        val (gl2,p2) = ttac (Thm.ASSUME subgoal) (asl,gl);
    in
     case gl1
       of [(asl1,g1)] =>
       ( if !show_rewrites then
           (print_string "New burden: ";
            print_goals gl1;
            print_string "Revised goal: ";
            print_goals gl2;
            print_newline())
          else ();
         (asl1,[g1],[p1],gl2,p2) )
        | _ => failwith "APPLY_IMP_THEN"
    end

end;

(* ================================================================== *)
(* We now introduce a series of tacticals for dependent rewriting     *)
(* functions, which will be easily understood by relation to the      *)
(* corresponding tacticals for tactics and conversions.               *)
(* ================================================================== *)

(* TAC_DEP turns a tactic into a dependent rewriting function. *)

fun TAC_DEP tac = fn (asl,gl) =>
    let val (gl0,p0) = tac (asl,gl)
    in (asl,[],[],gl0,p0)
    end
    handle _ => failwith "TAC_DEP";



(* DEP_TAC turns a dependent rewriting function into a tactic. *)

type validation = Thm.thm list -> Thm.thm;

fun DEP_TAC dep :tactic = fn g0 =>
    let val (asl1,gls,(pls:validation list),(gl2:goal list),(p2:validation))
            = dep g0 in
    ( (* if debug then
        (print_string "DEP_TAC:\nburdens = [";
         map (fn tm => (print_newline(); print_term tm; print_string ",")) gls;
         print_string "]\ncurrent goals = [";
         map (fn g2 => (print_newline(); print_goal g2; print_string ",")) gl2;
         print_string "]\n")
    else (); *)
    if gls = [] then (gl2,p2)
    else 
    let
        val rgls = mk_set (flatten (map strip_conj gls));
        val gl1 = [(asl1,list_mk_conj rgls)];
        val p1 = (fn [th] => 
                  map2 (fn gl => fn p =>
                        p [( (* if debug then
                               (print_string "Prove: ";
                                print_term gl;
                                print_newline();
                                print_string "From: ";
                                print_theorem th;
                                print_newline())
                            else (); *)
                            prove(gl,REPEAT CONJ_TAC
                                     THEN FIRST(map ACCEPT_TAC (CONJUNCTS th)))
                            handle _ => failwith "Burden proof failed"
                                                     )]) gls pls
                   | _ => failwith "DEP_TAC");
    in
      ( (* if debug then
          (print_string "gl1 = \n"; print_goal (hd gl1))
       else (); *)
       case gl2
         of [] =>
           (gl1,(fn thl => itlist Drule.PROVE_HYP (p1 thl) (p2 [])))
          | ((asl2,g2)::gl3) =>
              case gl1
                of [(asl1,g1)] =>
                  ((intersect asl1 asl2,Rsyntax.mk_conj{conj1=g1,conj2=g2})::gl3,
                   (fn (tha::thl) => 
                          itlist Drule.PROVE_HYP (p1 [CONJUNCT1 tha])
                                                 (p2 ((CONJUNCT2 tha)::thl))
                     | [] => failwith "DEP_TAC"))
                 | _ => failwith "DEP_TAC"
      )
    end)
    end
    handle _ => failwith "DEP_TAC";



fun choplist a b =
   case a
   of [] =>
        ([],b)
    | (h::t) =>
        let val (c,d) = choplist t (tl b) in
            ((hd b)::c, d)
        end;

infix THEN1_DEP;

fun ctac1 THEN1_DEP ctac2 = fn g =>
    let val (asl1,gs1,ps1,gl1,p1) = ctac1 g
    in
    case gl1
    of [] => 
         (asl1,gs1,ps1,gl1,p1)
     | (g1::gl1') =>
         let val (asl2,gs2,ps2,gl2,p2) = ctac2 g1
         in
         (intersect asl1 asl2, gs1@gs2, ps1@ps2, gl2@gl1',
          (fn ths => let val (ths1,ths2) = choplist gl2 ths in
                          p1 ((p2 ths1) :: ths2)
                     end))
         end
    end
    handle _ => failwith "THEN1_DEP";


val ALL_DEP = fn (asl,gl) =>
    (asl,[],[],[(asl,gl)],hd);


infix ORELSE_DEP;

fun ctac1 ORELSE_DEP ctac2 = fn g =>
    ctac1 g handle _ => ctac2 g;


fun FIRST_DEP cl = 
    case cl
    of [] => 
         ALL_DEP
     | (c::cl') =>
         c ORELSE_DEP FIRST_DEP cl';


fun EVERY_DEP cl = 
    case cl
    of [] => 
         ALL_DEP
     | (c::cl') =>
         c THEN1_DEP EVERY_DEP cl'
    handle _ => failwith "EVERY_DEP";


fun REPEAT_DEP ctac g =
    ((ctac THEN1_DEP REPEAT_DEP ctac) ORELSE_DEP ALL_DEP) g;


fun CHANGED_DEP ctac g =
    let val (asl,gls,pls,gl,p) = ctac g in
    if gl = [g] then failwith "CHANGED_DEP"
    else (asl,gls,pls,gl,p)
    end;



(* We define theorem-tactics that take one theorem and rewrite with it. *)

fun REWRITE_THM th = REWRITE_TAC[th];
fun PURE_REWRITE_THM th = PURE_REWRITE_TAC[th];
fun ONCE_REWRITE_THM th = ONCE_REWRITE_TAC[th];
fun PURE_ONCE_REWRITE_THM th = PURE_ONCE_REWRITE_TAC[th];


(* ================================================================== *)
(* End of local declarations.                                         *)
(* Beginning of exported declarations.                                *)
(* ================================================================== *)

in


val show_rewrites = show_rewrites;


(* ================================================================== *)
(* ================================================================== *)
(*                     DEPENDENT REWRITING TACTICS                    *)
(* ================================================================== *)
(* ================================================================== *)

(* ================================================================== *)
(*                                                                    *)
(* The tactics including ONCE in their name attempt to use each       *)
(* theorem in the list, only once, in order, left to right.           *)
(* The hypotheses added in the process of dependent rewriting are     *)
(* not rewritten by the ONCE tactics.  This gives a more fine-grain   *)
(* control of dependent rewriting.                                    *)
(*                                                                    *)
(* ================================================================== *)



fun DEP_ONCE_FIND_THEN (ttac:thm->tactic) ths :tactic =
    DEP_TAC
         (EVERY_DEP (map (fn th => APPLY_IMP_THEN ttac th
                                    ORELSE_DEP TAC_DEP (ttac th))
                          (flatten (map CONJUNCTS ths))))
    handle _ => failwith "DEP_ONCE_FIND_THEN";



val DEP_PURE_ONCE_REWRITE_TAC :(thm list)->tactic =
    DEP_ONCE_FIND_THEN (fn th => Ho_Rewrite.PURE_ONCE_REWRITE_TAC[th]);

fun DEP_ONCE_REWRITE_TAC thl :tactic =
    DEP_PURE_ONCE_REWRITE_TAC thl
    THEN Ho_Rewrite.REWRITE_TAC[];

fun DEP_PURE_ONCE_ASM_REWRITE_TAC thl :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_PURE_ONCE_REWRITE_TAC (asl @ thl));

fun DEP_ONCE_ASM_REWRITE_TAC thl :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_ONCE_REWRITE_TAC (asl @ thl));


val DEP_PURE_ONCE_SUBST_TAC :(thm list)->tactic =
    DEP_ONCE_FIND_THEN (fn th => SUBST1_TAC th ORELSE ALL_TAC);

fun DEP_ONCE_SUBST_TAC thl :tactic =
    DEP_PURE_ONCE_SUBST_TAC thl
    THEN Ho_Rewrite.REWRITE_TAC[];

fun DEP_PURE_ONCE_ASM_SUBST_TAC thl :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_PURE_ONCE_SUBST_TAC (asl @ thl));

fun DEP_ONCE_ASM_SUBST_TAC thl :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_ONCE_SUBST_TAC (asl @ thl));




(* ================================================================== *)
(*                                                                    *)
(* The tactics including LIST in their name take a list of lists of   *)
(* implication theorems, and attempt to use each list of theorems     *)
(* once, in order, left to right.  Each list of theorems is applied   *)
(* by rewriting with each theorem in it as many times as they apply.  *)
(* The hypotheses added in the process of dependent rewriting are     *)
(* collected from all rewritings, but they are not rewritten by the   *)
(* LIST tactics.  This gives a moderate and more controlled degree    *)
(* of dependent rewriting than provided by DEP_REWRITE_TAC.           *)
(*                                                                    *)
(* ================================================================== *)



fun DEP_LIST_FIND_THEN (ttac:thm->tactic) thss :tactic =
    DEP_TAC
         (EVERY_DEP (map (fn ths =>
             REPEAT_DEP (CHANGED_DEP
                (EVERY_DEP (map (fn th =>
                                    APPLY_IMP_THEN ttac th
                                    ORELSE_DEP TAC_DEP (ttac th))
                                 (flatten (map CONJUNCTS ths))))))
                          thss))
    handle _ => failwith "DEP_LIST_FIND_THEN";



val DEP_PURE_LIST_REWRITE_TAC :(thm list list)->tactic =
    DEP_LIST_FIND_THEN (fn th => Ho_Rewrite.PURE_REWRITE_TAC[th]);

val DEP_LIST_REWRITE_TAC :(thm list list)->tactic =
    DEP_LIST_FIND_THEN (fn th => Ho_Rewrite.REWRITE_TAC[th]);

fun DEP_PURE_LIST_ASM_REWRITE_TAC thss :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_PURE_LIST_REWRITE_TAC
                                   (map (fn ths => asl @ ths) thss));

fun DEP_LIST_ASM_REWRITE_TAC thss :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_LIST_REWRITE_TAC
                                   (map (fn ths => asl @ ths) thss));




(* ================================================================== *)
(*                                                                    *)
(* The tactics without ONCE attept to reuse all theorems until no     *)
(* changes can be achieved in the goal.  Hypotheses are rewritten     *)
(* and new ones generated from them, continuing until no further      *)
(* progress is possible.                                              *)
(*                                                                    *)
(* ================================================================== *)


fun DEP_FIND_THEN (ttac:thm->tactic) ths :tactic =
    DEP_TAC (REPEAT_DEP (CHANGED_DEP
         (EVERY_DEP (map (fn th => APPLY_IMP_THEN ttac th
                                    ORELSE_DEP TAC_DEP (ttac th))
                          (flatten (map CONJUNCTS ths))))))
    handle _ => failwith "DEP_FIND_THEN";




fun DEP_PURE_REWRITE_TAC thl :tactic =
    REPEAT (CHANGED_TAC (DEP_FIND_THEN
                           (fn th => Ho_Rewrite.PURE_REWRITE_TAC[th]) thl));

fun DEP_REWRITE_TAC thl :tactic =
    REPEAT (CHANGED_TAC (DEP_FIND_THEN
                           (fn th => Ho_Rewrite.REWRITE_TAC[th]) thl));

fun DEP_PURE_ASM_REWRITE_TAC thl :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_PURE_REWRITE_TAC (asl @ thl));

fun DEP_ASM_REWRITE_TAC thl :tactic =
    Tactical.ASSUM_LIST (fn asl => DEP_REWRITE_TAC (asl @ thl));


end

(* ================================================================== *)
(* ================================================================== *)
(*                 END OF DEPENDENT REWRITING TACTICS                 *)
(* ================================================================== *)
(* ================================================================== *)


end;



(* TEST EXAMPLES:

load "dep_rewrite";
open dep_rewrite;
show_rewrites := true;

(* Example theorems to play with: *)

open arithmeticTheory;

(* Implication arithmetic theorems:

val LESS_LESS_EQ_TRANS = |- !m n p. m < n /\ n <= p ==> m < p : thm
val LESS_EQ_LESS_TRANS = |- !m n p. m <= n /\ n < p ==> m < p : thm
val LESS_MULT2 = |- !m n. 0 < m /\ 0 < n ==> 0 < m * n : thm
val CANCEL_SUB = |- !p n m. p <= n /\ p <= m ==> ((n - p = m - p) = n = m)
  : thm
val SUB_CANCEL = |- !p n m. n <= p /\ m <= p ==> ((p - n = p - m) = n = m)
  : thm
val SUB_LESS_EQ_ADD = |- !m p. m <= p ==> (!n. p - m <= n = p <= m + n) : thm
val LESS_EQ_IMP_LESS_SUC = |- !n m. n <= m ==> n < SUC m : thm
val LESS_IMP_LESS_ADD = |- !n m. n < m ==> (!p. n < m + p) : thm
val SUB_SUB = |- !b c. c <= b ==> (!a. a - b - c = (a + c) - b) : thm
val LESS_EQ_SUB_LESS = |- !a b. b <= a ==> (!c. a - b < c = a < b + c) : thm
val LESS_EQ_ADD_SUB = |- !c b. c <= b ==> (!a. (a + b) - c = a + (b - c)) : thm
val LESS_SUB_ADD_LESS = |- !n m i. i < n - m ==> i + m < n : thm
val SUB_LESS_OR = |- !m n. n < m ==> n <= m - 1 : thm
val INV_PRE_LESS_EQ = |- !n. 0 < n ==> (!m. PRE m <= PRE n = m <= n) : thm
val INV_PRE_LESS = |- !m. 0 < m ==> (!n. PRE m < PRE n = m < n) : thm
val MOD_MOD = |- !n. 0 < n ==> (!k. (k MOD n) MOD n = k MOD n) : thm
val MOD_PLUS =
  |- !n. 0 < n ==> (!j k. (j MOD n + k MOD n) MOD n = (j + k) MOD n) : thm
val MOD_TIMES = |- !n. 0 < n ==> (!q r. (q * n + r) MOD n = r MOD n) : thm
val MOD_MULT = |- !n r. r < n ==> (!q. (q * n + r) MOD n = r) : thm
val ZERO_DIV = |- !n. 0 < n ==> (0 DIV n = 0) : thm
val ZERO_MOD = |- !n. 0 < n ==> (0 MOD n = 0) : thm
val MOD_EQ_0 = |- !n. 0 < n ==> (!k. (k * n) MOD n = 0) : thm
val LESS_MOD = |- !n k. k < n ==> (k MOD n = k) : thm
val DIV_MULT = |- !n r. r < n ==> (!q. (q * n + r) DIV n = q) : thm
val MOD_UNIQUE = |- !n k r. (?q. (k = q * n + r) /\ r < n) ==> (k MOD n = r)
  : thm
val DIV_UNIQUE = |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
  : thm
val DIV_LESS_EQ = |- !n. 0 < n ==> (!k. k DIV n <= k) : thm
val LESS_EQUAL_ANTISYM = |- !n m. n <= m /\ m <= n ==> (n = m) : thm
val LESS_MONO_MULT = |- !m n p. m <= n ==> m * p <= n * p : thm
val LESS_IMP_LESS_OR_EQ = |- !m n. m < n ==> m <= n : thm
val LESS_EQ_LESS_EQ_MONO = |- !m n p q. m <= p /\ n <= q ==> m + n <= p + q
  : thm
val LESS_EQ_TRANS = |- !m n p. m <= n /\ n <= p ==> m <= p : thm
val LESS_MONO_ADD = |- !m n p. m < n ==> m + p < n + p : thm
val ADD_EQ_SUB = |- !m n p. n <= p ==> ((m + n = p) = m = p - n) : thm
val LESS_SUC_NOT = |- !m n. m < n ==> ~(n < SUC m) : thm
val INV_PRE_EQ = |- !m n. 0 < m /\ 0 < n ==> ((PRE m = PRE n) = m = n) : thm
val PRE_SUC_EQ = |- !m n. 0 < n ==> ((m = PRE n) = SUC m = n) : thm
val SUB_ADD = |- !m n. n <= m ==> ((m - n) + n = m) : thm
val LESS_ADD_NONZERO = |- !m n. ~(n = 0) ==> m < m + n : thm
val ADD_INV_0 = |- !m n. (m + n = m) ==> (n = 0) : thm
val LESS_CASES_IMP = |- !m n. ~(m < n) /\ ~(m = n) ==> n < m : thm
val LESS_NOT_SUC = |- !m n. m < n /\ ~(n = SUC m) ==> SUC m < n : thm
val LESS_SUC_EQ_COR = |- !m n. m < n /\ ~(SUC m = n) ==> SUC m < n : thm
val OR_LESS = |- !m n. SUC m <= n ==> m < n : thm
val LESS_OR = |- !m n. m < n ==> SUC m <= n : thm
val FUN_EQ_LEMMA = |- !f x1 x2. f x1 /\ ~(f x2) ==> ~(x1 = x2) : thm
val LESS_TRANS = |- !m n p. m < n /\ n < p ==> m < p : thm
val LESS_MONO_REV = |- !m n. SUC m < SUC n ==> m < n : thm

*)

(*
[LESS_EQ_ADD_SUB,SUB_ADD,SUB_SUB,ADD_EQ_SUB,LESS_TRANS,SUB_LESS_EQ_ADD,
 CANCEL_SUB,LESS_EQ_SUB_LESS,LESS_EQ_LESS_EQ_MONO];
*)


g `(10 + y) - y < 12`;
e(DEP_ONCE_REWRITE_TAC[LESS_EQ_ADD_SUB]);
e(RW_TAC arith_ss []);
drop();

g `(x + y) - (x + 2) <= 2 * y`;
e(ASM_CASES_TAC (--`2 <= y`--));

 e(DEP_REWRITE_TAC[SUB_LESS_EQ_ADD,LESS_EQ_LESS_EQ_MONO]);
 e(RW_TAC arith_ss []);

 val SUB_EQ_0_IMP = GEN_ALL(snd(EQ_IMP_RULE (SPEC_ALL SUB_EQ_0)));
 e(DEP_REWRITE_TAC[SUB_EQ_0_IMP]);
 e(RW_TAC arith_ss []);

drop();

g `(1 + (2 + (3 + (4 + (5 + 6))))) - 5 = 16`;
e(DEP_REWRITE_TAC[LESS_EQ_ADD_SUB]);
e(RW_TAC arith_ss []);
drop();

g `EL (SUC(SUC 0)) (ZIP([1;2;3],ZIP([4;5;6],[7;8;9]))) = (3,6,9)`;
val EL_ZIP = listTheory.EL_ZIP;
e(DEP_REWRITE_TAC[EL_ZIP]);
e(RW_TAC list_ss []);
drop();

g `0 < (@n. 0 < n)`;
e(DEP_ONCE_REWRITE_TAC[SELECT_AX]);
drop();

g `!P f x. P f ==> (x = f x)`;
e(DEP_ONCE_REWRITE_TAC[RIGHT_FORALL_IMP_THM]); 
drop();

*)

