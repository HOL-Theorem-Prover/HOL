(****************************************************************************)
(* FILE          : BoyerMooreLib.sml                                        *)
(* DESCRIPTION   : The main functions for the Boyer-Moore-style prover.     *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 27th June 1991                                           *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 5th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreLib =
struct

local

open HolKernel Parse 
     basicHol90Lib Psyntax BoyerMooreSupport BoyerMooreWaterfall

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMoore",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* BOYER_MOORE : conv                                                       *)
(*                                                                          *)
(* Boyer-Moore-style automatic theorem prover.                              *)
(* Given a term (--`tm`--), attempts to prove |- tm.                        *)
(*--------------------------------------------------------------------------*)

fun BOYER_MOORE tm =
   (proof_print_depth := 0;
    proof_print_newline
       (WATERFALL
           [clausal_form_heuristic,
            BoyerMooreTermsAndClauses.subst_heuristic,
            BoyerMooreTermsAndClauses.simplify_heuristic,
            BoyerMooreEqualities.use_equality_heuristic,
            BoyerMooreGeneralize.generalize_heuristic,
            BoyerMooreIrrelevance.irrelevance_heuristic]
           BoyerMooreInduction.induction_heuristic
           (tm,false)))
   handle HOL_ERR _ => failwith "BOYER_MOORE";

(*--------------------------------------------------------------------------*)
(* BOYER_MOORE_CONV : conv                                                  *)
(*                                                                          *)
(* Boyer-Moore-style automatic theorem prover.                              *)
(* Given a term (--`tm`--), attempts to prove |- tm = T.                    *)
(*--------------------------------------------------------------------------*)

fun BOYER_MOORE_CONV tm =
   EQT_INTRO (BOYER_MOORE tm) handle HOL_ERR _ => failwith "BOYER_MOORE_CONV";

(*--------------------------------------------------------------------------*)
(* HEURISTIC_TAC :                                                          *)
(*    ((term * bool) -> ((term * bool) list * proof)) list -> tactic        *)
(*                                                                          *)
(* Tactic to do automatic proof using a list of heuristics. The tactic will *)
(* fail if it thinks the goal is not a theorem. Otherwise it will either    *)
(* prove the goal, or return as subgoals the conjectures it couldn't        *)
(* handle.                                                                  *)
(*                                                                          *)
(* If the `proof_printing' flag is set to true, the tactic displays each    *)
(* new conjecture it generates, prints blank lines between subconjectures   *)
(* which resulted from a split, and prints a final blank line when it can   *)
(* do no more.                                                              *)
(*                                                                          *)
(* Given a goal, the tactic constructs an implication from it, so that the  *)
(* hypotheses are made available. It then tries to prove this implication.  *)
(* When it can do no more, the function splits the clauses that it couldn't *)
(* prove into disjuncts. The last disjunct is assumed to be a conclusion,   *)
(* and the rest are taken to be hypotheses. These new goals are returned    *)
(* together with a proof of the original goal.                              *)
(*                                                                          *)
(* The proof takes a list of theorems for the subgoals and discharges the   *)
(* hypotheses so that the theorems are in clausal form. These clauses are   *)
(* then used to prove the implication that was constructed from the         *)
(* original goal. Finally the antecedants of this implication are           *)
(* undischarged to give a theorem for the original goal.                    *)
(*--------------------------------------------------------------------------*)

fun HEURISTIC_TAC heuristics (asl,w) =
   (proof_print_depth := 0;
    let fun negate tm = if (is_neg tm) then (rand tm) else (mk_neg tm)
        and NEG_DISJ_DISCH tm th =
           if (is_neg tm)
           then BoyerMooreIrrelevance.DISJ_DISCH (rand tm) th
           else CONV_RULE (REWR_CONV IMP_DISJ_THM) (DISCH tm th)
        val tm = list_mk_imp (asl,w)
        val tree =
           proof_print_newline
              (waterfall (clausal_form_heuristic::heuristics) (tm,false))
        val tml = map #1 (fringe_of_clause_tree tree)
        val disjsl = map disj_list tml
        val goals =
           map (fn disjs => (map negate (butlast disjs),last disjs)) disjsl
        fun proof thl =
           let val thl' =
                  map (fn (th,goal) => itlist NEG_DISJ_DISCH (#1 goal) th)
                     (combine (thl,goals))
           in  funpow (length asl) UNDISCH (prove_clause_tree tree thl')
           end
    in  (goals,proof)
    end)
   handle HOL_ERR _ => failwith "HEURISTIC_TAC";

(*--------------------------------------------------------------------------*)
(* BOYER_MOORE_TAC : tactic                                                 *)
(*                                                                          *)
(* Tactic to do automatic proof using Boyer & Moore's heuristics. The       *)
(* tactic will fail if it thinks the goal is not a theorem. Otherwise it    *)
(* will either prove the goal, or return as subgoals the conjectures it     *)
(* couldn't handle.                                                         *)
(*--------------------------------------------------------------------------*)

fun BOYER_MOORE_TAC aslw =
   HEURISTIC_TAC
      [BoyerMooreTermsAndClauses.subst_heuristic,
       BoyerMooreTermsAndClauses.simplify_heuristic,
       BoyerMooreEqualities.use_equality_heuristic,
       BoyerMooreGeneralize.generalize_heuristic,
       BoyerMooreIrrelevance.irrelevance_heuristic,
       BoyerMooreInduction.induction_heuristic]
      aslw
   handle HOL_ERR _ => failwith "BOYER_MOORE_TAC";

(*--------------------------------------------------------------------------*)
(* BM_SIMPLIFY_TAC : tactic                                                 *)
(*                                                                          *)
(* Tactic to do automatic simplification using Boyer & Moore's heuristics.  *)
(* The tactic will fail if it thinks the goal is not a theorem. Otherwise,  *)
(* it will either prove the goal or return the simplified conjectures as    *)
(* subgoals.                                                                *)
(*--------------------------------------------------------------------------*)

fun BM_SIMPLIFY_TAC aslw =
   HEURISTIC_TAC [BoyerMooreTermsAndClauses.subst_heuristic,
                  BoyerMooreTermsAndClauses.simplify_heuristic] aslw
   handle HOL_ERR _ => failwith "BM_SIMPLIFY_TAC";

(*--------------------------------------------------------------------------*)
(* BM_INDUCT_TAC : tactic                                                   *)
(*                                                                          *)
(* Tactic which attempts to do a SINGLE induction using Boyer & Moore's     *)
(* heuristics. The cases of the induction are returned as subgoals.         *)
(*--------------------------------------------------------------------------*)

fun BM_INDUCT_TAC aslw =
   let val induct = ref true
       fun once_induction_heuristic x =
          if !induct
          then (induct := false; BoyerMooreInduction.induction_heuristic x)
          else failwith ""
   in  HEURISTIC_TAC [once_induction_heuristic] aslw
   end
   handle HOL_ERR _ => failwith "BM_INDUCT_TAC";

end;

end; (* BoyerMoore *)
