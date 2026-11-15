(* ========================================================================= *)
(* FILE          : hh10_troubleshootingScript.sml                            *)
(* DESCRIPTION   : HolyHammer examples: what to do when the hammer fails     *)
(*                                                                           *)
(* Each section starts from a goal on which a plain hammer call failed       *)
(* and shows what worked instead.  The (* hh *) marks show where a later     *)
(* hammer call succeeded.                                                    *)
(* ========================================================================= *)
Theory hh10_troubleshooting
Ancestors
  list rich_list pred_set real transc complex
Libs
  realLib

(* -------------------------------------------------------------------------
   Failure 1: "ATPs could not find a proof" on a goal that is false

   The hammer cannot tell a false goal from a hard one.  Before trying
   harder, evaluate the goal on a small example.  For
     LENGTH (l1 ++ l2) = LENGTH l1
   EVAL ``LENGTH ([] ++ [0]) = LENGTH ([] : num list)`` returns F, so the
   intended statement must be something else.  The counterexample also
   makes a proof of the negation:
   ------------------------------------------------------------------------- *)

Theorem length_append_not_left:
  ~!(l1 : num list) l2. LENGTH (l1 ++ l2) = LENGTH l1
Proof
  strip_tac >>
  first_x_assum (qspecl_then [`[]`, `[0]`] mp_tac) >>
  EVAL_TAC
QED

(* -------------------------------------------------------------------------
   Failure 2: "ATPs could not find a proof" on a decidable goal

   The midpoint of x < y is below y.  The hammer sometimes finds a
   seven-lemma proof of this, and sometimes fails.  It is linear real
   arithmetic, which REAL_ARITH_TAC decides at once.  Likewise
   DECIDE_TAC and intLib.ARITH_TAC for natural numbers and integers,
   tautLib.TAUT_TAC for propositional tautologies, and EVAL_TAC for
   ground computation.
   ------------------------------------------------------------------------- *)

Theorem midpoint_below:
  x < y ==> (x + y) / 2 < y : real
Proof
  REAL_ARITH_TAC
QED

(* A partition of a list into the elements that satisfy P and those that
   do not.  The hammer fails on the whole goal (it needs induction), and
   after Induct_on `l` it proves the base case but not the step case.
   The simplifier, which knows FILTER's defining equations and can
   decide P h either way, closes both cases on its own. *)
Theorem filter_partition_length:
  LENGTH (FILTER P l) + LENGTH (FILTER (\x. ~P x) l) = LENGTH l
Proof
  Induct_on `l` >> rw []
QED

(* -------------------------------------------------------------------------
   Failure 3: "ATPs found proofs, but reconstruction failed for: ..."

   A prover found a proof, but Metis could not replay it within
   preplay_timeout (1 s by default).  The message lists the facts each
   prover used:

     ATPs found proofs, but reconstruction failed for:
     vampire: [pred_setTheory.IMAGE_SURJ, pred_setTheory.IN_IMAGE]
     e: [pred_setTheory.IMAGE_SURJ, pred_setTheory.IN_IMAGE]

   The facts are correct; Metis just needs help.  metis_tac with the two
   facts does not finish within 20 seconds, and neither does a larger
   preplay_timeout.  Rewriting with the equation first, and leaving the
   rest to Metis, works instantly.  Rule of thumb: rewrite with the
   listed equations (rw, simp, gvs) and give the remaining facts to
   metis_tac.
   ------------------------------------------------------------------------- *)

Theorem surj_iff_image:
  SURJ f s t <=> IMAGE f s = t /\ (!x. x IN s ==> f x IN t)
Proof
  rw [IMAGE_SURJ] >> metis_tac [IN_IMAGE]
QED

(* -------------------------------------------------------------------------
   Failure 4: set-builder notation and big operators

   [Paulson] An example from Lawrence Paulson's "Sledgehammer: some
   history, some tips".  The hammer fails on the whole statement, and
   also after rw [EXTENSION]: the goal still contains membership in a
   BIGINTER of an IMAGE, which is higher-order.  One more rewrite with
   the membership lemma for that combination (found with
   DB.find "BIGINTER_IMAGE") turns the goal into pure first-order
   logic.  The hammer's answer is then "metis_tac []": no lemmas at
   all.  Paulson's advice is the same in Isabelle: simplify first
   (auto), then hammer each resulting goal.
   ------------------------------------------------------------------------- *)

Theorem biginter_image_inter:
  C <> {} ==>
  BIGINTER (IMAGE (\x. A x INTER B x) C) =
  BIGINTER (IMAGE A C) INTER BIGINTER (IMAGE B C)
Proof
  rw [EXTENSION, IN_BIGINTER_IMAGE] >>
  (* hh *)
  metis_tac []
QED

(* -------------------------------------------------------------------------
   Not a failure: a slow call

   Euler's identity for a full turn, from the original HolyHammer demo.
   Following the demo, the call was made with a 60-second budget:

     hhConfig.hh_set ("timeout", "60");

   Vampire found a proof in 0.4 seconds, using 37 facts about complex
   numbers, sin and cos.  Replaying the proof in Metis and minimising
   the list took most of the call's time: every attempt to drop a fact
   is a Metis replay (bounded by twice the last successful replay time,
   and by minimize_timeout).  Long lists like this one are
   typical of proofs that unfold definitions (complex_of_real,
   complex_mul, RE, IM).  If a call is slow, look at the slice
   timings: when the prover answered early, more time will not change
   the outcome.  hhConfig.hh_set ("minimize", "false") skips the
   minimisation, at the price of a longer lemma list.
   ------------------------------------------------------------------------- *)

Theorem exp_two_pi_i:
  exp (i * (2 * pi)) = 1
Proof
  (* hh *)
  metis_tac [EXP_IMAGINARY, RE, IM, i, pairTheory.FST, pairTheory.SND,
             REAL_MUL_LID, COS_PERIODIC, REAL_DOUBLE, SIN_PERIODIC_PI,
             complex_of_real, complex_of_num, SIN_0, COS_0,
             COMPLEX_SCALAR_MUL_COMM, COMPLEX_SCALAR_LMUL_NEG1,
             COMPLEX_SCALAR_RMUL_NEG, complex_scalar_lmul, complex_mul,
             REAL_ADD_RID, REAL_SUB_RZERO, COMPLEX_SCALAR_LMUL_ENTIRE,
             COMPLEX_MUL_ARG]
QED
