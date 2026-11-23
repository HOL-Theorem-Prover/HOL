(* ========================================================================= *)
(* FILE          : hh10_troubleshootingScript.sml                            *)
(* DESCRIPTION   : HolyHammer examples: what to do when the hammer fails     *)
(* ADAPTED FROM  : an example from Thibault Gauthier's HolyHammer demo.      *)
(*                                                                           *)
(* Each section starts from a goal on which a plain hammer call failed       *)
(* and shows what worked instead.  The hh calls are the later hammer         *)
(* calls that succeeded; they run when the theory is built, and the          *)
(* comment after each is the proof HolyHammer printed.                       *)
(* ========================================================================= *)
Theory hh10_troubleshooting
Ancestors
  list rich_list pred_set real transc complex
Libs
  realLib holyHammer

(* -------------------------------------------------------------------------
   Failure 1: "ATPs could not find a proof" on a goal that is false

   The hammer cannot tell a false goal from a hard one.  Before trying
   harder, evaluate the goal on a small example.  For
     LENGTH (l1 ++ l2) = LENGTH l1
   EVAL ``LENGTH ([] ++ [0]) = LENGTH ([] : num list)`` returns F, so the
   intended statement must be something else.  The hammer proves the
   negation:
   ------------------------------------------------------------------------- *)

Theorem length_append_not_left:
  ~!(l1 : num list) l2. LENGTH (l1 ++ l2) = LENGTH l1
Proof
  hh
  (* metis_tac [LENGTH_APPEND, arithmeticTheory.ADD_CLAUSES, LENGTH,
                cvTheory.SUC_EQ] *)
QED

(* -------------------------------------------------------------------------
   Failure 2: "ATPs could not find a proof" on a decidable goal

   A point a third of the way from x to y lies strictly between them.
   The hammer fails on this.  It is linear real arithmetic, which
   REAL_ARITH_TAC decides at once.  Likewise
   DECIDE_TAC and intLib.ARITH_TAC for natural numbers and integers,
   tautLib.TAUT_TAC for propositional tautologies, and EVAL_TAC for
   ground computation.
   ------------------------------------------------------------------------- *)

Theorem third_between:
  x < y ==> x < (2 * x + y) / 3 /\ (2 * x + y) / 3 < y : real
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
   preplay_timeout (2.5 s by default).  The message lists the facts each
   prover used; here every list contains the equation IMAGE_SURJ.
   Rewriting with it first, and leaving the rest to Metis, works
   instantly.  Rule of thumb: rewrite with the listed equations (rw,
   simp, gvs) and give the remaining facts to metis_tac.
   ------------------------------------------------------------------------- *)

Theorem surj_iff_image:
  SURJ f s t <=> IMAGE f s = t /\ (!x. x IN s ==> f x IN t)
Proof
  rw [IMAGE_SURJ] >> metis_tac [IN_IMAGE]
QED

(* -------------------------------------------------------------------------
   Failure 4: set-builder notation and big operators

   Lawrence Paulson's "Sledgehammer: some history, some tips" warns
   that goals with set comprehensions are hard for the hammer.  This
   one shows why.  The hammer fails on the whole statement, and also
   after rw [EXTENSION]: the goal still contains membership in a
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
  hh
  (* metis_tac [] *)
QED

(* -------------------------------------------------------------------------
   Not a failure: a long proof

   Euler's identity for a full turn, from the original HolyHammer demo.
   The hammer proves it in a few seconds, but the proof needs eleven
   facts, among them the definitions complex_of_num, complex_of_real
   and complex_scalar_rmul.  Long lists like this are typical of proofs
   that unfold definitions.
   ------------------------------------------------------------------------- *)

Theorem exp_two_pi_i:
  exp (i * (2 * pi)) = 1
Proof
  hh
  (* metis_tac [EXP_IMAGINARY, complex_scalar_rmul, REAL_MUL_LZERO,
                complex_of_num, complex_of_real, COMPLEX_MUL_LID,
                COMPLEX_EXP_0, REAL_MUL_COMM, COMPLEX_MUL_ARG, SIN_PERIODIC,
                COS_PERIODIC] *)
QED
