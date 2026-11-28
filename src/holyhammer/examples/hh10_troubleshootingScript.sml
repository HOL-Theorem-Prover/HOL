(* ========================================================================= *)
(* FILE          : hh10_troubleshootingScript.sml                            *)
(* DESCRIPTION   : HolyHammer examples: what to do when the hammer fails     *)
(*                                                                           *)
(* Each section starts from a goal on which a plain hammer call fails        *)
(* and shows what works instead.  The hh calls are the later hammer          *)
(* calls that succeed; they run when the theory is built, and the            *)
(* comment after each is the proof HolyHammer printed.                       *)
(* ========================================================================= *)
Theory hh10_troubleshooting
Ancestors
  list rich_list pred_set real
Libs
  realLib holyHammer

(* -------------------------------------------------------------------------
   Failure 1: "ATPs could not find a proof" on a goal that is false

   The hammer cannot tell a false goal from a hard one, and it fails on
     LENGTH (TAKE n l) = n
   Before trying harder, evaluate the goal on a small example:
   EVAL ``LENGTH (TAKE 1 ([] : num list)) = 1`` returns F.  TAKE cannot
   take more elements than the list has, so the statement lacks a
   hypothesis.  With it, the hammer succeeds:
   ------------------------------------------------------------------------- *)

Theorem length_take_le:
  n <= LENGTH l ==> LENGTH (TAKE n l) = n
Proof
  hh
  (* metis_tac [LENGTH_TAKE] *)
QED

(* -------------------------------------------------------------------------
   Failure 2: "ATPs could not find a proof" on a decidable goal

   A point a third of the way from x to y lies strictly between them.
   The hammer fails on this.  It is linear real arithmetic, which
   REAL_ARITH_TAC decides at once.  Likewise DECIDE_TAC and
   intLib.ARITH_TAC for natural numbers and integers, tautLib.TAUT_TAC
   for propositional tautologies, and EVAL_TAC for ground computation.
   ------------------------------------------------------------------------- *)

Theorem third_between:
  x < y ==> x < (2 * x + y) / 3 /\ (2 * x + y) / 3 < y : real
Proof
  REAL_ARITH_TAC
QED

(* -------------------------------------------------------------------------
   Failure 3: a goal that needs induction

   A partition of a list into the elements that satisfy P and those that
   do not.  The hammer fails on the whole goal: the provers do not do
   induction.  After Induct_on `l` it proves the base case but not the
   step case.  The simplifier, which knows FILTER's defining equations
   and can decide P h either way, closes both cases on its own.
   ------------------------------------------------------------------------- *)

Theorem filter_partition_length:
  LENGTH (FILTER P l) + LENGTH (FILTER (\x. ~P x) l) = LENGTH l
Proof
  Induct_on `l` >> rw []
QED

(* -------------------------------------------------------------------------
   Failure 4: "ATPs found proofs, but reconstruction failed for: ..."

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
   Failure 5: set-builder notation and big operators

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
