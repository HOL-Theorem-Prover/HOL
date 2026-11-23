(* ========================================================================= *)
(* FILE          : hh11_complexScript.sml                                    *)
(* DESCRIPTION   : HolyHammer examples: a long proof about complex numbers   *)
(* ADAPTED FROM  : an example from Thibault Gauthier's HolyHammer demo.      *)
(*                                                                           *)
(* The hh call runs HolyHammer when the theory is built; the comment after   *)
(* it is the proof HolyHammer printed.  This file is separate from           *)
(* hh06_real because the facts of complexTheory change the hammer's          *)
(* premise selection for the real-number goals there.                        *)
(* ========================================================================= *)
Theory hh11_complex
Ancestors
  real transc complex
Libs
  realLib holyHammer

(* -------------------------------------------------------------------------
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
