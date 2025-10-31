(* ========================================================================== *)
(* FILE          : hh_demoScript.sml                                          *)
(* DESCRIPTION   : HolyHammer demo                                            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2020                                                       *)
(* ========================================================================== *)
Theory hh_demo
Ancestors
  arithmetic real complex
Libs
  holyHammer


(* load "holyHammer"; open holyHammer; *)
(* mlibUseful.trace_level := 0; *)

(* -------------------------------------------------------------------------
   Example 1: integer exponentation
   ------------------------------------------------------------------------- *)

(* hh ([],``a <= b ==> (g ** (b - a) * g ** a = g ** b)``); *)
Theorem EXP_NEG:
    a <= b ==> (g ** (b - a) * g ** a = g ** b)
Proof
  METIS_TAC [SUB_ADD, EXP_ADD]
QED

(* -------------------------------------------------------------------------
   Example 2: inversion
   ------------------------------------------------------------------------- *)

(* load "realTheory"; open realTheory; *)
(* hh ([], ``a = b * 2 ==> b = a / 2``); *)
Theorem INV_DIV2:
    a = b * 2 ==> b = a / 2
Proof
  METIS_TAC [REAL_DOUBLE, REAL_HALF_DOUBLE, REAL_MUL_ASSOC, real_div]
QED

(* -------------------------------------------------------------------------
   Example 3: Euler's formula
   ------------------------------------------------------------------------- *)

(* load "complexTheory"; open complexTheory; *)
(* hh ([], ``exp (i * (2 * pi)) = 1``); set_timeout 60; *)
Theorem EXP_2PI:
    exp (i * (2 * pi)) = 1
Proof
  METIS_TAC [EXP_IMAGINARY, complex_of_num, complex_of_real, REAL_ADD_LID,
    REAL_DOUBLE, REAL_NEGNEG, transcTheory.COS_0, transcTheory.COS_PERIODIC_PI,
    transcTheory.SIN_0, transcTheory.SIN_PERIODIC_PI]
QED


