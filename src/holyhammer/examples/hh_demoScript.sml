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
val th = store_thm ("EXP_NEG",
  ``a <= b ==> (g ** (b - a) * g ** a = g ** b)``,
  METIS_TAC [SUB_ADD, EXP_ADD]);

(* -------------------------------------------------------------------------
   Example 2: inversion
   ------------------------------------------------------------------------- *)

(* load "realTheory"; open realTheory; *)
(* hh ([], ``a = b * 2 ==> b = a / 2``); *)
val th = store_thm ("INV_DIV2",
  ``a = b * 2 ==> b = a / 2``,
  METIS_TAC [REAL_DOUBLE, REAL_HALF_DOUBLE, REAL_MUL_ASSOC, real_div])

(* -------------------------------------------------------------------------
   Example 3: Euler's formula
   ------------------------------------------------------------------------- *)

(* load "complexTheory"; open complexTheory; *)
(* hh ([], ``exp (i * (2 * pi)) = 1``); set_timeout 60; *)
val th = store_thm ("EXP_2PI",
  ``exp (i * (2 * pi)) = 1``,
  METIS_TAC [EXP_IMAGINARY, complex_of_num, complex_of_real, REAL_ADD_LID,
    REAL_DOUBLE, REAL_NEGNEG, transcTheory.COS_0, transcTheory.COS_PERIODIC_PI,
    transcTheory.SIN_0, transcTheory.SIN_PERIODIC_PI])


