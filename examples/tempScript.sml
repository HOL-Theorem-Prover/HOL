(*---------------------------------------------------------------------------*
 * tempScript.sml:                                                           *
 *                                                                           *
 * A template theory script suitable for Holmake. If you are going to use it *
 * for theory "x", you must change the name of this file to "xScript.sml",   *
 * and the argument to "new_theory" below must be changed to be "x".         *
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*
 * First, make standard environment available.                               *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib;


(*---------------------------------------------------------------------------*
 * Next, bring in extra tools used. For example, if you were going to use    *
 * bossLib, then while you were working interactively, you may have to       *
 * execute                                                                   *
 *                                                                           *
      load "bossLib";                                                        *
 *                                                                           *
 * before executing                                                          *
 *                                                                           *
      open bossLib;                                                          *
 *                                                                           *
 * However, when using the batch compiler, the call to "load" isn't allowed. *
 *                                                                           *
 * The following opening of bossLib is only for example. You should only     *
 * refer to modules that are used.                                           *
 *---------------------------------------------------------------------------*)

open bossLib;


(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "temp";


< THIS AREA INTENTIONALLY LEFT BLANK: YOUR STUFF GOES HERE! >


(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
