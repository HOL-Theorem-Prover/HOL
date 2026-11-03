(* Tables keyed by a float type pair plus a rounding mode, for          *)
(* binary_ieeeLib.                                                      *)
(*                                                                      *)
(* This instantiation lives in its own file rather than in              *)
(* binary_ieeeLib.sml because mosml needs Table.ui named on the         *)
(* compiler command line for a functor application (its dependency      *)
(* auto-detection misses them), and a Holmakefile rule supplying it     *)
(* bypasses Holmake's quote filter.  binary_ieeeLib.sml contains HOL    *)
(* quotations, so it cannot carry such a rule; this file deliberately   *)
(* contains none.  See src/floating-point/Holmakefile.                  *)

structure TwmTab = Table(
  type key = (Type.hol_type * Type.hol_type) * Term.term
  val ord = Lib.pair_compare
              (Lib.pair_compare (Type.compare, Type.compare),
               Term.compare)
  fun pp _ = HOLPP.add_string "<twm-key>"
)
