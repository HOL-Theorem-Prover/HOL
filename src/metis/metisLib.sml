(* ========================================================================= *)
(* THE METIS LIBRARY                                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

structure metisLib :> metisLib =
struct

open HolKernel Parse boolLib folTools metisTools;

type 'a stream = 'a mlibStream.stream;

(* ------------------------------------------------------------------------- *)
(* Prolog solver.                                                            *)
(* ------------------------------------------------------------------------- *)

fun PROLOG_SOLVE ths =
  FOL_SOLVE mlibMeson.prolog
  {parm =
   {equality   = false,
    boolean    = false,
    combinator = false,
    mapping    = {higher_order = false, with_types = true}},
   thms = ths,
   hyps = [],
   lim  = mlibMeter.unlimited};

end