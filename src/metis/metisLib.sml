(* ========================================================================= *)
(* THE METIS LIBRARY                                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

structure metisLib :> metisLib =
struct

open HolKernel Parse boolLib folTools metisTools;

type 'a stream = 'a mlibStream.stream;

(* ------------------------------------------------------------------------- *)
(* Chatting and error handling.                                              *)
(* ------------------------------------------------------------------------- *)

local
  open mlibUseful;
in
  fun chat l m = trace {module = "metisLib", message = m, level = l};
  val ERR = mk_HOL_ERR "metisLib";
  val BUG = BUG;
end;

(* ------------------------------------------------------------------------- *)
(* Prolog solver.                                                            *)
(* ------------------------------------------------------------------------- *)

local
  val prolog_parm =
    {equality   = false,
     boolean    = false,
     combinator = false,
     mapping    = {higher_order = false, with_types = true}};
in
  fun PROLOG_SOLVE ths =
    let
      val () = (chat 1 "prolog: "; chat 2 "\n")
    in
      FOL_SOLVE mlibMeson.prolog
      {parm = prolog_parm, thms = ths, hyps = [], lim  = mlibMeter.unlimited}
    end;
end;

end