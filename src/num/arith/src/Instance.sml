(*****************************************************************************)
(* FILE          : instance.sml                                              *)
(* DESCRIPTION   : Conversional for increasing the power of a conversion by  *)
(*                 allowing it to work on a substitution instance of a term  *)
(*                 that is acceptable to it.                                 *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 30th January 1992                                         *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Instance :> Instance =
struct

open Arbint HolKernel boolLib;

(*---------------------------------------------------------------------------*)
(* INSTANCE_T_CONV : (term -> term list) -> conv -> conv                     *)
(*                                                                           *)
(* Generalizes a conversion that is used to prove formulae true by replacing *)
(* any syntactically unacceptable subterms with variables, attempting to     *)
(* prove this generalised formula, and if successful re-instantiating.       *)
(* The first argument is a function for obtaining a list of syntactically    *)
(* unacceptable subterms of a term. This function should include in its      *)
(* result list any variables in the term that do not appear in other         *)
(* subterms returned. The second argument is the conversion to be            *)
(* generalised.                                                              *)
(*---------------------------------------------------------------------------*)

fun INSTANCE_T_CONV detector conv tm =
 let val (univs,tm') = strip_forall tm
     val insts = Lib.mk_set (detector tm')
     val vars = map (genvar o type_of) insts
     val s = map2 (curry op |->) insts vars
     val tm'' = list_mk_forall (vars, subst s tm')
 in
    EQT_INTRO (GENL univs (SPECL insts (EQT_ELIM (conv tm''))))
 end;

end
