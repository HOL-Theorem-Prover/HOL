(* =====================================================================*)
(* FILE          : Gspec.sig                                            *)
(* DESCRIPTION   : Signature for support for set abstractions.          *)
(*                                                                      *)
(* =====================================================================*)


signature Gspec =
sig
   val SET_SPEC_CONV : Thm.thm -> Abbrev.conv
end;
