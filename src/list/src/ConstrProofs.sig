(* ===================================================================== *)
(* FILE          : ConstrProofs.sig                                      *)
(* DESCRIPTION   : Signature for proof support for concrete datatypes.   *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


signature ConstrProofs =
sig
   val prove_constructors_one_one  : Thm.thm -> Thm.thm
   val prove_constructors_distinct : Thm.thm -> Thm.thm
end;
