(* ===================================================================== *)
(* FILE          : let_conv.sig                                          *)
(* DESCRIPTION   : Signature for paired beta conversion and "let" terms. *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


signature Let_conv =
sig
   val PAIRED_BETA_CONV : Abbrev.conv
   val let_CONV : Abbrev.conv
   val PAIRED_ETA_CONV : Abbrev.conv
   val GEN_BETA_CONV : Abbrev.conv
end;
