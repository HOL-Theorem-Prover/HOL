(* ===================================================================== *)
(* FILE          : net.sig                                               *)
(* DESCRIPTION   : Signature for term nets.                              *)
(*                                                                       *)
(* AUTHOR        : Somebody at ICL.                                      *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(* ===================================================================== *)

signature Net =
sig
(*  structure Term : Public_term_sig *)
  type 'a net
  val empty_net : 'a net
  val enter : Term.term * 'a -> 'a net -> 'a net
  val lookup : Term.term -> 'a net -> 'a list
end;
