(* ===================================================================== *)
(* FILE          : Hol_pp.sig                                            *)
(* DESCRIPTION   : Signature for the prettyprinting of HOL terms and     *)
(*                 types.                                                *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* EXTENDED      : Richard Boulton, March 2, 1994                        *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(* ===================================================================== *)


signature Hol_pp =
sig
  type ppstream = Portable.ppstream
  type term = Term.term
  type hol_type = Type.hol_type

  val pp_type        : ppstream -> hol_type -> unit
  val pp_term        : ppstream -> term -> unit
  val type_to_string : hol_type -> string
  val term_to_string : term -> string
  val print_type     : hol_type -> unit
  val print_term     : term -> unit
end;
