(* ===================================================================== *)
(* FILE          : hol_pp.sig                                            *)
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
  val pp_type : Portable.ppstream -> Type.hol_type -> unit
  val pp_term : Portable.ppstream -> Term.term -> unit
  val type_to_string : Type.hol_type -> string
  val term_to_string : Term.term -> string
  val print_type : Type.hol_type -> unit
  val print_term : Term.term -> unit
end;
