(* ========================================================================= *)
(* FILE          : Theory.sml                                                *)
(* DESCRIPTION   : Management of logical theories.                           *)
(*                                                                           *)
(* AUTHOR        : Konrad Slind, University of Calgary                       *)
(*                 (also T.U. Munich and Cambridge)                          *)
(* DATE          : September 11, 1991                                        *)
(* REVISION      : August 7, 1997                                            *)
(*               : March 9, 1998                                             *)
(*               : August 2000                                               *)
(*                                                                           *)
(* ========================================================================= *)

signature Theory =
sig

  type hol_type  = Type.hol_type
  type term      = Term.term
  type thm       = Thm.thm
  type ppstream  = Portable.ppstream
  type thy_addon = {sig_ps    : (ppstream -> unit) option,
                    struct_ps : (ppstream -> unit) option}
 
(* Create a new theory *)

  val new_theory         : string -> unit

(* Adding to the current theory *)

  val new_type           : string * int -> unit
  val new_constant       : string * hol_type -> unit
  val new_axiom          : string * term -> thm
  val save_thm           : string * thm -> thm

(* Delete from the current theory *)

  val delete_type        : string -> unit
  val delete_const       : string -> unit
  val delete_axiom       : string -> unit
  val delete_definition  : string -> unit
  val delete_theorem     : string -> unit

(* Information on the current theory segment *)

  val current_theory     : unit -> string
  val parents            : string -> string list
  val ancestry           : string -> string list
  val types              : string -> (string * int) list
  val constants          : string -> term list
  val axioms             : unit -> (string * thm) list
  val definitions        : unit -> (string * thm) list
  val theorems           : unit -> (string * thm) list
  val axiom              : string -> thm
  val definition         : string -> thm
  val theorem            : string -> thm

(* Support for persistent theories *)

  val adjoin_to_theory   : thy_addon -> unit
  val export_theory      : unit -> unit
  val after_new_theory   : (string -> unit) -> unit

(* Freshness information on HOL objects *)

  val uptodate_type      : hol_type -> bool
  val uptodate_term      : term -> bool
  val uptodate_thm       : thm -> bool
  val scrub              : unit -> unit

(* Changing internal bindings of ML-level names to theory objects *)

  val set_MLname         : string -> string -> unit

(* For internal use *)

  val pp_thm             : (ppstream -> thm -> unit) ref
  val link_parents       : string*int*int -> (string*int*int)list -> unit
  val incorporate_types  : string -> (string*int) list -> unit
  val incorporate_consts : string -> (string*hol_type)list -> unit

end;
