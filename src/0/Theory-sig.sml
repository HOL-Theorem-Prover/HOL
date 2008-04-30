signature Theory =
sig

  type hol_type
  type term
  type thm
  type ppstream  = Portable.ppstream
  type thy_addon = {sig_ps    : (ppstream -> unit) option,
                    struct_ps : (ppstream -> unit) option}
  type num = Arbnum.num

(* Create a new theory *)

  val new_theory         : string -> unit

(* Add to the current theory segment *)

  val new_type           : string * int -> unit
  val new_constant       : string * hol_type -> unit
  val new_axiom          : string * term -> thm
  val save_thm           : string * thm -> thm

(* Delete from the current theory segment *)

  val delete_type        : string -> unit
  val delete_const       : string -> unit
  val delete_binding     : string -> unit

(* Information on the current theory segment *)

  val current_theory     : unit -> string
  val stamp              : string -> Time.time
  val parents            : string -> string list
  val ancestry           : string -> string list
  val types              : string -> (string * int) list
  val constants          : string -> term list
  val current_axioms     : unit -> (string * thm) list
  val current_theorems   : unit -> (string * thm) list
  val current_definitions : unit -> (string * thm) list

(* Support for persistent theories *)

  val adjoin_to_theory   : thy_addon -> unit
  val export_theory      : unit -> unit
  val after_new_theory   : (string * string -> unit) -> unit

(* Freshness information on HOL objects *)

  val uptodate_type      : hol_type -> bool
  val uptodate_term      : term -> bool
  val uptodate_thm       : thm -> bool
  val scrub              : unit -> unit
  val try_theory_extension : ('a->'b) -> 'a -> 'b

(* Changing internal bindings of ML-level names to theory objects *)

  val set_MLname         : string -> string -> unit

(* For internal use *)

  val pp_thm             : (ppstream -> thm -> unit) ref
  val link_parents       : string*num*num -> (string*num*num)list -> unit
  val incorporate_types  : string -> (string*int) list -> unit
  val incorporate_consts : string -> (string*hol_type)list -> unit

end
