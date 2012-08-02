signature Theory =
sig

  type hol_type  = Type.hol_type
  type term      = Term.term
  type thm       = Thm.thm
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

(* Make hooks available so that theory changes can be seen by
   "interested parties" *)
  val register_hook : string * (TheoryDelta.t -> unit) -> unit
  val delete_hook : string -> unit
  val get_hooks : unit -> (string * (TheoryDelta.t -> unit)) list

(* -- and persistent data added to theories *)
  structure LoadableThyData : sig
    type t
    val new : {thydataty : string, merge : 'a * 'a -> 'a,
               read : string -> 'a option, write : 'a -> string} ->
              ('a -> t) * (t -> 'a option)
    val segment_data : {thy: string, thydataty: string} -> t option

    val write_data_update : {thydataty : string, data : t} -> unit
    val set_theory_data : {thydataty : string, data : t} -> unit
    (* call these in a session to update and record something for later -
       these will update segment data, and  also cause a call to
       temp_encoded_update to appear in the theory file meaning that the
       change to the data will persist/be exported.  The first,
       write_data_update uses the merge functionality to augment what has
       already been stored.  The set_theory_data function overrides whatever
       might have been there. *)

    val temp_encoded_update : {thy : string, thydataty : string,
                               data : string} -> unit
    (* updates segment data using an encoded string *)
  end

(* Extensions by definition *)
  structure Definition : sig
    val new_type_definition    : string * thm -> thm
    val new_definition         : string * term -> thm
    val new_specification      : string * string list * thm -> thm

    val new_definition_hook    : ((term -> term list * term) *
                                  (term list * thm -> thm)) ref
  end

(* Freshness information on HOL objects *)

  val uptodate_type      : hol_type -> bool
  val uptodate_term      : term -> bool
  val uptodate_thm       : thm -> bool
  val scrub              : unit -> unit

  val try_theory_extension : ('a -> 'b) -> 'a -> 'b

(* Changing internal bindings of ML-level names to theory objects *)

  val set_MLname         : string -> string -> unit

(* For internal use *)

  val pp_thm             : (ppstream -> thm -> unit) ref
  val link_parents       : string*num*num -> (string*num*num)list -> unit
  val incorporate_types  : string -> (string*int) list -> unit


  val store_definition   : string * thm -> thm
  val incorporate_consts : string -> hol_type Vector.vector ->
                           (string*int) list -> unit
  (* Theory files (which are just SML source code) call this function as
     the last thing done when they load.  This will in turn cause a
     TheoryDelta event to be sent to all registered listeners *)
  val load_complete : string -> unit




end
