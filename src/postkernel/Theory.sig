signature Theory =
sig

  type hol_type  = Type.hol_type
  type term      = Term.term
  type thm       = Thm.thm
  type thy_addon = {sig_ps    : (unit -> HOLPP.pretty) option,
                    struct_ps : (unit -> HOLPP.pretty) option}
  type num = Arbnum.num
  datatype thm_src_location = datatype DB_dtype.thm_src_location
  type thminfo = DB_dtype.thminfo

(* Create a new theory *)

  val new_theory         : string -> unit

(* Add to the current theory segment *)

  val temp_binding       : string -> string
  val is_temp_binding    : string -> bool
  val dest_temp_binding  : string -> string
  val new_type           : string * int -> unit
  val new_constant       : string * hol_type -> unit
  val new_axiom          : string * term -> thm
  val save_thm           : string * thm -> thm
  val save_private_thm   : string * thm -> thm
  val gen_save_thm       : {name:string,private:bool,thm:thm,
                            loc: thm_src_location} -> thm
  val gen_new_axiom      : string * term * thm_src_location -> thm

(* Delete from the current theory segment *)

  val delete_type        : string -> unit
  val delete_const       : string -> unit
  val delete_binding     : string -> unit

(* Modify binding in the current theory segment *)

  val upd_binding        : string -> (thminfo -> thminfo) -> unit

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
  val current_ML_deps    : unit -> string list

(* Support for persistent theories *)

  val adjoin_to_theory       : thy_addon -> unit
  val adjoin_after_completion: (unit -> HOLPP.pretty) -> unit
  val quote_adjoin_to_theory : string quotation -> string quotation -> unit
  val export_theory          : unit -> unit

(* Make hooks available so that theory changes can be seen by
   "interested parties" *)
  val register_hook : string * (TheoryDelta.t -> unit) -> unit
  val delete_hook : string -> unit
  val get_hooks : unit -> (string * (TheoryDelta.t -> unit)) list
  val disable_hook : string -> ('a -> 'b) -> 'a -> 'b
  val enable_hook : string -> ('a -> 'b) -> 'a -> 'b

(* -- and persistent data added to theories *)
  structure LoadableThyData : sig
    type t
    type shared_writemaps = TheoryPP.shared_writemaps
    type shared_readmaps = TheoryPP.shared_readmaps
    val new : {thydataty : string, pp : 'a -> string,
               merge : 'a * 'a -> 'a,
               terms : 'a -> term list,
               strings : 'a -> string list,
               read : shared_readmaps -> HOLsexp.t -> 'a option,
               write : shared_writemaps -> 'a -> HOLsexp.t} ->
              ('a -> t) * (t -> 'a option)
    val segment_data : {thy: string, thydataty: string} -> t option
    val segment_data_string : {thy:string,thydataty:string} -> string option

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
                               shared_readmaps : shared_readmaps,
                               data : HOLsexp.t} -> unit
    (* updates segment data using an encoded string *)
  end

(* Extensions by definition *)
  structure Definition : sig
    val new_type_definition    : string * thm -> thm
    val located_new_type_definition :
        {loc:thm_src_location,name:string,witness:thm} -> thm
    val new_definition         : string * term -> thm
    val located_new_definition :
        {loc:thm_src_location,name:string,def:term} -> thm
    val new_specification      : string * string list * thm -> thm
    val located_new_specification :
        {loc:thm_src_location,name:string,constnames:string list,
         witness: thm} -> thm
    val gen_new_specification  : string * thm -> thm
    val located_gen_new_specification :
        {name:string,witness:thm, loc: thm_src_location} -> thm

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

(* recording a dependency of the theory on an ML module *)
  val add_ML_dependency  : string -> unit

  val format_name_message : {pfx:string,name:string} -> string

(* For internal use *)

  val pp_thm                 : (thm -> HOLPP.pretty) ref
  val link_parents           : string*num*num -> (string*num*num) list -> unit
  val incorporate_types      : string -> (string*int) list -> unit


  val store_definition       : string * thm -> thm
  val gen_store_definition   : string * thm * thm_src_location -> thm
  val incorporate_consts : string -> hol_type Vector.vector ->
                           (string*int) list -> unit
  (* Theory files (which are just SML source code) call this function as
     the last thing done when they load.  This will in turn cause a
     TheoryDelta event to be sent to all registered listeners *)
  val load_complete : string -> unit

end
