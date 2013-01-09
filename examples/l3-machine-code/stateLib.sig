signature stateLib =
sig
   include Abbrev

   type footprint_extra = (term * term) * (term -> term) * (term -> term)
   val dest_code_access: term -> int * term
   val gvar: string -> hol_type -> term
   val is_code_access: string * term -> term -> bool
   val list_mk_code_pool: term * term * term list -> term
   val mk_code_pool: term * term * term -> term
   val mk_pre_post:
      thm -> thm -> thm -> thm list -> (thm -> term * term * term) ->
      footprint_extra list -> (term list * term list * term -> term * term) ->
      thm -> term
   val pool_select_state_thm: thm -> thm list -> thm -> thm
   val read_footprint:
      thm -> thm list -> (thm -> term * term * term) -> footprint_extra list ->
      thm -> term list * term * term * term
   val sep_definitions: string -> string list list -> thm -> thm list
   val spec:
      thm -> thm list -> thm list -> thm list -> thm list -> thm list ->
      hol_type list -> tactic -> tactic -> thm * term -> thm
   val star_select_state_thm: thm -> thm list -> term list * thm -> thm
   val update_frame_state_thm:
      thm -> (Q.tmquote * Q.tmquote * Q.tmquote) list -> thm
   val vvar: hol_type -> term
   val varReset: unit -> unit
end
