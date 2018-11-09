signature smlThm =
sig

  type fea = int list

  (* theorems from the global namespace *)
  val namespace_tag : string
  val unsafe_namespace_thms : unit -> (string * thm) list
  val safe_namespace_thms : unit -> (string * thm) list

  (* theorem strings *)
  val dbfetch_of_sthm : string -> string
  val mk_metis_call : string list -> string
  
  (* data for the nearest neighbor predictor *)
  val create_thmdata : 
    unit -> (int, real) Redblackmap.dict * (string * fea) list
  
  (* SML value of theorem identifiers *)
  val thm_of_name : string -> (string * thm) option
  val thml_of_namel : string list -> (string * thm) list

end
