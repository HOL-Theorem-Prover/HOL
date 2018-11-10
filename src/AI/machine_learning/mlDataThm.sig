signature mlDataThm =
sig

  include Abbrev

  type fea = int list

  (* theorems from the global namespace *)
  val namespace_tag : string
  val unsafe_namespace_thms : unit -> (string * thm) list
  val safe_namespace_thms : unit -> (string * thm) list

  (* theorem strings *)
  val dbfetch_of_thmid : string -> string
  val dbfetch_of_depid : thm -> string option
  val mk_metis_call : string list -> string
  
  (* data for the nearest neighbor predictor *)
  val create_thmdata : unit -> 
    (int, real) Redblackmap.dict * (string, int list) Redblackmap.dict
  val clean_goalfea_cache : unit -> unit  

  (* dependencies of a top-level theorem *)
  val validdep_of_thmid : string -> string list
  
  (* SML value of theorem identifiers *)
  val thm_of_name : string -> (string * thm) option
  val thml_of_namel : string list -> (string * thm) list

end
