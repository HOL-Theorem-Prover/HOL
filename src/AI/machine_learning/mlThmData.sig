signature mlThmData =
sig

  include Abbrev

  type thmdata = (int, real) Redblackmap.dict *
    (string, int list) Redblackmap.dict

  (* theorems from the global namespace *)
  val namespace_tag : string
  val unsafe_namespace_thms : unit -> (string * thm) list
  val safe_namespace_thms : unit -> (string * thm) list

  (* theorem strings *)
  val dbfetch_of_thmid : string -> string
  val dbfetch_of_depid : thm -> string option
  val mk_metis_call : string list -> string

  (* data for the nearest neighbor predictor *)
  val create_thmdata : unit -> thmdata

  (* caching features of goals for faster creation of thmdata *)
  val clean_goalfea_cache : unit -> unit

  (* dependencies of a top-level theorem *)
  val depnumber_of_thm : thm -> int
  val intactdep_of_thm : thm -> bool * string list
  val validdep_of_thmid : string -> string list

  (* SML value of theorem identifiers *)
  val thm_of_name : string -> (string * thm) option
  val thml_of_namel : string list -> (string * thm) list

end
