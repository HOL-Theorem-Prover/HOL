signature mlThmData =
sig

  include Abbrev

  type thmid = string
  type thmdata = (int, real) Redblackmap.dict * (thmid * mlFeature.fea) list
  val empty_thmdata : thmdata

  (* theorems from the global namespace *)
  val namespace_tag : string
  val unsafe_namespace_thms : unit -> (string * thm) list
  val safe_namespace_thms : unit -> (string * thm) list

  (* theorem strings *)
  val dbfetch_of_thmid : string -> string
  val dbfetch_of_depid : thm -> string option
  val mk_metis_call : string list -> string

  (* data for the nearest neighbor predictor *)
  val create_thmdata_time : real ref
  val add_cthy_time : real ref
  val add_namespace_time : real ref
  val thmdata_tfidf_time : real ref
  val create_thmdata : unit -> thmdata
  val clean_create_thmdata_cache : unit -> unit

  (* dependencies of a top-level theorem *)
  val depnumber_of_thm : thm -> int
  val intactdep_of_thm : thm -> bool * string list
  val validdep_of_thmid : string -> string list

  (* SML value of theorem identifiers *)
  val thm_of_name : string -> (string * thm) option
  val thml_of_namel : string list -> (string * thm) list

end
