signature tttManifest =
sig

  (* -----------------------------------------------------------------------
     Compatibility versions.
     Bump format_version when the on-disk tactic-data representation
     changes.  Bump tactictoe_version when recorder, feature, or learning
     changes make existing tactic data unsuitable.  Either bump makes every
     recorded theory stale.
     ----------------------------------------------------------------------- *)
  val format_version : int
  val tactictoe_version : int
  val manifest_format_version : int

  type provenance = {tacdata_version : int, tactictoe_version : int}

  type entry =
    { thy : string, data_hash : string, src_hash : string,
      anc_version : int, anc_hash : string, recorded_at : int, failed : bool,
      tacdata_version : int, tactictoe_version : int }

  type manifest =
    { tacdata_version : int, tactictoe_version : int, entries : entry list }

  (* directories *)
  val tacdata_dir : unit -> string
  val tacdata_data_dir : unit -> string
  val manifest_file : unit -> string
  val manifest_generation : unit -> string

  (* theory identity *)
  val find_script : string -> string
  val ttt_ancestry : string -> string list
  val ancestry_version : string -> int
  val ancestry_hash : string -> string
  val source_hash : string -> string
  val current_provenance : unit -> provenance
  val tacdata_file_of_identity :
    string -> string -> int -> provenance -> string
  val current_tacdata_file : string -> string
  val entry_file : entry -> string

  (* manifest I/O; read_manifest returns NONE if the file is absent,
     unparsable, or written by a different manifest format version *)
  val read_manifest : unit -> manifest option
  val write_manifest : provenance -> entry list -> unit

  (* entry lookup and construction *)
  val entry_matches : provenance -> string -> string -> entry -> bool
  val find_entry : provenance -> string -> string -> manifest -> entry option
  val update_entry : entry -> entry list -> entry list
  val success_entry : provenance -> string -> string -> string -> entry
  val failed_entry : provenance -> string -> string -> entry

  (* resolving the tactic-data file of a theory; the _in variant takes an
     already-read manifest so that a caller resolving a whole ancestry does
     not re-read and re-parse the manifest once per theory *)
  val tacdata_file_for_thy : string -> string option
  val tacdata_file_for_thy_in : manifest option -> string -> string option

end
