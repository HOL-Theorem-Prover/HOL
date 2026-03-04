signature TraceMetadata =
sig
  type metadata = {
    n_types : int,
    n_terms : int,
    p_min_id : int,
    p_max_id : int,
    heap_parent : string option,
    thy_name : string,
    exports : (string * int) list,
    name_refs : (int * string * string) list,
    load_refs : (int * string * int) list,
    const_defs : (int * string * string list) list,
    type_defs : (int * string * string) list,
    const_decls : (string * string * int) list,
    type_decls : (string * string * int) list,
    t_const_refs : (int * string * string) list,
    y_tyop_refs : (int * string * string) list,
    compute_ids : int list,
    c_deps : (int list * int list * int list) option
  }

  (* Write a .pftm metadata file *)
  val write : string -> metadata -> unit

  (* Read a .pftm metadata file. Returns NONE if not found. *)
  val read : string -> metadata option

  (* Extract metadata by scanning a .pft trace file.
     Expensive: reads the entire decompressed file. *)
  val extract : string -> metadata

  (* Derive .pftm path from a .pft base path *)
  val metadata_path : string -> string
end
