signature Holmake_tools =
sig

  datatype CodeType =
           Theory of string
         | Script of string
         | Other of string

  datatype File =
           SML of CodeType
         | SIG of CodeType
         | UO of CodeType
         | UI of CodeType
         | Unhandled of string

  (* string/path manipulations *)
  val normPath : string -> string
  val fullPath : string list -> string
  val spacify : string list -> string
  val nspaces : (string -> unit) -> int -> unit
  val collapse_bslash_lines : string -> string
  val realspace_delimited_fields : string -> string list

  (* diagnostics/output *)
  type output_functions = {warn : string -> unit, info : string -> unit,
                           tgtfatal : string -> unit,
                           diag : string -> unit}
  val output_functions : {quiet_flag: bool, debug:bool} -> output_functions
  val die_with : string -> 'a


  val do_lastmade_checks: output_functions ->
                          {no_lastmakercheck : bool} ->
                          unit

  (* dependency analysis *)
  exception HolDepFailed
  val runholdep :
      {ofs : output_functions, includes : string list, extras : string list,
       arg : File, destination : string} -> unit

  (* File IO *)
  val string_part : File -> string
  val toCodeType : string -> CodeType
  val toFile : string -> File
  val codeToString : CodeType -> string
  val fromFile : File -> string
  val file_compare : File * File -> order
  val primary_dependent : File -> File option
  val exists_readable : string -> bool
  val generate_all_plausible_targets : string option -> File list

  val clean_dir : {extra_cleans: string list} -> unit
  val clean_depdir : {depdirname : string} -> bool

  val maybe_recurse :
      {warn: string -> unit,
       no_prereqs : bool,
       hm: {relpath:string option,abspath:string} -> string Binaryset.set ->
           string list -> string list -> string Binaryset.set option,
       visited: string Binaryset.set,
       includes : string list,
       dir : {abspath: string, relpath: string option},
       local_build : unit -> bool,
       cleantgt : string option} ->
      string Binaryset.set option

end
