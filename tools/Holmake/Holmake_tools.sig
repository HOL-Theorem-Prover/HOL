signature Holmake_tools =
sig

  datatype CodeType =
           Theory of string
         | Script of string
         | Other of string

  datatype ArticleType =
           RawArticle of string
         | ProcessedArticle of string

  datatype File =
           SML of CodeType
         | SIG of CodeType
         | UO of CodeType
         | UI of CodeType
         | ART of ArticleType
         | Unhandled of string

  (* file lists are dependencies *)
  datatype buildcmds = Compile of File list
                     | BuildScript of string * File list
                     | BuildArticle of string * File list
                     | ProcessArticle of string

  (* simple list things *)
  val member : ''a -> ''a list -> bool
  val set_union : ''a list -> ''a list -> ''a list
  val delete : ''a -> ''a list -> ''a list
  val set_diff : ''a list -> ''a list -> ''a list
  val remove_duplicates : ''a list -> ''a list

  (* fixed constants *)
  val DEFAULT_OVERLAY : string

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


  type 'optv buildinfo_t = {
    optv : 'optv, hmake_options : string list,
    actual_overlay : string option,
    envlist : string -> string list,
    quit_on_failure : bool,
    outs : output_functions
  }




  val do_lastmade_checks: output_functions ->
                          {no_lastmakercheck : bool} ->
                          unit


  (* File IO *)
  val string_part : File -> string
  val toCodeType : string -> CodeType
  val toFile : string -> File
  val codeToString : CodeType -> string
  val articleToString : ArticleType -> string
  val fromFile : File -> string
  val fromFileNoSuf : File -> string
  val file_compare : File * File -> order
  val primary_dependent : File -> File option
  val exists_readable : string -> bool
  val generate_all_plausible_targets : string option -> File list

  val clean_dir : {extra_cleans: string list} -> unit
  val clean_depdir : {depdirname : string} -> bool

  structure hmdir : sig
    type t
    val extendp : {base : t, extension : string} -> t
    val extend : {base : t, extension : t} -> t
    val toString : t -> string
    val toAbsPath : t -> string
    val fromPath : {origin: string, path : string} -> t
    val sort : t list -> t list
    val curdir : unit -> t
    val compare : t * t -> order
  end

  type include_info = {includes : string list, preincludes : string list}
  type 'dir holmake_dirinfo = {visited : hmdir.t Binaryset.set,
                               includes : 'dir list,
                               preincludes : 'dir list}
  type 'dir holmake_result = 'dir holmake_dirinfo option

  val maybe_recurse :
      {warn: string -> unit,
       diag : string -> unit,
       no_prereqs : bool,
       hm: {dir : hmdir.t,
            visited : hmdir.t Binaryset.set,
            targets : string list} ->
           hmdir.t holmake_result,
       dirinfo : string holmake_dirinfo,
       dir : hmdir.t,
       local_build : include_info -> bool,
       cleantgt : string option} ->
      hmdir.t holmake_result

  val holdep_arg : File -> File option

  val get_direct_dependencies :
      {incinfo : include_info, DEPDIR : string,
       output_functions : output_functions,
       extra_targets : string list } ->
      File -> File list
  exception HolDepFailed

  val forces_update_of : string * string -> bool


end
