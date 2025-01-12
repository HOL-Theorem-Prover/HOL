signature Holmake_tools =
sig

  datatype CodeType = datatype HOLFS_dtype.CodeType
  datatype ArticleType = datatype HOLFS_dtype.ArticleType
  datatype File = datatype HOLFS_dtype.File
  datatype buildcmds = datatype Holmake_tools_dtype.buildcmds

  val |> : 'a * ('a -> 'b) -> 'b
  val memoise : ('a * 'a -> order) -> ('a -> 'b) -> ('a -> 'b)

  (* simple list things *)
  val member : ''a -> ''a list -> bool
  val set_unionl : ''a list -> ''a list -> ''a list
  val delete : ''a -> ''a list -> ''a list
  val set_diffl : ''a list -> ''a list -> ''a list
  val remove_duplicates : ''a list -> ''a list
  val front : 'a list -> 'a list (* exception Empty *)
  val front_last : 'a list -> 'a list * 'a (* exception Empty *)

  (* comparisons *)
  type 'a cmp = 'a * 'a -> order
  val pair_compare : 'a cmp * 'b cmp -> ('a * 'b) cmp
  val inv_img_cmp  : ('b -> 'a) -> 'a cmp -> 'b cmp
  val lex_compare  : 'a cmp -> 'a list cmp

  (* fixed constants *)
  val DEFAULT_OVERLAY : string

  (* string/path manipulations *)
  val normPath : string -> string
  val fullPath : string list -> string
  val spacify : string list -> string
  val nspaces : (string -> unit) -> int -> unit
  val collapse_bslash_lines : string -> string
  val realspace_delimited_fields : string -> string list
  val kernelid_fname : string
  val concatWithf : ('a -> string) -> string -> 'a list -> string

  (* exceptions *)
  structure Exception : sig
    datatype 'a result = Res of 'a | Exn of exn
    val get_res : 'a result -> 'a option
    val get_exn : 'a result -> exn option
    val capture : ('a -> 'b) -> 'a -> 'b result
    val release : 'a result -> 'a
  end


  (* sets *)
  type 'a set = 'a Binaryset.set
  val set_add : 'a -> 'a set -> 'a set
  val set_addList : 'a list -> 'a set -> 'a set
  val set_union : 'a set -> 'a set -> 'a set
  val set_diff : 'a set -> 'a set -> 'a set
  val set_exists : ('a -> bool) -> 'a set -> bool
  val set_concatWith : ('a -> string) -> string -> 'a set -> string
  val set_mapPartial : ('a -> 'b option) -> 'b set -> 'a set -> 'b set
  val listItems : 'a set -> 'a list
  val set_member : 'a set -> 'a -> bool
  val empty_strset : string set

  (* terminal stuff: colouring of strings, getting width *)
  val red : string -> string
  val boldred : string -> string
  val boldgreen : string -> string
  val boldyellow : string -> string
  val bold : string -> string
  val dim : string -> string
  val CLR_EOL : string
  val getWidth : unit -> int
  val strip_codes : string -> string
  val noesc_size : string -> int

  (* diagnostics/output *)
  type output_functions = {warn : string -> unit,
                           info : string -> unit,
                           info_inline : string -> unit,
                           info_inline_end : unit -> unit,
                           chatty : string -> unit,
                           tgtfatal : string -> unit,
                           diag : string -> (unit -> string) -> unit}
  type 'a ofn_update = ('a -> 'a) -> output_functions -> output_functions
  val fupd_info_inline : (string -> unit) ofn_update
  val fupd_info_inline_end : (unit -> unit) ofn_update
  val fupd_info : (string -> unit) ofn_update
  val quieten_info : output_functions -> output_functions
  (* 0 : quiet, 1 : normal, 2 : chatty, 3 : everything + debug info *)
  val output_functions :
      {chattiness:int,
       debug: {ins:string list,outs:string list} option,
       usepfx:bool} -> output_functions
  val default_ofns : output_functions
  val die_with : string -> 'a


  val check_distrib : string -> string option
    (* check_distrib s returns SOME(HOLDIR/bin/s) if we are under some HOLDIR.*)
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
  val extract_theory : string list -> string option

  val clean_dir : output_functions -> {extra_cleans: string list} -> unit
  val clean_depdir : {depdirname : string} -> bool
  val clean_forReloc : {holheap : string option} -> unit
  val pushdir : string -> ('a -> 'b) -> ('a -> 'b)




  structure hmdir : sig
    type t
    val extendp : {base : t, extension : string} -> t
    val extend : {base : t, extension : t} -> t
    val toString : t -> string
    val toAbsPath : t -> string
    val getParent : t -> t (* loops/fixpoint at root *)
    val pretty_dir : t -> string (* uses holpathdb abbreviations *)
    val fromPath : {origin: string, path : string} -> t
    val sort : t list -> t list
    val curdir : unit -> t
    val compare : t * t -> order
    val eqdir : t -> t -> bool
    val chdir : t -> unit
  end
  val nice_dir : string -> string (* prints a dir with ~ when HOME is set *)
  type include_info = {includes : string list, preincludes : string list}
  val empty_incinfo : include_info
  type dirset = hmdir.t Binaryset.set
  type incset_pair = {pres : dirset, incs : dirset}
  val empty_dirset : dirset
  type incdirmap = (hmdir.t,incset_pair) Binarymap.dict
  val empty_incdirmap : incdirmap
  type holmake_dirinfo = {
    visited : hmdir.t Binaryset.set,
    incdirmap : incdirmap
  }
  type holmake_result = holmake_dirinfo option

  val process_hypat_options :
      string -> {noecho : bool, ignore_error : bool, command : string}

  (* nicely format a list of makefile targets *)
  val target_string : string list -> string

  val holdep_arg : File -> File option

  structure hm_target : sig
    type t
    val empty_tgtset : t Binaryset.set
    val mk : hmdir.t * File -> t
    val compare : t * t -> order
    val toString : t -> string
    val tgtset_diff : t list -> t list -> t list
    val tgtexists_readable : t -> bool
    val localFile : File -> t
    val filestr_to_tgt : string -> t (* directory dependent *)
    val setHMF_text : string -> t -> t
    val setFile : File -> t -> t
    val dirpart : t -> hmdir.t
    val filepart : t -> File
    val HMF_text : t -> string option
  end

  type dep = hm_target.t
  val tgt_toString : dep -> string

  val generate_all_plausible_targets :
        (string -> unit) -> dep option -> dep list


  val get_direct_dependencies :
      {incinfo : include_info, DEPDIR : string,
       output_functions : output_functions,
       extra_targets : dep list } ->
      File -> dep list
  exception HolDepFailed

  val forces_update_of : string * string -> bool
  val depforces_update_of : dep * dep -> bool


end
