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

  val normPath : string -> string
  val fullPath : string list -> string

  type output_functions = {warn : string -> unit, info : string -> unit,
                           tgtfatal : string -> unit,
                           diag : string -> unit}
  val output_functions : {quiet_flag: bool, debug:bool} -> output_functions

  val do_lastmade_checks: output_functions ->
                          {no_lastmakercheck : bool} ->
                          unit

  val string_part : File -> string
  val toCodeType : string -> CodeType
  val toFile : string -> File
  val codeToString : CodeType -> string
  val fromFile : File -> string
  val file_compare : File * File -> order
  val primary_dependent : File -> File option

  val clean_dir : {extra_cleans: string list} -> unit
  val clean_depdir : {depdirname : string} -> bool

end

