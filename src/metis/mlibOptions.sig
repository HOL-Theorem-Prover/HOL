(* ========================================================================= *)
(* PROCESSING COMMAND LINE OPTIONS                                           *)
(* Created by Joe Hurd, August 2003                                          *)
(* ========================================================================= *)

signature mlibOptions =
sig

(* One command line option: names, arguments, description and a processor *)
type opt = {switches : string list, arguments : string list,
            description : string, processor : string * string list -> unit}

(* Option processors may raise an Optionexit exception *)
exception Optionexit of {message : string option, usage : bool, success : bool}

(* Wrappers for option processors *)
val int_option : int option * int option -> (string * int -> unit) ->
                 string * string list -> unit
val real_option : real option * real option -> (string * real -> unit) ->
                  string * string list -> unit

(* Basic options useful for all programs *)
val basic_options : opt list

(* All the command line options of a program *)
type allopts = {name : string, version : string, header : string,
                footer : string, options : opt list}

(* Usage information *)
val version_information : allopts -> string
val usage_information   : allopts -> string

(* Process the command line options passed to the program *)
val process_options : allopts -> string list -> string list * string list

end
