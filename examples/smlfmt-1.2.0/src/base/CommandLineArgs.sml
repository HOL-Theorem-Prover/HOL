(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure CommandLineArgs:
sig
  (* each takes a key K and a default value D, looks for -K V in the
   * command-line arguments, and returns V if it finds it, or D otherwise. *)
  val parseString: string -> string -> string
  val parseInt: string -> int -> int
  val parseReal: string -> real -> real
  val parseBool: string -> bool -> bool

  (** Look for every instance of -K V and return seq of the Vs.
    * For example, if this is given on the commandline:
    *   -arg a -arg b -arg c -arg d
    * then
    *   parseStrings "arg" ==> ["a", "b", "c", "d"]
    *)
  val parseStrings: string -> string list

  (* parseFlag K returns true if --K given on command-line *)
  val parseFlag: string -> bool

  val positional: unit -> string list
end =
struct

  fun die msg =
    ( TextIO.output (TextIO.stdErr, msg ^ "\n")
    ; TextIO.flushOut TextIO.stdErr
    ; OS.Process.exit OS.Process.failure
    )

  fun positional () =
    let
      fun loop found rest =
        case rest of
          [] => List.rev found
        | [x] =>
            List.rev (if not (String.isPrefix "-" x) then x :: found else found)
        | x :: y :: rest' =>
            if not (String.isPrefix "-" x) then loop (x :: found) (y :: rest')
            else if String.isPrefix "--" x then loop found (y :: rest')
            else loop found rest'
    in
      loop [] (CommandLine.arguments ())
    end

  fun search key args =
    case args of
      [] => NONE
    | x :: args' => if key = x then SOME args' else search key args'

  fun parseString key default =
    case search ("-" ^ key) (CommandLine.arguments ()) of
      NONE => default
    | SOME [] => die ("Missing argument of \"-" ^ key ^ "\" ")
    | SOME (s :: _) => s

  fun parseStrings key =
    let
      fun loop args =
        case search ("-" ^ key) args of
          NONE => []
        | SOME [] => die ("Missing argument of \"-" ^ key ^ "\"")
        | SOME (v :: args') => v :: loop args'
    in
      loop (CommandLine.arguments ())
    end

  fun parseInt key default =
    case search ("-" ^ key) (CommandLine.arguments ()) of
      NONE => default
    | SOME [] => die ("Missing argument of \"-" ^ key ^ "\" ")
    | SOME (s :: _) =>
        case Int.fromString s of
          NONE => die ("Cannot parse integer from \"-" ^ key ^ " " ^ s ^ "\"")
        | SOME x => x

  fun parseReal key default =
    case search ("-" ^ key) (CommandLine.arguments ()) of
      NONE => default
    | SOME [] => die ("Missing argument of \"-" ^ key ^ "\" ")
    | SOME (s :: _) =>
        case Real.fromString s of
          NONE => die ("Cannot parse real from \"-" ^ key ^ " " ^ s ^ "\"")
        | SOME x => x

  fun parseBool key default =
    case search ("-" ^ key) (CommandLine.arguments ()) of
      NONE => default
    | SOME [] => die ("Missing argument of \"-" ^ key ^ "\" ")
    | SOME ("true" :: _) => true
    | SOME ("false" :: _) => false
    | SOME (s :: _) => die ("Cannot parse bool from \"-" ^ key ^ " " ^ s ^ "\"")

  fun parseFlag key =
    case search ("--" ^ key) (CommandLine.arguments ()) of
      NONE => false
    | SOME _ => true

end
