(* Token.sml *)

structure Token : TOKEN =
struct

  datatype token
    = Tident of string
    | Tchar of char
    | Tstring of string
    | Taction of Syntax.location
    | Taction1 of int
    | Trule
    | Tparse
    | Tand
    | Tequal
    | Tend
    | Tor
    | Tunderscore
    | Teof
    | Tlbracket
    | Trbracket
    | Tstar
    | Tmaybe
    | Tplus
    | Tlparen
    | Trparen
    | Tcaret
    | Tdash
    | Tlet

end (* structure Token *)
