
exception NeverHappen of string  (* bad error *)

type mode =
    ModeMosml
  | ModeHol
  | ModeText
  | ModeTex
  | ModeDir
  | ModeNone

val render_mode : mode -> string

type delim =
  | DelimHolTex      (* delimit HOL within TeX *)
  | DelimHolTexMath  (* etc *)
  | DelimHolMosml
  | DelimHolMosmlD
  | DelimText
  | DelimTex
  | DelimDir
  | DelimEOF

type delim_info = { imode : mode; sopen : string; sclose : string }

val delim_info : delim -> delim_info

val make_indent : int -> string

val pretty_pos : Lexing.lexbuf -> string
