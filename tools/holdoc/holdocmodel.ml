(* a model for HOLDoc documents *)

type texdoc = texdoc_content list

and texholmode = TexHolLR | TexHolMath

and texdoc_content =
    TexContent of string
  | TexHol of texholmode * holdoc
  | TexDir of directive

and textdoc = textdoc_content list

and textdoc_content =
    TextContent of string
  | TextText of textdoc
  | TextDir of directive

and mosmldoc = mosml_content list

and mosmlholmode = MosmlHolBT | MosmlHolBTBT

and mosml_content =
     MosmlContent of string
   | MosmlStr of string
   | MosmlIndent of int
   | MosmlHol of (string * string list) option * mosmlholmode * holdoc  (* ident preceding delim, strings preceding delim  *)
   | MosmlText of textdoc
   | MosmlTex of texdoc
   | MosmlDir of directive

and holdoc = hol_content list

and hol_content =
     HolIdent of bool * string
   | HolStr of string
   | HolWhite of string
   | HolIndent of int
   | HolSep of string
   | HolText of textdoc
   | HolTex of texdoc
   | HolDir of directive

and directive = directive_content

and directive_content =
     DirThunk of (unit -> unit)       (* do it; not the nicest implementation! *)
   | DirVARS of (bool * string) list  (* VARS directive - special handling *)

