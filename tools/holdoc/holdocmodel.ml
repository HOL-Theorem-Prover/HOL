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

and 'a lines = 'a               (* first line *)
              * (int * 'a) list  (* subsequent lines with indents *)

and mosmldoc = mosml_line lines

and mosml_line = mosml_content list

and mosmlholmode = MosmlHolBT | MosmlHolBTBT

and mosml_content =
     MosmlContent of string
   | MosmlHol of string option * mosmlholmode * holdoc  (* ident preceding delim *)
   | MosmlText of textdoc
   | MosmlTex of texdoc
   | MosmlDir of directive

and holdoc = hol_line lines

and hol_line = hol_content list

and hol_content =
     HolIdent of bool * string
   | HolStr of string
   | HolWhite of string
   | HolSep of string
   | HolText of textdoc
   | HolTex of texdoc
   | HolDir of directive

and directive = directive_content

and directive_content =
     DirThunk of (unit -> unit)       (* do it; not the nicest implementation! *)
   | DirVARS of (bool * string) list  (* VARS directive - special handling *)

