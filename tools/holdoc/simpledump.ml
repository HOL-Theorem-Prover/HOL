(* straightforward literal dumper - renders everything to
   the obvious string, except for directives which are
   processed as appropriate and elided. *)

open Holdocmodel
open Holparse
open Holparsesupp
open Hollex


let dolist f cs =
  String.concat "" (List.map f cs)

let rec dumptexdoc cs = dolist dumptexdoc_content cs
    
and dumptexdoc_content = function
    TexContent s -> s
  | TexHol(TexHolLR,d) -> "[[" ^ dumpholdoc d ^ "]]"
  | TexHol(TexHolMath,d) -> "<[" ^ dumpholdoc d ^ "]>"
  | TexDir d -> dumpdirective d

and dumptextdoc cs = dolist dumptextdoc_content cs

and dumptextdoc_content = function
    TextContent s -> s
  | TextText d -> "(*" ^ dumptextdoc d ^ "*)"
  | TextDir d -> dumpdirective d

and dumpmosmldoc cs = dolist dumpmosml_content cs

and dumpmosml_content = function
    MosmlContent s -> s
  | MosmlIndent n -> make_indent n
  | MosmlHol(io,md,d) ->
      let is = (match io with None -> "" | Some i -> i) in
      let bt = (match md with MosmlHolBT -> "`" | MosmlHolBTBT -> "``") in
      is ^ bt ^ dumpholdoc d ^ bt
  | MosmlText d -> "(*" ^ dumptextdoc d ^ "*)"
  | MosmlTex d -> "(*:" ^ dumptexdoc d ^ ":*)"
  | MosmlDir d -> dumpdirective d

and dumpholdoc cs = dolist dumphol_content cs

and dumphol_content = function
    HolIdent(b,s) -> s
  | HolStr s -> "\"" ^ s ^ "\""
  | HolWhite s -> s
  | HolIndent n -> make_indent n
  | HolSep s -> s
  | HolText d -> "(*" ^ dumptextdoc d ^ "*)"
  | HolTex d -> "(*:" ^ dumptexdoc d ^ ":*)"
  | HolDir d -> dumpdirective d

and dumpdirective d = dumpdirective_content d

and dumpdirective_content = function
    DirThunk f -> (f (); "")  (* do it now! (side-effecting) *)
  | DirVARS bis -> ""  (* ignore! *)

