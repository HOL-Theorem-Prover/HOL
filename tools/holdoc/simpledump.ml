(* straightforward literal dumper - renders everything to
   the obvious string, except for directives which are
   processed as appropriate and elided. *)

open Holdocmodel
open Holparse
open Holparsesupp
open Hollex
open Holdoc_init


let dolist f cs =
  String.concat "" (List.map f cs)

let rec dumptexdoc cs = dolist dumptexdoc_content cs
    
and dumptexdoc_content = fun (x,_) ->
  match x with
    TexContent s -> s
  | TexHol((ld,rd),d) -> 
      (match ld with
      | TexHolLR -> "[["
      | TexHolMath -> "<[") ^
      dumpholdoc d ^
      (match rd with
      | TexHolLR -> "]]"
      | TexHolMath -> "]>")
   | TexDir d -> dumpdirective d

and dumptextdoc cs = dolist dumptextdoc_content cs

and dumptextdoc_content = fun (x,_) ->
  match x with
    TextContent s -> s
  | TextText d -> "(*" ^ dumptextdoc d ^ "*)"
  | TextDir d -> dumpdirective d

and dumpmosmldoc cs = dolist dumpmosml_content cs

and dumpmosml_content = fun (x,_) ->
  match x with
    MosmlContent s -> s
  | MosmlWhite s -> s
  | MosmlStr s -> "\"" ^ s ^ "\""
  | MosmlIndent n -> make_indent n
  | MosmlIdent (b,s) -> s
  | MosmlHol(md,d) ->
      let bt = (match md with MosmlHolBT -> "`" | MosmlHolBTBT -> "``") in
      bt ^ dumpholdoc d ^ bt
  | MosmlText d -> "(*" ^ dumptextdoc d ^ "*)"
  | MosmlTex d -> "(*:" ^ dumptexdoc d ^ ":*)"
  | MosmlDir d -> dumpdirective d

and dumpholdoc cs = dolist dumphol_content cs

and dumphol_content = fun (x,_) ->
  match x with
    HolIdent(b,s) -> s
  | HolStr s -> "\"" ^ s ^ "\""
  | HolWhite s -> s
  | HolIndent n -> make_indent n
  | HolSep s -> s
  | HolText d -> "(*" ^ dumptextdoc d ^ "*)"
  | HolTex d -> "(*:" ^ dumptexdoc d ^ ":*)"
  | HolDir d -> dumpdirective d

and dumpdirective d = dumpdirective_content d

and dumpdirective_content = fun (x,_) ->
  (do_directive x; "")  (* do it now! (side-effecting) *)

