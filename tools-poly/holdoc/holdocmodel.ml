(* a model for HOLDoc documents *)

type 'a located = 'a * (Lexing.position * Lexing.position)  (* start, end+1 *)

type texdoc = texdoc_content list

and texholdelimmode = TexHolLR | TexHolMath

and texholmode = texholdelimmode * texholdelimmode  (* left mode, right mode *)

and texdoc_content = texdoc_content0 located

and texdoc_content0 =
    TexContent of string
  | TexHol of texholmode * holdoc
  | TexDir of directive

and textdoc = textdoc_content list

and textdoc_content = textdoc_content0 located

and textdoc_content0 =
    TextContent of string
  | TextText of textdoc
  | TextDir of directive

and mosmldoc = mosml_content list

and mosmlholmode = MosmlHolBT | MosmlHolBTBT

and mosml_content = mosml_content0 located

and mosml_content0 =
     MosmlContent of string
   | MosmlWhite of string
   | MosmlStr of string
   | MosmlIndent of int
   | MosmlIdent of bool * string
   | MosmlHol of mosmlholmode * holdoc
   | MosmlText of textdoc
   | MosmlTex of texdoc
   | MosmlDir of directive

and holdoc = hol_content list

and hol_content = hol_content0 located

and hol_content0 =
     HolIdent of bool * string
   | HolStr of string
   | HolWhite of string
   | HolIndent of int
   | HolSep of string
   | HolText of textdoc
   | HolTex of texdoc
   | HolDir of directive

and directive = directive_content

and directive_content = directive_content0 located

and directive_content0 =
     DirThunk of (unit -> unit)       (* do it; not the nicest implementation! *)
   | DirVARS of (bool * string) list  (* VARS directive - special handling *)
   | DirRCSID of string


let zero_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

let rec format_location : (Lexing.position * Lexing.position) -> string
    = fun (l0,l1) ->
      if l0 = Lexing.dummy_pos && l1 = Lexing.dummy_pos then
        ""
      else if l0 = Lexing.dummy_pos then
        format_location (l1,l1)
      else if l1 = Lexing.dummy_pos then
        format_location (l0,l0)
      else begin
        let l0_col = l0.Lexing.pos_cnum - l0.Lexing.pos_bol in
        let l1_col = l1.Lexing.pos_cnum - l1.Lexing.pos_bol in
        if l0.Lexing.pos_fname = l1.Lexing.pos_fname then
        l0.Lexing.pos_fname ^ ":" ^
        begin
          if l0.Lexing.pos_lnum = l1.Lexing.pos_lnum then
            string_of_int l0.Lexing.pos_lnum ^ ":" ^ string_of_int l0_col ^
            begin
              if l0_col = l1_col then
                ":"
              else
                "-" ^ string_of_int l1_col ^ ":"
            end
          else if l1.Lexing.pos_lnum = l0.Lexing.pos_lnum + 1 && l1_col = 0 then  (* to end of line *)
            string_of_int l0.Lexing.pos_lnum ^ ":" ^ string_of_int l0_col ^ "-:"
          else (* lines differ *)
            string_of_int l0.Lexing.pos_lnum ^ ":" ^ string_of_int l0_col ^
            "-" ^ string_of_int l1.Lexing.pos_lnum ^ ":" ^ string_of_int l1_col ^ ":"
        end
      else (* filenames differ *)
        l0.Lexing.pos_fname ^ ":" ^ string_of_int l0.Lexing.pos_lnum ^ ":" ^ string_of_int l0_col ^
        "-" ^ l1.Lexing.pos_fname ^ ":" ^ string_of_int l1.Lexing.pos_lnum ^ ":" ^ string_of_int l1_col ^ ":"
      end

let columns_of : (Lexing.position * Lexing.position) -> (int * int)
    = fun (l0,l1) ->
      (if l0 = Lexing.dummy_pos then
        0
      else
        l0.Lexing.pos_cnum - l0.Lexing.pos_bol),
      (if l1 = Lexing.dummy_pos then
        0
      else
        l1.Lexing.pos_cnum - l1.Lexing.pos_bol)
        
          
