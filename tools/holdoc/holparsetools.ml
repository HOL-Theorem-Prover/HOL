(* useful tools for using the parser and lexer *)

open Holparsesupp
open Hollex

exception SyntaxError of string

let parse mode nonterminal lexbuf =
  let lst = token_init mode lexbuf in
  try 
    nonterminal (fun _ ->
                   let t = token lst in
                   (* prerr_string ("«"^render_token t^"» "); *)
                   t) lexbuf  (* ick - hack! *)
  with
    Parsing.Parse_error ->
      raise (SyntaxError ("unexpected token "^Lexing.lexeme lexbuf^" at "^pretty_pos lexbuf))

let parse_chan mode nonterminal chan =
  let lexbuf = Lexing.from_channel chan in
  parse mode nonterminal lexbuf

let move_to_start lexbuf file =
  lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = file;
                                Lexing.pos_lnum = 1;
                                Lexing.pos_bol = 0;
                                Lexing.pos_cnum = 0;
                              }

let from_filelist files =
  let lexbuf_r = ref None in
  let files_r = ref files in
  let chan_r = ref None in
  let rec read buf len =
    let lexbuf = match !lexbuf_r with Some x -> x | None -> raise (Failure "from_filelist") in
    match !chan_r with
      Some chan ->
        let n = input chan buf 0 len in
        if n = 0 then begin
          chan_r := None;
          read buf len
        end else
          n
    | None ->
        match !files_r with
          (file::files) ->
            files_r := files;
            chan_r := Some (open_in file);
            move_to_start lexbuf file;
            read buf len
        | [] ->
            move_to_start lexbuf "<eof>";
            0
  in
  let lexbuf = Lexing.from_function read in
  lexbuf_r := Some lexbuf;
  lexbuf

let parse_fileargs_ext handlers finalhook error mode nonterminal =
  let files = ref [] in
  let handle_file f = files := f :: !files in
  Arg.parse handlers handle_file error;
  finalhook ();
  let lexbuf =
    if !files = [] then
      Lexing.from_channel stdin  (* use stdin if no files listed *)
    else
      from_filelist (List.rev !files)
  in
  parse mode nonterminal lexbuf

let parse_fileargs mode nonterminal =
  parse_fileargs_ext [] (fun () -> ()) "Invalid argument" mode nonterminal
