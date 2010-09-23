(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* Parsing of SMT-LIB 2 benchmarks *)

structure SmtLib_Parser =
struct

  (* Function 'parse_file' parses an SMT-LIB benchmark, returning a
     dictionary with all terms declared in that benchmark. *)

  (* We only parse "declare-fun" commands, we expect each one of these
     to be on a line by itself, and we do not perform assertion stack
     management (cf. push/pop in the SMT-LIB 2 standard).  This whole
     parser is really just a dirty hack. It works for the benchmarks
     currently found in the SMT-LIB repository, but it does not
     implement the SMT-LIB standard in general. *)

local

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Parser"

  fun remove_right_parenthesis (tokens : string list) : string list =
    if List.null tokens then
      raise ERR "remove_right_parenthesis" "empty token list"
    else
      let
        val (front, last) = Lib.front_last tokens
      in
        if last = ")" then
          front
        else
          raise ERR "remove_right_parenthesis" "')' expected"
      end

  (* turns a token list that represents a non-atomic sexpr into a list
     of token lists, each representing a top-level sub-sexpr of the
     original sexpr; also returns any remaining tokens that are not
     part of the non-atomic sexpr *)
  fun unfold_sexpr ("(" :: tokens) : string list list * string list =
    let
      fun aux tokenss _ 0 (")" :: toks) =
          (* terminate the sexpr, also return remaining tokens *)
          (List.rev tokenss, toks)
        | aux tokenss acc 1 (")" :: toks) =
          (* push the sexpr that ends here, continue at level 0 *)
          aux (List.rev (")" :: acc) :: tokenss) [] 0 toks
        | aux tokenss acc n (")" :: toks) =
          (* add ")" to 'acc', continue at level n-1 *)
          aux tokenss (")" :: acc) (n - 1) toks
        | aux tokenss acc n ("(" :: toks) =
          (* add "(" to 'acc', continue at level n+1 *)
          aux tokenss ("(" :: acc) (n + 1) toks
        | aux tokenss _ 0 (tok :: toks) =
          (* push the atomic sexpr 'tok', continue at level 0 *)
          aux ([tok] :: tokenss) [] 0 toks
        | aux tokenss acc n (tok :: toks) =
          (* add 'tok' to 'acc', continue at level n *)
          aux tokenss (tok :: acc) n toks
        | aux _ _ _ _ =
          raise ERR "unfold_sexpr" "invalid token sequence (in function aux)"
    in
      aux [] [] 0 tokens
    end
    | unfold_sexpr _ =
    raise ERR "unfold_sexpr" "invalid token sequence"

  (***************************************************************************)
  (* parsing of types                                                        *)
  (***************************************************************************)

  fun parse_typ ["Bool"] : Type.hol_type =
    Type.bool
    | parse_typ ["Int"] =
    intSyntax.int_ty
    | parse_typ [token] =
    (* some uninterpreted type; this works only because all sorts in
       all current SMT-LIB benchmarks are declared with arity 0 *)
    Type.mk_vartype ("'" ^ token)
    | parse_typ tokens =
    let
      val (tokenss, rest) = unfold_sexpr tokens
      val _ = if List.null rest then ()
        else
          raise ERR "parse_typ" "non-empty rest"
    in
      case tokenss of
        [["Array"], dom, rng] =>
          (* arrays are translated as functions *)
          Type.--> (parse_typ dom, parse_typ rng)
      | [["_"], ["BitVec"], [n]] =>
          wordsSyntax.mk_word_type (fcpLib.index_type (Arbnum.fromString n))
      | _ =>
          raise ERR "parse_typ" "invalid token sequence"
    end

  (***************************************************************************)
  (* parsing of "declare-fun" lines                                          *)
  (***************************************************************************)

  (* parses a single line of the SMT-LIB file, split into a list of
     tokens already; returns an extended dictionary *)
  fun parse_token_line dict ("(" :: "declare-fun" :: name :: tokens) =
    let
      val tokens = remove_right_parenthesis tokens
      val _ = case Redblackmap.peek (dict, name) of
        NONE => ()
      | SOME _ =>
        raise ERR "parse_token_line"
          ("function '" ^ name ^ "' defined more than once")
      val (doms, rng) = unfold_sexpr tokens
      val typ = boolSyntax.list_mk_fun (List.map parse_typ doms, parse_typ rng)
    in
      Redblackmap.insert (dict, name, Term.mk_var (name, typ))
    end
    | parse_token_line dict _ =
    (* we completely ignore everything else *)
    dict

  (***************************************************************************)
  (* tokenization                                                            *)
  (***************************************************************************)

  (* tokens are simply strings; we use no markup *)

  fun token_if_not_null ([] : char list) (tokens : string list) : string list =
        tokens
    | token_if_not_null cs tokens =
        String.implode (List.rev cs) :: tokens

  fun tokenize (tokens : string list) (acc : char list) ([] : char list)
    : string list =
        List.rev (token_if_not_null acc tokens)
    | tokenize tokens acc (#"\r" :: cs) =
        tokenize (token_if_not_null acc tokens) [] cs
    | tokenize tokens acc (#"\n" :: cs) =
        tokenize (token_if_not_null acc tokens) [] cs
    | tokenize tokens acc (#" " :: cs) =
        tokenize (token_if_not_null acc tokens) [] cs
    | tokenize tokens acc (#"(" :: cs) =
        tokenize ("(" :: token_if_not_null acc tokens) [] cs
    | tokenize tokens acc (#")" :: cs) =
        tokenize (")" :: token_if_not_null acc tokens) [] cs
    | tokenize tokens acc (c :: cs) =
        tokenize tokens (c :: acc) cs

in

  fun parse_file (path : string) : (string, Term.term) Redblackmap.dict =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG ("HolSmtLib: parsing SMT-LIB file '" ^ path ^ "'")
      else ()
    val instream = TextIO.openIn path
    fun parse_lines dict : (string, Term.term) Redblackmap.dict =
      if TextIO.endOfStream instream then
        dict
      else
        let
          val line = Option.valOf (TextIO.inputLine instream)
            handle Option.Option =>
              raise ERR "parse_file" "unexpected end of file"
          val dict = if String.isPrefix "(declare-fun" line then
              let
                val tokens = tokenize [] [] (String.explode line)
                val _ = if !SolverSpec.trace > 2 then
                    Feedback.HOL_MESG ("HolSmtLib: parsing SMT-LIB token(s) " ^
                      String.concatWith ", " tokens)
                  else ()
              in
                parse_token_line dict tokens
              end
            else
              dict
        in
          parse_lines dict
        end
    val dict = parse_lines (Redblackmap.mkDict String.compare)
    val _ = TextIO.closeIn instream
  in
    dict
  end

end  (* local *)

end
