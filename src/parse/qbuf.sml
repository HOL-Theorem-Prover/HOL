structure qbuf :> qbuf =
struct

  open base_tokens

  (* qbufs are references to triples:
       field #1   :  the optional lexbuf for a current QUOTE part of the
                     quotation
       field #2   :  the "current token"  (advance recalculates this)
       field #3   :  the frag list that we're consuming.

   Invariants:

   i)     the first element of fld3 is a QUOTE element iff
          the current token is a BT_AQ
   ii)    fld1 (lexbuf) is NONE iff current \in {BT_AQ, BT_EOI}
  *)

  type 'a qbuf = (Lexing.lexbuf option * 'a base_token  * 'a frag list) ref

  fun leading_quotes acc (q as QUOTE s :: t) = leading_quotes (s::acc) t
    | leading_quotes acc t = (String.concat (List.rev acc), t)

  fun buffer_from_tok lbuf tok rest =
      case tok of
        BT_EOI => new_buffer0 rest
      | BT_InComment n => let
          fun consume_aqs (ANTIQUOTE _ :: t) = consume_aqs t
            | consume_aqs x = x
        in
          case consume_aqs rest of
            [] => raise LEX_ERR ("Quotation finishes in "^Int.toString (n + 1)^
                                 " levels of comment")
          | rest' => let
              val (s, rest'') = leading_quotes [] rest'
              val lbuf = Lexing.createLexerString s
            in
              buffer_from_tok lbuf (base_lexer.comment lbuf n) rest''
            end
        end
      | _ => (SOME lbuf, tok, rest)
  and new_buffer0 q =
      case q of
        [] => (NONE, BT_EOI, q)
      | (QUOTE _ :: _) => let
          val (s, rest) = leading_quotes [] q
          val lexbuf = Lexing.createLexerString s
        in
          buffer_from_tok lexbuf (base_lexer.base_token lexbuf) rest
        end
      | ANTIQUOTE x :: rest => (NONE, BT_AQ x, rest)

  fun new_buffer q = ref (new_buffer0 q)

  fun current (ref (_, x, _)) = x

  fun buffer_from_lbuf lb q = buffer_from_tok lb (base_lexer.base_token lb) q

  fun advance (r as ref (lbopt, curr, q)) =
      case curr of
        BT_AQ _ => r := new_buffer0 q
      | BT_EOI => ()
      | _ => r := buffer_from_lbuf (valOf lbopt) q

  fun lex_to_toklist q = let
    val fb = new_buffer q
    fun recurse acc =
        case current fb of
          BT_EOI => List.rev acc
        | t => (advance fb; recurse (t::acc))
  in
    recurse []
  end

  fun replace_current t (r as ref (lb, _, q)) = r := (lb, t, q)

  fun toString (r as ref (lbopt, c, q)) = let
    fun lb_toStringList acc lb = let
      val t = base_lexer.base_token lb
    in
      case t of
        BT_EOI => (acc, true)
      | _ =>  lb_toStringList (base_tokens.toString t::" "::acc) lb
    end handle base_tokens.LEX_ERR s => (acc, false)
    val (buffered, ok) =
        case lbopt of
          SOME lb => lb_toStringList [base_tokens.toString c] lb
        | NONE => ([base_tokens.toString c], true)
    fun q_toString acc [] = acc
      | q_toString acc (QUOTE s :: t) = q_toString (s::acc) t
      | q_toString acc (ANTIQUOTE _ :: t) = q_toString (" <AQ> "::acc) t
  in
    if ok then
      String.concat (List.rev (q_toString buffered q))
    else
      String.concat (List.rev buffered)
  end

end;




