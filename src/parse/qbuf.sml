structure qbuf :> qbuf =
struct

  open base_tokens locn

  (* qbufs are references to quadruples:
       field #1   :  the optional lexbuf for a current QUOTE part of the
                     quotation, along with the extra lexer state
       field #2   :  the "current token" and its location  (advance recalculates this)
       field #3   :  the first fragment number of the remainder frag list
       field #4   :  the frag list that we're consuming.

   Invariants:

   i)     the first element of fld4 is a QUOTE element iff
          the current token is a BT_AQ
   ii)    fld1 (lexbuf) is NONE iff current \in {BT_AQ, BT_EOI}
  *)

  type 'a qbuf = ((Lexing.lexbuf * base_lexer.extrastate) option
               * 'a base_token located
               * int
               * 'a frag list) ref

  fun leading_quotes acc nf (q as QUOTE s :: t) = leading_quotes (s::acc) (nf+1) t
    | leading_quotes acc nf t = (String.concat (List.rev acc), nf, t)

  fun buffer_from_tok (lbuf,st) (tok,locn) nf_rest rest =
      case tok of
        BT_EOI => new_buffer0 nf_rest rest
      | BT_InComment n => let
          fun consume_aqs nf (ANTIQUOTE _ :: t) = consume_aqs nf t
            | consume_aqs nf x = (x,nf)
        in
          case consume_aqs nf_rest rest of
            ([],nf_rest') => raise LEX_ERR ("Quotation finishes in "^Int.toString (n + 1)^
                                            " levels of comment",locp(LocPEnd(nf_rest'-1)))
          | (rest',nf_rest') => let
              val (s, nf_rest'', rest'') = leading_quotes [] nf_rest' rest'
              val lbuf = Lexing.createLexerString s
              val (t,locn) = base_lexer.comment lbuf (base_lexer.newstate nf_rest') n
            in
              buffer_from_tok (lbuf,st) (t,locn) nf_rest'' rest''
            end
        end
      | _ => (SOME (lbuf,st), (tok,locn), nf_rest, rest)
  and new_buffer0 nf q =
      case q of
        [] => (NONE, (BT_EOI,locp(LocPEnd(nf-1))), 0, q)
      | (QUOTE _ :: _) => let
          val (s, nf_rest, rest) = leading_quotes [] nf q
          val lexbuf = Lexing.createLexerString s
          val st = base_lexer.newstate nf
          val (t,locn) = base_lexer.base_token lexbuf st
        in
          buffer_from_tok (lexbuf,st) (t,locn) nf_rest rest
        end
      | ANTIQUOTE x :: rest => (NONE, (BT_AQ x,locfrag nf), nf+1, rest)

  fun new_buffer q = ref (new_buffer0 0 q)

  fun current (ref (_, x, _, _)) = x

  fun buffer_from_lbuf (lb,st) nf_q q = 
      let val (t,locn) = base_lexer.base_token lb st
      in
          buffer_from_tok (lb,st) (t,locn) nf_q q
      end

  fun advance (r as ref (lbopt, (curr,_), nf_q, q)) =
      case curr of
          BT_AQ _ => r := new_buffer0 nf_q q
        | BT_EOI => ()
        | _ => r := buffer_from_lbuf (valOf lbopt) nf_q q

  fun lex_to_toklist q = let
    val fb = new_buffer q
    fun recurse acc =
        case current fb of
          (BT_EOI,_) => List.rev acc
        | t => (advance fb; recurse (t::acc))
  in
    recurse []
  end

  fun replace_current t (r as ref (lb, _, nf_q, q)) = r := (lb, t, nf_q, q)

  fun toString (r as ref (lbopt, (c,_), nf_q, q)) = let
    fun lb_toStringList acc (lb,st) = let
      val (t,locn) = base_lexer.base_token lb st
    in
      case t of
        BT_EOI => (acc, true)
      | _ =>  lb_toStringList (base_tokens.toString t::" "::acc) (lb,st)
    end handle base_tokens.LEX_ERR (s,errlocn) => (acc, false)
    val (buffered, ok) =
        case lbopt of
          SOME (lb,st) => lb_toStringList [base_tokens.toString c] (lb,st)
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




