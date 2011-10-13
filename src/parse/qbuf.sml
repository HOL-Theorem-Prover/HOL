structure qbuf :> qbuf =
struct

  open base_tokens locn Portable Lib

(* For SML/NJ *)

 infix ##;

  (* qbufs are references to quadruples:
       field #1   :  the optional lexing function for a current QUOTE part
                     of the quotation
       field #2   :  the "current token" and its location  (advance recalculates this)
       field #3   :  the first fragment number of the remainder frag list
       field #4   :  the frag list that we're consuming.

   Invariants:

   i)     the first element of fld4 is a QUOTE element iff
          the current token is a BT_AQ
   ii)    fld1 (lexbuf) is NONE iff current \in {BT_AQ, BT_EOI}
  *)

  type extrastate = base_lexer.UserDeclarations.extrastate
  type 'a qbuf = ((unit -> 'a base_token located) option *
                  'a base_token located *
                  int *
                  'a frag list) ref

  fun read_from_string s = let
    val state = ref (Substring.full s)
    fun reader n = let
      open Substring
    in
      if n >= size (!state) then string (!state) before state := full ""
      else let
          val (left, right) = splitAt (!state, n)
        in
          state := right;
          string left
        end
    end
  in
    reader
  end

  fun lift_tok (BT_Ident s) = BT_Ident s
    | lift_tok (BT_Numeral p) = BT_Numeral p
    | lift_tok (BT_DecimalFraction r) = BT_DecimalFraction r
    | lift_tok BT_EOI = BT_EOI
    | lift_tok (BT_AQ _) = raise Fail "qbuf: Should never happen"

  fun leading_quotes acc nf (q as QUOTE s :: t) = leading_quotes (s::acc) (nf+1) t
    | leading_quotes acc nf t = (String.concat (List.rev acc), nf, t)

  fun buffer_from_tok lexer (tok,locn) nf_rest rest =
      case tok of
        BT_EOI => new_buffer0 nf_rest rest
      | _ => (SOME lexer, (tok,locn), nf_rest, rest)
  and new_buffer0 nf q =
      case q of
        [] => (NONE, (BT_EOI,locp(LocPEnd(nf-1))), 0, q)
      | (QUOTE _ :: _) => let
          open Lib
          val (s, nf_rest, rest) = leading_quotes [] nf q
          val st = base_lexer.UserDeclarations.newstate nf
          val lexer = (lift_tok ## I) o
                      (base_lexer.makeLexer (read_from_string s) st)
          val (t,locn) = lexer ()
        in
          buffer_from_tok lexer (t,locn) nf_rest rest
        end
      | ANTIQUOTE x :: rest => (NONE, (BT_AQ x,locfrag nf), nf+1, rest)

  fun new_buffer q = ref (new_buffer0 0 q)

  fun current (ref (_, x, _, _)) = x

  fun buffer_from_lbuf lexfn nf_q q =
      let val (t,locn) = lexfn ()
      in
          buffer_from_tok lexfn (t,locn) nf_q q
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
    fun lb_toStringList acc lexfn = let
      val (t,locn) = lexfn ()
    in
      case t of
        BT_EOI => (acc, true)
      | _ =>  lb_toStringList (base_tokens.toString t::" "::acc) lexfn
    end handle base_tokens.LEX_ERR (s,errlocn) => (acc, false)
    val (buffered, ok) =
        case lbopt of
          SOME lexfn => lb_toStringList [base_tokens.toString c] lexfn
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




