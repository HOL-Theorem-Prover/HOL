(*---------------------------------------------------------------------------
                Parsing datatype specifications

   The grammar we're parsing is:

       G ::=              id "=" <form>
       form ::=           <phrase> ( "|" <phrase> ) *  |  <record_defn>
       phrase ::=         id  | id "of" <under_constr>
       under_constr ::=   <ptype> ( "=>" <ptype> ) * | <record_defn>
       record_defn ::=    "<|"  <idtype_pairs> "|>"
       idtype_pairs ::=   id ":" <type> | id : <type> ";" <idtype_pairs>
       ptype ::=          <type> | "(" <type> ")"

  It had better be the case that => is not a type infix.  This is true of
  the standard HOL distribution.  In the event that => is an infix, this
  code will still work as long as the input puts the types in parentheses.
 ---------------------------------------------------------------------------*)

structure ParseDatatype :> ParseDatatype =
struct

open Feedback
val ERR = mk_HOL_ERR "ParseDatatype";
val ERRloc = mk_HOL_ERRloc "ParseDatatype";

open Portable Lib;

open ParseDatatype_dtype

fun pretypeToType pty =
  case pty of
    dVartype s => Type.mk_vartype s
  | dTyop {Tyop = s, Thy, Args} => let
    in
      case Thy of
        NONE => Type.mk_type(s, map pretypeToType Args)
      | SOME t => Type.mk_thy_type{Tyop = s, Thy = t,
                                   Args = map pretypeToType Args}
    end
  | dAQ pty => pty

val bads = CharSet.addString(CharSet.empty, "()\"")

fun consume P (qb,s,locn) = let
  open base_tokens
  (* know first char of s is OK wrt P *)
  fun grab i =
      if i = size s then i
      else if P (String.sub(s,i)) then grab (i + 1)
      else i
  val alphapfx_len = grab 1
  val pfx = String.substring(s,0,alphapfx_len)
  val sfx = String.extract(s,alphapfx_len,NONE)
in
  if sfx = "" then ((fn () => qbuf.advance qb), pfx, locn)
  else let
      val (locn',locn'') = locn.split_at (size pfx) locn
    in
      ((fn () => qbuf.replace_current (BT_Ident sfx,locn'') qb), pfx, locn')
    end
end

fun consume_n n (qb,s,locn) =
  let
    open base_tokens
    val pfx = String.substring(s,0,n)
    val sfx = String.extract(s,n,NONE)
  in
    if sfx = "" then ((fn () => qbuf.advance qb), BT_Ident pfx, locn)
    else
      let
        val (locn',locn'') = locn.split_at n locn
      in
        ((fn () => qbuf.replace_current (BT_Ident sfx,locn'') qb),
         BT_Ident pfx, locn')
      end
  end

fun okident c = Char.isAlphaNum c orelse c = #"'" orelse c = #"_"

fun ident_munge dollared qb s locn = let
  val s0 = String.sub(s, 0)
in
  if Char.isAlpha s0 then let
      val (adv, pfx, locn') = consume okident (qb,s,locn)
    in
      if pfx <> "of" orelse dollared then (adv(); pfx)
      else raise ERRloc "ident" locn
                        "Expected an identifier, got (reserved word) \"of\""
    end
  else if s0 = #"$" then
    (* Allow leading dollar signs as quoting mechanism (for "of", but to
       also cope with potential user paranoia over names of infix
       constructors).
       Note that the base_lexer ensures that only one dollar sign is possible
       at the head of a BT_Ident string, and that it is followed by a
       non-empty string *)
    ident_munge true qb (String.extract(s, 1, NONE)) (locn.move_start 1 locn)
  else let
      val s_chars = CharSet.addString(CharSet.empty, s)
      val overlap = CharSet.intersect(bads, s_chars)
    in
      if CharSet.isEmpty overlap then (qbuf.advance qb; s)
      else raise ERRloc "ident" locn
                        (s ^ " not a valid constructor/field/type name")
    end
end

fun ident qb =
    case qbuf.current qb of
      (base_tokens.BT_Ident s,locn) => ident_munge false qb s locn
    | (bt,locn) => raise ERRloc "ident" locn ("Expected an identifier, got "^
                                              base_tokens.toString bt)


fun cmem c s =
  let
    fun recurse i =
      i >= 0 andalso (String.sub(s,i) = c orelse recurse (i - 1))
  in
    recurse (size s - 1)
  end


fun pdtok_of qb = let
  open base_tokens CharSet
  fun advance () = qbuf.advance qb
in
  case qbuf.current qb of
      (t as BT_Ident s,locn) =>
      let
        val c0 = String.sub(s, 0)
      in
        if Char.isAlpha c0 then
          let
            val (adv,idstr,locn') = consume Char.isAlphaNum (qb,s,locn)
          in
            (adv,BT_Ident idstr,locn')
          end
        else if Char.isDigit c0 then
          let
            val (adv,idstr,locn') = consume Char.isDigit (qb,s,locn)
          in
            (adv, BT_Ident idstr, locn')
          end
        else if String.isPrefix "=>" s then consume_n 2 (qb,s,locn)
        else if cmem c0 "()[]" then consume_n 1 (qb,s,locn)
        else if String.isPrefix "<|" s then consume_n 2 (qb,s,locn)
        else if String.isPrefix "|>" s then consume_n 2 (qb,s,locn)
        else
          let
            fun oksym c = Char.isPunct c andalso c <> #"(" andalso c <> #")"
                          andalso c <> #"'"
            val (adv,idstr,locn') = consume oksym (qb,s,locn)
          in
            (adv,BT_Ident idstr,locn')
          end
      end
    | (t,locn) => (advance, t, locn)
end;


fun scan s qb = let
  val (adv, t, locn) = pdtok_of qb
in
  case t of
    base_tokens.BT_Ident s' => if s <> s' then
                                 raise ERRloc "scan" locn
                                           ("Wanted \""^s^"\"; got \""^s'^"\"")
                               else adv()
  | x => raise ERRloc "scan" locn ("Wanted \""^s^"\"; got \""^
                                   base_tokens.toString x^"\"")
end

fun qtyop {Tyop, Thy, Locn, Args} =
    dTyop {Tyop = Tyop, Thy = SOME Thy, Args = Args}
fun tyop ((s,locn), args) = dTyop {Tyop = s, Thy = NONE, Args = args}

fun parse_type G strm =
  parse_type.parse_type
    {vartype = dVartype o #1, tyop = tyop, qtyop = qtyop, antiq = dAQ}
    true
    G
    strm

fun parse_atom G strm =
  parse_type.parse_atom
    {vartype = dVartype o #1, tyop = tyop, qtyop = qtyop, antiq = dAQ}
    true
    G
    strm

val parse_constructor_id = ident

fun parse_record_fld G qb = let
  val fldname = ident qb
  val () = scan ":" qb
in
  (fldname, parse_type G qb)
end

fun sepby1 sepsym p qb = let
  val i1 = p qb
  fun recurse acc =
      case Lib.total (scan sepsym) qb of
        NONE => List.rev acc
      | SOME () => recurse (p qb :: acc)
in
  recurse [i1]
end

fun termsepby1 s term p qb =
  let
    val res1 = p qb
    fun recurse acc =
      case pdtok_of qb of
          (adv, base_tokens.BT_Ident t, locn) =>
            if t = s then (adv(); term_or_continue acc)
            else List.rev acc
        | _ => List.rev acc
    and term_or_continue acc =
      case pdtok_of qb of
          (_, tok, _) => if tok = term then List.rev acc
                         else recurse (p qb :: acc)
  in
    recurse [res1]
  end

fun parse_record_defn G qb = let
  val () = scan "<|" qb
  val result =
      termsepby1 ";" (base_tokens.BT_Ident "|>") (parse_record_fld G) qb
  val () = scan "|>" qb
in
  result
end

fun parse_phrase G qb = let
  val constr_id = parse_constructor_id qb
in
  case pdtok_of qb of
    (_,base_tokens.BT_Ident "of",_) => let
      val _ = qbuf.advance qb
      val optargs = sepby1 "=>" (parse_type G) qb
    in
      (constr_id, optargs)
    end
  | _ => (constr_id, [])
end

fun optscan tok qb =
    case qbuf.current qb of
        (tok',_) => if tok = tok' then (qbuf.advance qb; qb)
                    else qb

fun fragtoString (QUOTE s) = s
  | fragtoString (ANTIQUOTE _) = " ^... "

fun quotetoString [] = ""
  | quotetoString (x::xs) = fragtoString x ^ quotetoString xs

fun parse_harg G qb =
  case qbuf.current qb of
      (base_tokens.BT_Ident s, _) =>
      if String.sub(s,0) = #"(" then
        let
          val (adv,_,_) = pdtok_of qb
          val _ = adv()
        in
          parse_type G qb before scan ")" qb
        end
      else
        (parse_atom G qb
         handle HOL_ERR {origin_structure = "Parse", message, ...} =>
                raise ERR "parse_harg" message)
    | (base_tokens.BT_AQ ty, _) => (qbuf.advance qb; dAQ ty)
    | (_, locn) => raise ERRloc "parse_harg" locn
                         "Unexpected token in constructor's argument"

fun parse_hargs G qb =
  case pdtok_of qb of
      (_, base_tokens.BT_Ident "|", _) => []
    | (_, base_tokens.BT_Ident ";", _) => []
    | (_, base_tokens.BT_EOI, _) => []
    | _ => let
      val arg = parse_harg G qb
      val args = parse_hargs G qb
    in
      arg::args
    end

fun parse_hphrase G qb = let
  val constr_id = parse_constructor_id qb
in
  (constr_id, parse_hargs G qb)
end

fun parse_form G phrase_p qb =
    case pdtok_of qb of
      (_,base_tokens.BT_Ident "<|",_) => Record (parse_record_defn G qb)
    | _ => Constructors (qb |> optscan (base_tokens.BT_Ident "|")
                            |> sepby1 "|" (phrase_p G))

fun extract_tynames q =
  let
    val qb = qbuf.new_buffer q
    fun recurse delims acc =
      case pdtok_of qb of
          (adv,t as base_tokens.BT_Ident ";",loc) =>
            if null delims then (adv(); next_decl acc)
            else (adv(); recurse delims acc)
        | (_,base_tokens.BT_EOI, _) =>
            if null delims then List.rev acc
            else raise ERR "parse_HG"
                       ("looking for delimiter match ("^ hd delims^
                        ") but came to end of input")
        | (adv,t as base_tokens.BT_Ident "(",locn) =>
            (adv(); recurse (")" :: delims) acc)
        | (adv,t as base_tokens.BT_Ident "<|", locn) =>
            (adv(); recurse ("|>" :: delims) acc)
        | (adv,t as base_tokens.BT_Ident "[", locn) =>
            (adv(); recurse ("]" :: delims) acc)
        | (adv, t as base_tokens.BT_Ident s, locn) =>
            (case delims of
                 [] => (adv(); recurse delims acc)
               | d::ds => if d = s then (adv(); recurse ds acc)
                          else (adv(); recurse delims acc))
        | (adv, tok, locn) => (adv(); recurse delims acc)
    and next_decl acc =
        case pdtok_of qb of
            (_, base_tokens.BT_EOI, _) => List.rev acc
          | _ =>
            let
              val tyname = ident qb
              val () = scan "=" qb
            in
              recurse [] (tyname :: acc)
            end
  in
    next_decl []
  end

fun parse_g G phrase_p qb = let
  val tyname = ident qb
  val () = scan "=" qb
in
  (tyname, parse_form G phrase_p qb)
end

fun hide_tynames q G0 =
  List.foldl (uncurry type_grammar.hide_tyop) G0 (extract_tynames q)

val parse_listener : AST list Listener.t = Listener.new_listener ()

fun core_parse G0 phrase_p q = let
  val G = hide_tynames q G0
  val qb = qbuf.new_buffer q
  val result = termsepby1 ";" base_tokens.BT_EOI (parse_g G phrase_p) qb
  val _ = Listener.call_listener parse_listener result
in
  case qbuf.current qb of
      (base_tokens.BT_EOI,_) => result
    | (t,locn) => raise ERRloc "parse" locn
                        ("Parse failed looking at "^base_tokens.toString t)
end

fun parse G0 = core_parse G0 parse_phrase
fun hparse G0 = core_parse G0 parse_hphrase


end
