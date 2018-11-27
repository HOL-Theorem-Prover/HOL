structure term_tokens :> term_tokens =
struct

  open Portable qbuf base_tokens locn

  val WARN = Feedback.HOL_WARNING "term lexer" ""

  datatype 'a term_token =
    Ident of string
  | Antiquote of 'a
  | Numeral of (Arbnum.num * char option)
  | Fraction of {wholepart : Arbnum.num, fracpart : Arbnum.num,
                 places : int}
  | QIdent of (string * string)


val c0 = Char.ord #"0"
val c9 = Char.ord #"9"
val ca = Char.ord #"a"
val cf = Char.ord #"f"
val cA = Char.ord #"A"
val cF = Char.ord #"F"
val c' = Char.ord #"'"
val c_ = Char.ord #"_"
val clambda = 0x3BB (* lower case lambda *)

fun repc i c = CharVector.tabulate(i, fn _ => c)

val non_aggregating_chars =
    foldl (fn (c, cs) => HOLset.add(cs,c))
          (HOLset.empty Int.compare)
          (UTF8.explodei "()[]{}~.,;-¬") (* UOK *)
fun cpt_is_nonagg_char i = HOLset.member(non_aggregating_chars, i)
val cpts_have_nonagg_char = List.exists cpt_is_nonagg_char

fun isIdent_i i = UnicodeChars.isMLIdent_i i andalso i <> clambda

val sup_codepoints =
    let open UnicodeChars UTF8
    in
      map (#2 o valOf o firstChar)
          [sup_0, sup_1, sup_2, sup_3, sup_4, sup_5, sup_6, sup_7, sup_8, sup_9]
    end
fun unpc_encode s =
    let
      val sz = String.size s
    in
      if sz <= 3 then s
      else
        let
          open Lib
          val cpoints = List.rev (UTF8.explodei s)
          fun recurse A base uni seendigit lastzerop inp =
              case inp of
                  [] => NONE
                | [_] => NONE
                | cp::rest =>
                  case (uni,seendigit) of
                      (_, false) =>
                        if c0 <= cp andalso cp <= c9 then
                          recurse ((cp-c0)*base + A) (base * 10) false true
                                  (cp = c0) rest
                        else if mem cp sup_codepoints then
                          recurse (index (equal cp) sup_codepoints * base + A)
                                  (base * 10) true true false rest
                        else NONE
                    | (true, true) =>
                        if mem cp sup_codepoints then
                          recurse (index (equal cp) sup_codepoints * base + A)
                                  (base * 10) true true false rest
                        else if cp = Char.ord #"'" then SOME(A,rest)
                        else NONE
                    | (false,true) =>
                        if c0 <= cp andalso cp <= c9 then
                          recurse ((cp-c0)*base + A) (base * 10) false true
                                  (cp = c0) rest
                        else if cp = Char.ord #"'" andalso not lastzerop then
                          SOME(A,rest)
                        else NONE
        in
          if hd cpoints = Char.ord #"'" then
            case recurse 0 1 false false false (tl cpoints) of
                NONE => s
              | SOME (i, rest) =>
                String.concat (List.rev (repc i #"'" :: map UTF8.chr rest))
          else s
        end
    end

(* lexer guarantees:

     All Idents fit into one of the following categories :

     * a double-quote delimited string
     * a character literal, consisting of four characters, # " <anything> "
     * an alpha-numeric identifier (first character will be one
       of _ ' A-Z a-z), possibly preceded by a dollar sign
     * a symbolic identifier = a chain of symbol characters (again possibly
       preceded by a dollar sign).

     A symbol is any  printable ASCII character EXCEPT
       A-Z a-z 0-9 $ "
     " is used exclusively for strings, and $ is used for
     token 'quoting' as well as being the separator for qualified identifiers.
*)

val str_all = CharVector.all

open qbuf

fun digit_term A cpts =
    case cpts of
        [] => (Numeral(A,NONE), [])
      | d::rest => if d < 128 andalso Char.isAlpha (Char.chr d) then
                     (Numeral(A,SOME (Char.chr d)), rest)
                   else (Numeral(A,NONE), d::rest)
fun maybefrac backup cpts (* have seen decimal point *) =
    case cpts of
        [] => backup
      | 95 (* _ *) :: rest => maybefrac backup rest
      | d :: rest =>
        if c0 <= d andalso d <= c9 then
          let
            fun add A i = let open Arbnum in fromInt 10 * A + fromInt i end
            val (w,fr,p) =
                case backup of
                    (Fraction{wholepart=w,fracpart=f,places=p},_) => (w,f,p)
                  | (Numeral(n, _),_) => (n,Arbnum.zero,0)
                  | _ => raise Fail "term_tokens.maybefrac invariant failure"
            val b' = Fraction{wholepart=w, places=p+1, fracpart=add fr (d-c0)}
          in
            maybefrac (b',rest) rest
          end
        else backup
fun digits locn b A cpts =
    let
      fun add A i = let open Arbnum in fromInt b * A + fromInt i end
      val digs = digits (locn.move_start 1 locn) b
    in
      case cpts of
          [] => (Numeral(A,NONE), [])
        | 46 (* . *) :: rest => if b = 10 then
                                  maybefrac (Numeral(A,NONE),cpts) rest
                                else (Numeral(A,NONE), cpts)
        | 95 (* _ *) :: rest => digs A rest
        | d :: rest =>
          if c0 <= d andalso d <= c9 then
            if d - c0 >= b then
              raise LEX_ERR ("Illegal digit for base-" ^ Int.toString b ^
                             " number", locn)
            else digs (add A (d - c0)) rest
          else if b = 16 then
            if ca <= d andalso d <= cf then
              digs (add A (10 + d - ca)) rest
            else if cA <= d andalso d <= cF then
              digs (add A (10 + d - cA)) rest
            else digit_term A cpts
          else digit_term A cpts
    end

fun digits_afterbasespec locn b cpts =
    let
      val vdone =
          case b of 2 => Numeral(Arbnum.zero, SOME #"b")
                  | 16 => Numeral(Arbnum.zero, SOME #"x")
                  | i => raise Fail "digits_afterbasespec: impossible"
      val done = (vdone, cpts)
    in
      case cpts of
          [] => done
        | d :: rest => if c0 <= d andalso d <= c9 then
                         digits locn b Arbnum.zero cpts
                       else done
    end
fun digit1_was0 locn octalok cpts =
    case cpts of
        [] => (Numeral(Arbnum.zero, NONE), [])
      | 98 (* b *) :: rest => digits_afterbasespec locn 2 rest
      | 120 (* x *) :: rest => digits_afterbasespec locn 16 rest
      | d :: rest => if c0 <= d andalso d <= c9 then
                       if octalok then digits locn 8 Arbnum.zero cpts
                       else digits locn 10 Arbnum.zero cpts
                     else digit_term Arbnum.zero cpts
fun numeralthing locn octalok cpts = (* head is a digit *)
    case cpts of
        48 (* 0 *) :: rest => digit1_was0 locn octalok rest
      | _ => digits locn 10 Arbnum.zero cpts

fun A_to_string A = String.concat (map UTF8.chr (List.rev A))

fun DEBUG s cpts = print (s ^ ": " ^
                          (case cpts of [] => "[]"
                                      | h :: _ => Int.fmt StringCvt.HEX h) ^
                          "\n")
fun alphaIdentSupDigits locn (A0,rest0) (acc as (A,pc)) cpts =
    case cpts of
        [] => ((A_to_string A0, 0), rest0)
      | 39 (* ' *) :: rest => ((A_to_string A,pc), rest)
      | cp :: rest =>
        case UnicodeChars.supDigitVal_i cp of
            NONE => ((A_to_string A0, 0), rest0)
          | SOME i =>
              alphaIdentSupDigits locn (A0,rest0) (A,pc*10 + i) rest

and alphaIdentPrimeDigits locn A0 (acc as (A,pc)) cpts =
    case cpts of
        [] => ((A_to_string A0,0), cpts)
      | 39 (* ' *) :: rest => alphaIdentFinishedDigits locn (39::A0) acc rest
      | cp :: rest =>
        if c0 <= cp andalso cp <= c9 then
          alphaIdentPrimeDigits locn (cp::A0) (A,pc*10 + (cp - c0)) rest
        else alphaIdent locn A0 rest

and alphaIdentFinishedDigits locn A0 (A,pc) cpts =
    (* head of A0 is a prime *)
    case cpts of
        [] => ((A_to_string A, pc), cpts)
      | 39 (* ' *) :: rest => alphaIdent' locn A0 (tl A0,2) rest
      | cp :: rest =>
        if isIdent_i cp then
          alphaIdent locn (cp::A0) rest
        else if UnicodeChars.isSupDigit_i cp then
          alphaIdentSupDigits locn (A0,cpts) (A0,0) cpts
        else if c0 <= cp andalso cp <= c9 then
          alphaIdentPrimeDigits locn A0 (A0,0) cpts
        else ((A_to_string A, pc), cpts)

and alphaIdent' locn A0 (acc as (A,pc)) cpts =
    (* last character seen was a prime/apostrophe, pc is number seen in a row
       and will thus be >= 1 *)
    case cpts of
        [] => ((A_to_string A, pc), cpts)
      | 39 (* ' *) :: rest =>
          alphaIdent' locn (39::A0) (A,pc+1) rest
      | cp :: rest =>
        if UnicodeChars.isSupDigit_i cp then
          alphaIdentSupDigits locn (A0,cpts) (A,0) cpts
        else if c0 <= cp andalso cp <= c9 then
          alphaIdentPrimeDigits locn A0 (A,0) cpts
        else if isIdent_i cp then alphaIdent locn (cp::A0) rest
        else
          ((A_to_string A, pc), cpts)

and alphaIdent locn A cpts =
    (* have consumed 1+ alphabetic thing (in A) *)
    case cpts of
        [] => ((A_to_string A,0), [])
      | 39 (* ' *) :: rest => alphaIdent' locn (39::A) (A,1) rest
      | cp :: rest => if isIdent_i cp then alphaIdent locn (cp::A) rest
                      else ((A_to_string A,0), cpts)


fun holsymbol c =
    UnicodeChars.isSymbolic_i c andalso c <> 36 (* $ *) andalso c <> 39 (* ' *)
    andalso not (cpt_is_nonagg_char c) andalso c <> 95 (* _ *)
    andalso c <> 34 (* " *) orelse c = clambda
fun symbolIdent locn A cpts = (* have consumed 1+ symbolic thing (in A) *)
    case cpts of
        [] => (A_to_string A, [])
      | 36 (* $ *) :: _ => raise LEX_ERR("Illegal dollar character", locn)
      | cp :: rest => if holsymbol cp then symbolIdent locn (cp::A) rest
                      else (A_to_string A, cpts)

fun constsymbol i = Lexis.in_class(Lexis.hol_symbols, i)
fun constSymIdent locn A cpts = (* have consumed 1+ symbolic thing (in A) *)
    case cpts of
        [] => (A_to_string A, [])
      | 36 (* $ *) :: _ => raise LEX_ERR("Illegal dollar character", locn)
      | cp :: rest => if constsymbol cp then constSymIdent locn (cp::A) rest
                      else (A_to_string A, cpts)

fun constAlpha i = Lexis.in_class(Lexis.alphabet, i)
fun constAlphaIdent locn A cpts =
    case cpts of
        [] => (A_to_string A, [])
      | 36 (* $ *) :: _ => raise LEX_ERR("Illegal dollar character", locn)
      | cp :: rest => if Lexis.in_class(Lexis.alphanumerics, cp) then
                        constAlphaIdent locn (cp::A) rest
                      else (A_to_string A, cpts)

fun quotes nqs locn cpts =
    case cpts of
        [] => (Ident (repc nqs #"'"), [])
      | 39 (* ' *) :: rest => quotes (nqs+1) locn rest
      | cp :: rest =>
          if UnicodeChars.isAlpha_i cp then
            raise LEX_ERR ("Term idents can't begin with prime characters",
                           locn)
          else
            (Ident (repc nqs #"'"), cpts)

fun dollars locn c cpts =
    case cpts of
        [] => (Ident(CharVector.tabulate(c, fn _ => #"$")), [])
      | 36 (* $ *) :: rest => dollars locn (c + 1) rest
      | _ => raise LEX_ERR ("Bad token: " ^
                            CharVector.tabulate(c, fn _ => #"$") ^
                            String.concat (map UTF8.chr cpts), locn)

fun qvar_interior locn A cpts =
    case cpts of
        [] => raise LEX_ERR ("Unterminated quoted variable", locn)
      | 41 (* ) *) :: rest => (Ident (A_to_string A), rest)
      | 92 (* \ *) :: rest => qvar_interior_bslash locn A rest
      | cpt :: rest => qvar_interior locn (cpt::A) rest
and qvar_interior_bslash locn A cpts =
    case cpts of
        [] => raise LEX_ERR ("Trailing backslash at end of quoted variable",
                             locn)
      | 41 (* ) *) :: rest => qvar_interior locn (41 :: A) rest
      | 92 (* \ *) :: rest => qvar_interior locn (92 :: A) rest
      | 110 (* n *) :: rest => qvar_interior locn (10 (* NL *) :: A) rest
      | 116 (* t *) :: rest => qvar_interior locn (9 (* TAB *) :: A) rest
      | c :: rest => raise LEX_ERR ("Bad backslash applied to " ^ UTF8.chr c,
                                    locn)

val badqid_str = "Malformed qualified identifier"
fun qualified_part2 locn cpts =
    case cpts of
        [] => raise LEX_ERR("Illegal trailing $ (" ^ badqid_str ^ "?)", locn)
      | 36 (* $ *) :: _ => raise LEX_ERR(badqid_str, locn)
      | 39 (* ' *) :: _ => raise LEX_ERR(badqid_str, locn)
      | 48 (* 0 *) :: rest =>
        (case rest of
            [] => ("0", [])
          | 36 (* $ *) :: _ => raise LEX_ERR(badqid_str, locn)
          | 39 (* ' *) :: _ => raise LEX_ERR(badqid_str, locn)
          | cp2 :: _ =>
              if UnicodeChars.isSymbolic_i cp2 then ("0", rest)
              else
                raise LEX_ERR("Illegal constant name in qualified identifier",
                              locn)
        )
      | cp::rest =>
        if constsymbol cp then constSymIdent locn [cp] rest
        else if constAlpha cp then constAlphaIdent locn [cp] rest
        else raise LEX_ERR ("Illegal 2nd part to qualified identifier", locn)

(* various possibilities have already been filtered out. In particular, need
   not worry about string and character literals, nor quoted-variables (the
   $var$(...) syntax)
*)
fun toplevel_split locn octalok cpts =
    case cpts of
        [] => raise LEX_ERR("Empty string to split!?", locn)
      | 36 (* $ *) :: rest => raise Fail "toplevel_split: unexpected $"
      | 39 (* ' *) :: rest => quotes 1 locn rest
      | c :: rest =>
        if c0 <= c andalso c <= c9 then numeralthing locn octalok cpts
        else if UnicodeChars.isAlpha_i c andalso c <> clambda orelse c = c_ then
          let val ((ident_s,pc), rest) = alphaIdent locn [c] rest
              val id = ident_s ^ repc pc #"'"
          in
            case rest of
                [] => (Ident id, [])
              | 36 (* $ *) :: rest =>
                  apfst (fn s => QIdent(id,s)) (qualified_part2 locn rest)
              | _ => (Ident id, rest)
          end
        else if holsymbol c then apfst Ident (symbolIdent locn [c] rest)
        else raise LEX_ERR("Uncategorisable code-point: " ^ UTF8.chr c, locn)

fun split_ident mixedset octalok s locn qb = let
  val {advance,replace_current} = qb
  fun pushstring (s,loc) = replace_current (BT_Ident s, loc)
  val s0 = String.sub(s, 0)
  val is_char = s0 = #"#" andalso size s > 1 andalso String.sub(s,1) = #"\""
  val cpts = UTF8.explodei s
  val (cp0, cpts0) =
      case cpts of [] => raise Fail "split_ident: invariant failure"
                 | h::t => (h,t)
  fun i2s is = String.concat (map UTF8.chr is)
  fun stdfinish (tok, sfx) =
      let
        val sz = UTF8.size sfx
      in
        if 0 < sz then
          let
            val (locn1,locn2) = locn.split_at (length cpts - UTF8.size sfx) locn
          in
            pushstring (sfx, locn2);
            (tok, locn1)
          end
        else (advance(); (tok, locn))
      end
in
  if is_char orelse s0 = #"\"" then (advance(); (Ident s, locn))
  else if cp0 = 36 (* $ *) then
    if List.all (Lib.equal 36) cpts then (advance(); (Ident s, locn))
    else if size s > 1 andalso String.sub(s,1) = #"$" then
      raise LEX_ERR ("Bad token "^s, locn)
    else if String.isPrefix "$var$(" s then
      stdfinish (apsnd i2s (qvar_interior locn [] (List.drop(cpts, 6))))
    else
      let
        val (tok,locn') = split_ident mixedset octalok
                                      (String.extract(s, 1, NONE))
                                      (locn.move_start 1 locn) qb
      in
        case tok of
            Ident s' => (Ident ("$" ^ s'), locn.move_start ~1 locn')
          | _ => raise LEX_ERR
                       ("Can't use $-quoting of this sort of token", locn')
      end
  else
    case Exn.capture (toplevel_split locn octalok) cpts of
        Exn.Res (i, []) => (advance(); (i, locn))
      | r => (
          case UTF8Set.longest_pfx_member(mixedset, s) of
              NONE =>
              (* identifier blob doesn't occur in list of known keywords *)
              if cpt_is_nonagg_char cp0 then
                stdfinish (Ident (UTF8.chr cp0), i2s cpts0)
              else
                stdfinish (apsnd i2s (Exn.release r))
            | SOME {pfx,rest} =>
                if size rest = 0 then (advance(); (Ident s, locn))
                else
                  stdfinish(Ident pfx, rest)
      )
end

fun mixed ilist =
    case ilist of
        [] => false
      | cp::rest =>
        let
          val P =
              if UnicodeChars.isDigit_i cp then UnicodeChars.isDigit_i
              else if UnicodeChars.isAlpha_i cp then UnicodeChars.isMLIdent_i
              else holsymbol
        in
          List.exists (not o P) rest
        end

fun lex keywords = let
  val kwd_is = map (fn s => (s, UTF8.explodei s)) keywords
  fun test (s, is) = mixed is orelse cpts_have_nonagg_char is
  val mixedkws = List.filter test kwd_is
  val mixedset = UTF8Set.addList(UTF8Set.empty, map #1 mixedkws)
  val split = split_ident mixedset (!base_tokens.allow_octal_input)
in
fn qb => let
   val (bt,locn) = current qb
   in
     case bt of
         BT_Numeral p         => (advance qb; SOME (Numeral p,locn))
       | BT_DecimalFraction r => (advance qb; SOME (Fraction r, locn))
       | BT_AQ x              => (advance qb; SOME (Antiquote x,locn))
       | BT_EOI               => NONE
       | BT_Ident s           => let
           val qbfns = {advance = (fn () => advance qb),
                        replace_current = (fn p => replace_current p qb)}
           val (tok,locn') = split s locn qbfns
         in
           SOME (tok,locn')
         end
   end
end

fun user_split_ident keywords = let
  val kwd_is = map (fn s => (s, UTF8.explodei s)) keywords
  fun test (s, is) = mixed is orelse cpts_have_nonagg_char is
  val mixedkws = List.filter test kwd_is
  val mixedset = UTF8Set.addList(UTF8Set.empty, map #1 mixedkws)
  val split = split_ident mixedset (!base_tokens.allow_octal_input)
in
  fn s => let
       val pushback = ref ""
       fun rc (btid, _) =
           case btid of
             BT_Ident s => (pushback := s)
           | _ => () (* shouldn't happen *)
       val _ = split s locn.Loc_None {advance=fn()=>(), replace_current=rc}
     in
       (String.substring(s,0,size s - size (!pushback)),
        !pushback)
     end
end

fun token_string (Ident s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (Antiquote x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote token"

fun is_ident (Ident _) = true
  | is_ident _ = false
fun is_aq (Antiquote _) = true
  | is_aq _ = false

fun lextest toks s = let
  val qb = qbuf.new_buffer [QUOTE s]
  fun recurse acc =
      case lex toks qb of
        NONE => List.rev acc
      | SOME (t,_) => recurse (t::acc)
in
  recurse []
end

fun toString aqp t =
    case t of
        Ident s => "Ident(\""^String.toString s^"\")"
      | Antiquote a => "AQ(" ^ aqp a ^ ")"
      | Numeral(n,copt) => "Numeral(" ^ Arbnum.toString n ^ ", " ^
                           (case copt of NONE => "NONE"
                                       | SOME c => str c) ^ ")"
      | Fraction{wholepart,fracpart,places} =>
          "Fraction{w=" ^ Arbnum.toString wholepart ^", f=" ^
          Arbnum.toString fracpart ^ ", p=" ^ Int.toString places ^ "}"
      | QIdent(s1,s2) => s1 ^ "$" ^ s2

end (* struct *)

(* good parsing/lexing test:

val q as [QUOTE s] =
    `~((~v5 \/ ~v0 \/ v0) /\ (~v5 \/ ~v2 \/ v2) /\ (~v5 \/ ~v31 \/ v31) /\
       (~v5 \/ ~v5 \/ v5) /\ (~v13 \/ ~v0 \/ v7) /\ (~v13 \/ ~v2 \/ v9) /\
       (~v13 \/ ~v31 \/ v11) /\ (~v13 \/ ~v5 \/ v13) /\ (~v20 \/ ~v0 \/ v15) /\
       (~v20 \/ ~v2 \/ v16) /\ (~v20 \/ ~v31 \/ v18) /\ (~v20 \/ ~v5 \/ v20) /\
       (~v28 \/ ~v0 \/ v22) /\ (~v28 \/ ~v2 \/ v24) /\ (~v28 \/ ~v31 \/ v26) /\
       (~v28 \/ ~v5 \/ v28) /\ (~v31 \/ ~v7 \/ v0) /\ (~v31 \/ ~v9 \/ v2) /\
       (~v31 \/ ~v11 \/ v31) /\ (~v31 \/ ~v13 \/ v5) /\ (~v11 \/ ~v7 \/ v7) /\
       (~v11 \/ ~v9 \/ v9) /\ (~v11 \/ ~v11 \/ v11) /\ (~v11 \/ ~v13 \/ v13) /\
       (~v18 \/ ~v7 \/ v15) /\ (~v18 \/ ~v9 \/ v16) /\ (~v18 \/ ~v11 \/ v18) /\
       (~v18 \/ ~v13 \/ v20) /\ (~v26 \/ ~v7 \/ v22) /\ (~v26 \/ ~v9 \/ v24) /\
       (~v26 \/ ~v11 \/ v26) /\ (~v26 \/ ~v13 \/ v28) /\ (~v2 \/ ~v15 \/ v0) /\
       (~v2 \/ ~v16 \/ v2) /\ (~v2 \/ ~v18 \/ v31) /\ (~v2 \/ ~v20 \/ v5) /\
       (~v9 \/ ~v15 \/ v7) /\ (~v9 \/ ~v16 \/ v9) /\ (~v9 \/ ~v18 \/ v11) /\
       (~v9 \/ ~v20 \/ v13) /\ (~v16 \/ ~v15 \/ v15) /\
       (~v16 \/ ~v16 \/ v16) /\ (~v16 \/ ~v18 \/ v18) /\
       (~v16 \/ ~v20 \/ v20) /\ (~v24 \/ ~v15 \/ v22) /\
       (~v24 \/ ~v16 \/ v24) /\ (~v24 \/ ~v18 \/ v26) /\
       (~v24 \/ ~v20 \/ v28) /\ (~v0 \/ ~v22 \/ v0) /\ (~v0 \/ ~v24 \/ v2) /\
       (~v0 \/ ~v26 \/ v31) /\ (~v0 \/ ~v28 \/ v5) /\ (~v7 \/ ~v22 \/ v7) /\
       (~v7 \/ ~v24 \/ v9) /\ (~v7 \/ ~v26 \/ v11) /\ (~v7 \/ ~v28 \/ v13) /\
       (~v15 \/ ~v22 \/ v15) /\ (~v15 \/ ~v24 \/ v16) /\
       (~v15 \/ ~v26 \/ v18) /\ (~v15 \/ ~v28 \/ v20) /\
       (~v22 \/ ~v22 \/ v22) /\ (~v22 \/ ~v24 \/ v24) /\
       (~v22 \/ ~v26 \/ v26) /\ (~v22 \/ ~v28 \/ v28) /\ (~v6 \/ ~v1 \/ v1) /\
       (~v6 \/ ~v3 \/ v3) /\ (~v6 \/ ~v4 \/ v4) /\ (~v6 \/ ~v6 \/ v6) /\
       (~v14 \/ ~v1 \/ v8) /\ (~v14 \/ ~v3 \/ v10) /\ (~v14 \/ ~v4 \/ v12) /\
       (~v14 \/ ~v6 \/ v14) /\ (~v21 \/ ~v1 \/ v30) /\ (~v21 \/ ~v3 \/ v17) /\
       (~v21 \/ ~v4 \/ v19) /\ (~v21 \/ ~v6 \/ v21) /\ (~v29 \/ ~v1 \/ v23) /\
       (~v29 \/ ~v3 \/ v25) /\ (~v29 \/ ~v4 \/ v27) /\ (~v29 \/ ~v6 \/ v29) /\
       (~v4 \/ ~v8 \/ v1) /\ (~v4 \/ ~v10 \/ v3) /\ (~v4 \/ ~v12 \/ v4) /\
       (~v4 \/ ~v14 \/ v6) /\ (~v12 \/ ~v8 \/ v8) /\ (~v12 \/ ~v10 \/ v10) /\
       (~v12 \/ ~v12 \/ v12) /\ (~v12 \/ ~v14 \/ v14) /\
       (~v19 \/ ~v8 \/ v30) /\ (~v19 \/ ~v10 \/ v17) /\
       (~v19 \/ ~v12 \/ v19) /\ (~v19 \/ ~v14 \/ v21) /\
       (~v27 \/ ~v8 \/ v23) /\ (~v27 \/ ~v10 \/ v25) /\
       (~v27 \/ ~v12 \/ v27) /\ (~v27 \/ ~v14 \/ v29) /\ (~v3 \/ ~v30 \/ v1) /\
       (~v3 \/ ~v17 \/ v3) /\ (~v3 \/ ~v19 \/ v4) /\ (~v3 \/ ~v21 \/ v6) /\
       (~v10 \/ ~v30 \/ v8) /\ (~v10 \/ ~v17 \/ v10) /\
       (~v10 \/ ~v19 \/ v12) /\ (~v10 \/ ~v21 \/ v14) /\
       (~v17 \/ ~v30 \/ v30) /\ (~v17 \/ ~v17 \/ v17) /\
       (~v17 \/ ~v19 \/ v19) /\ (~v17 \/ ~v21 \/ v21) /\
       (~v25 \/ ~v30 \/ v23) /\ (~v25 \/ ~v17 \/ v25) /\
       (~v25 \/ ~v19 \/ v27) /\ (~v25 \/ ~v21 \/ v29) /\ (~v1 \/ ~v23 \/ v1) /\
       (~v1 \/ ~v25 \/ v3) /\ (~v1 \/ ~v27 \/ v4) /\ (~v1 \/ ~v29 \/ v6) /\
       (~v8 \/ ~v23 \/ v8) /\ (~v8 \/ ~v25 \/ v10) /\ (~v8 \/ ~v27 \/ v12) /\
       (~v8 \/ ~v29 \/ v14) /\ (~v30 \/ ~v23 \/ v30) /\
       (~v30 \/ ~v25 \/ v17) /\ (~v30 \/ ~v27 \/ v19) /\
       (~v30 \/ ~v29 \/ v21) /\ (~v23 \/ ~v23 \/ v23) /\
       (~v23 \/ ~v25 \/ v25) /\ (~v23 \/ ~v27 \/ v27) /\
       (~v23 \/ ~v29 \/ v29) /\ (~v29 \/ v1) /\ (~v21 \/ v3) /\ (~v14 \/ v4) /\
       (~v6 \/ v6) /\ (~v27 \/ v8) /\ (~v19 \/ v10) /\ (~v12 \/ v12) /\
       (~v4 \/ v14) /\ (~v25 \/ v30) /\ (~v17 \/ v17) /\ (~v10 \/ v19) /\
       (~v3 \/ v21) /\ (~v23 \/ v23) /\ (~v30 \/ v25) /\ (~v8 \/ v27) /\
       (~v1 \/ v29) /\ (v0 \/ v1) /\ (v2 \/ v3) /\ (v31 \/ v4) /\ (v5 \/ v6) /\
       (v7 \/ v8) /\ (v9 \/ v10) /\ (v11 \/ v12) /\ (v13 \/ v14) /\
       (v15 \/ v30) /\ (v16 \/ v17) /\ (v18 \/ v19) /\ (v20 \/ v21) /\
       (v22 \/ v23) /\ (v24 \/ v25) /\ (v26 \/ v27) /\ (v28 \/ v29) /\ ~v30 /\
       ~v31)`;

val _ = time (for_se 1 100) (fn i => ignore (term_tokens.lextest [] s));

*)
