(* json-parser.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *)

structure JSONParser :> JSONParser =
struct

structure W = Word

datatype error_code = datatype JSONSource.error_code

type source = JSONSource.source

val openStream = JSONSource.openStream
val openFile = JSONSource.openFile
val openString = JSONSource.openString
val close = JSONSource.close

(* fast (no overflow checking) increment/decrement operations *)
fun inc n = W.toIntX(W.fromInt n + 0w1)
fun dec n = W.toIntX(W.fromInt n - 0w1)

(* local copy of list reverse that the compiler can inline *)
fun reverse xs = let
  fun rev' ([], ys) = ys
    | rev' (x::xs, ys) = rev' (xs, x::ys)
in
  rev' (xs, [])
end

(* make a string from a list of characters in reverse order; the first argument
 * is the number of characters, which must be equal or greater than the length
 * of the input list
 *)
fun mkString (_, cs) = CharVector.fromList (List.rev cs)

fun next (src as (strm, nLines)) =
    (case TextIO.StreamIO.input1 strm of
         SOME(#"\n", strm') => (#"\n", (strm', nLines+1))
       | SOME(c, strm') => (c, (strm', nLines))
       | NONE => (#"\000", src)
    (* end case *))

fun parse source = let
  fun error' (src, ec) = let
    val msg = JSONSource.errorMsg (src, ec)
  in
    raise Fail msg
  end
  fun matchC (src, c) = let
    val (c', src') = next src
  in
    if (c = c')
    then src'
    else error' (src, InvalidLiteral)
  end
  (* skip white space *)
  fun skipWS (src as (strm, nLines)) =
      (case TextIO.StreamIO.input1 strm of
           SOME(#" ", strm') => skipWS (strm', nLines)
         | SOME(#"\t", strm') => skipWS (strm', nLines)
         | SOME(#"\r", strm') => skipWS (strm', nLines)
         | SOME(#"\n", strm') => skipWS (strm', nLines+1)
         (*
                  | SOME(#"/", strm') => if comments
                      then skipComment (strm', nLines)
                      else error' (src, CommentsNotAllowed)
         *)
         (* currently, comments are always allowed *)
         | SOME(#"/", strm') => skipComment (strm', nLines)
         | SOME(c, strm') => (c, (strm', nLines))
         | NONE => (#"\000", src)
      (* end case *))
  (* skip over a C-style comment; the initial '/' has been consumed *)
  and skipComment (src as (strm, nLines)) = let
    fun skip (strm, nLines) =
        (case TextIO.StreamIO.input1 strm of
             SOME(#"*", strm') =>
             let
               (* look for "/" (possibly preceded by stars) *)
               fun lp (strm, nLines) =
                   (case TextIO.StreamIO.input1 strm of
                        SOME(#"/", strm') => skipWS (strm', nLines)
                      | SOME(#"*", strm') => lp (strm', nLines)
                      | SOME(#"\n", strm') => skip (strm', nLines+1)
                      | SOME(_, strm') => skip (strm', nLines)
                      | NONE => error' (src, UnclosedComment)
                   (* end case *))
             in
               lp (strm', nLines)
             end
           | SOME(#"\n", strm') => skip (strm', nLines+1)
           | SOME(_, strm') => skip (strm', nLines)
           | NONE => error' (src, UnclosedComment)
        (* end case *))
  in
    case TextIO.StreamIO.input1 strm
     of SOME(#"*", strm') => skip (strm', nLines)
      | _ => error' (src, InvalidCharacter)
                    (* end case *)
  end
  (* parse a JSON value *)
  fun parseValue src =
      (case skipWS src of
           (#"[", src) => parseArray src
         | (#"{", src) => parseObject src
         | (#"-", src) => (case next src
                            of (#"0", src') => scanNumber(src', true, 0)
                             | (#"1", src') => scanNumber(src', true, 1)
                             | (#"2", src') => scanNumber(src', true, 2)
                             | (#"3", src') => scanNumber(src', true, 3)
                             | (#"4", src') => scanNumber(src', true, 4)
                             | (#"5", src') => scanNumber(src', true, 5)
                             | (#"6", src') => scanNumber(src', true, 6)
                             | (#"7", src') => scanNumber(src', true, 7)
                             | (#"8", src') => scanNumber(src', true, 8)
                             | (#"9", src') => scanNumber(src', true, 9)
                             | _ => error' (src, InvalidNumber)
                          (* end case *))
         | (#"0", src') => scanNumber(src', false, 0)
         | (#"1", src') => scanNumber(src', false, 1)
         | (#"2", src') => scanNumber(src', false, 2)
         | (#"3", src') => scanNumber(src', false, 3)
         | (#"4", src') => scanNumber(src', false, 4)
         | (#"5", src') => scanNumber(src', false, 5)
         | (#"6", src') => scanNumber(src', false, 6)
         | (#"7", src') => scanNumber(src', false, 7)
         | (#"8", src') => scanNumber(src', false, 8)
         | (#"9", src') => scanNumber(src', false, 9)
         | (#"\"", src) => scanStringValue src
         | (#"f", src) =>
           let (* match "a" "l" "s" "e" *)
             val src = matchC (src, #"a")
             val src = matchC (src, #"l")
             val src = matchC (src, #"s")
             val src = matchC (src, #"e")
           in
             (JSON.BOOL false, src)
           end
         | (#"n", src) => let (* match "u" "l" "l" *)
                            val src = matchC (src, #"u")
                            val src = matchC (src, #"l")
                            val src = matchC (src, #"l")
                          in
                            (JSON.NULL, src)
                          end
                          | (#"t", src) => let (* match "r" "u" "e" *)
                            val src = matchC (src, #"r")
                            val src = matchC (src, #"u")
                            val src = matchC (src, #"e")
                          in
                            (JSON.BOOL true, src)
                          end
                          | _ => error' (src, InvalidCharacter)
                       (* end case *))
  (* parse a JSON array assuming that the '[' has been consumed *)
  and parseArray src = let
    (* loop to scan one or more items *)
    fun lp (src, items) = let
      val (item, src) = parseValue src
      val items = item::items
    in
      case skipWS src
       of (#",", src) => lp (src, items)
        | (#"]", src) => (JSON.ARRAY(reverse items), src)
        | _ => error' (src, InvalidArray)
                      (* end case *)
    end
  in
    case skipWS src
     of (#"]", src) => (JSON.ARRAY[], src)
      | _ => lp (src, [])
                (* end case *)
  end
  (* parse a JSON object assuming that the '[' has been consumed *)
  and parseObject src = let
    (* loop to scan one or more key-value pairs *)
    fun lp (src, items) =
        (case skipWS src of
             (#"\"", src) =>
             let
               val (key, src) = scanString src
             in
               case skipWS src of
                   (#":", src) =>
                   let
                     val (v, src) = parseValue src
                     val items = (key, v)::items
                   in
                     case skipWS src
                      of (#",", src) => lp (src, items)
                       | (#"}", src) => (JSON.OBJECT(reverse items), src)
                       | _ => error' (src, InvalidObject)
                                     (* end case *)
                   end
                 | _ => error' (src, ExpectedColon)
                               (* end case *)
             end
           | _ => error' (src, ExpectedKey)
        (* end case *))
  in
    case skipWS src
     of (#"}", src) => (JSON.OBJECT[], src)
      | _ => lp (src, [])
                (* end case *)
  end
  (* scan a string value assuming that the first quote has been consumed *)
  and scanString start = let
    fun c2w c = W.fromInt(ord c)
    fun w2c w = Char.chr(W.toInt w)
    (* scan a string
     * `src` is the input source
     * `n` is the number of bytes in the result
     * `cs` is the result list of characters in reverse order
     *)
    fun scan (src, n, cs) =
        (case next src of
             (#"\000", _) => error' (start, UnclosedString)
           | (#"\"", src) => (mkString(n, cs), src)
           | (#"\\", src) => scanEscape (src, n, cs)
           | (c, src) =>
             if (#" " <= c) andalso (c < #"\127") then
               (* printable ASCII character *)
               scan (src, inc n, c::cs)
             else
               (* either non-printable ASCII or UTF-8 byte sequence *)
               scanUTF8 (src, c, c2w c, n, cs)
        (* end case *))
    and scanEscape (src, n, cs) = let
      fun return (src, c) = scan (src, inc n, c::cs)
    in
      case next src
       of (#"\"", src) => return (src, #"\"")
        | (#"\\", src) => return (src, #"\\")
        | (#"/", src) => return (src, #"/")
        | (#"b", src) => return (src, #"\008") (* backspace *)
        | (#"f", src) => return (src, #"\012") (* form feed *)
        | (#"n", src) => return (src, #"\010") (* line feed *)
        | (#"r", src) => return (src, #"\013") (* carriage return *)
        | (#"t", src) => return (src, #"\009") (* tab *)
        | (#"u", src) => scanUnicodeEscape (src, n, cs)
        | _ => error' (src, InvalidEscape)
                      (* end case *)
    end
    (* scan a Unicode escape sequence; we have already consumed the "\u"
     * prefix, so we just need to parse the four hex digits followed by
     * a possible second escape sequence for a surrogate pair.  The result
     * is encoded as a UTF-8 byte sequence.
     *)
    and scanUnicodeEscape (src, n, cs) = let
      (* scan a hex digit *)
      fun getDigit src = (case next src
                           of (#"0", src) => (0w0, src)
                            | (#"1", src) => (0w1, src)
                            | (#"2", src) => (0w2, src)
                            | (#"3", src) => (0w3, src)
                            | (#"4", src) => (0w4, src)
                            | (#"5", src) => (0w5, src)
                            | (#"6", src) => (0w6, src)
                            | (#"7", src) => (0w7, src)
                            | (#"8", src) => (0w8, src)
                            | (#"9", src) => (0w9, src)
                            | (#"a", src) => (0w10, src)
                            | (#"A", src) => (0w10, src)
                            | (#"b", src) => (0w11, src)
                            | (#"B", src) => (0w11, src)
                            | (#"c", src) => (0w12, src)
                            | (#"C", src) => (0w12, src)
                            | (#"d", src) => (0w13, src)
                            | (#"D", src) => (0w13, src)
                            | (#"e", src) => (0w14, src)
                            | (#"E", src) => (0w14, src)
                            | (#"f", src) => (0w15, src)
                            | (#"F", src) => (0w15, src)
                            | _ => error' (src, InvalidUnicodeEscape)
                         (* end case *))
      fun getDigits src = let
        (* get a four-digit hex number *)
        val (d0, src) = getDigit src
        val (d1, src) = getDigit src
        val (d2, src) = getDigit src
        val (d3, src) = getDigit src
        val n = W.<<(d0, 0w12)
                + W.<<(d1, 0w8)
                + W.<<(d2, 0w4)
                + d3
      in
        (n, src)
      end
      val (u0, src) = getDigits src
      (* get the second 16-bit code point of a surrogate pair *)
      fun scanLowSurrogate src = (
        (* match "\uxxxx" *)
        case next src
         of (#"\\", src) => (case next src
                              of (#"u", src) => let
                                val (u1, src) = getDigits src
                              in
                                if (u1 < 0wxDC00) orelse (0wxDFFF < u1)
                                then error' (src, InvalidUnicodeSurrogatePair)
                                (* convert pair to a Unicode code point
                                 * and then to UTF-8 bytes.
                                 *)
                                else toUTF8 (src,
                                             0wx10000
                                             + W.<<(u0 - 0wxD800, 0w10)
                                             + (u1 - 0wxDC00))
                              end
                               | _ => error' (src, InvalidUnicodeSurrogatePair)
                            (* end case *))
          | _ => error' (src, InvalidUnicodeSurrogatePair)
      (* end case *))
      (* convert a word to a UTF-8 sequence; remember that `cs`
       * is in reverse order.
       *)
      and toUTF8 (src, w) =
          if (w <= 0wx7f)
          then scan (src, inc n, w2c w :: cs) (* one byte (ASCII) *)
          else if (w <= 0wx7ff)
                    (* two bytes *)
          then scan (src,
                     n+2,
                     w2c(W.orb(0wx80, W.andb(w, 0wx3f)))
                     :: w2c(W.orb(0wxc0, W.>>(w, 0w6)))
                     :: cs)
          else if (w <= 0wxffff)
                    (* three bytes *)
          then scan (src,
                     n+3,
                     w2c(W.orb(0wx80, W.andb(w, 0wx3f)))
                     :: w2c(W.orb(0wx80, W.andb(W.>>(w, 0w6), 0wx3f)))
                     :: w2c(W.orb(0wxe0, W.>>(w, 0w12)))
                     :: cs)
          else if (w <= 0wx10ffff)
                    (* four bytes *)
          then scan (src,
                     n+4,
                     w2c(W.orb(0wx80, W.andb(w, 0wx3f)))
                     :: w2c(W.orb(0wx80, W.andb(W.>>(w, 0w6), 0wx3f)))
                     :: w2c(W.orb(0wx80, W.andb(W.>>(w, 0w12), 0wx3f)))
                     :: w2c(W.orb(0wxf0, W.>>(w, 0w18)))
                     :: cs)
          else error' (src, InvalidUnicodeEscape)
    in
      if (u0 < 0wxD800)
      then toUTF8 (src, u0)
      else if (u0 <= 0wxDBFF) (* D800-DBFF: high surrogate *)
      then scanLowSurrogate src
      else if (u0 <= 0wxDFFF) (* DC00-DFFF: low surrogate *)
      then error' (src, InvalidUnicodeSurrogatePair)
      else toUTF8 (src, u0)
    end (* scanUnicodeEscape *)
    (* a simple state machine for scanning a valid UTF-8 byte sequence.  See
     * https://unicode.org/mail-arch/unicode-ml/y2003-m02/att-0467/01-The_Algorithm_to_Valide_an_UTF-8_String
     * for a description of the state machine.
     *)
    and scanUTF8 (src, chr0, byte0, n, cs) = let
      fun getByte src = (case next src
                          of (#"\000", _) => error' (src, IncompleteUTF8)
                           | (c, src') => (c2w c, c, src')
                        (* end case *))
      fun inRange (minB : word, b, maxB) = ((b - minB) <= maxB - minB)
      (* handles last byte for all multi-byte sequences *)
      fun stateA (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wx80, b, 0wxbf)
        then scan (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* handles second/third byte for three/four-byte sequences *)
      and stateB (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wx80, b, 0wxbf)
        then stateA (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* byte0 = 0b1110_0000 (3-byte sequence) *)
      and stateC (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wxa0, b, 0wxbf)
        then stateA (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* byte0 = 0b1110_1101 (3-byte sequence) *)
      and stateD (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wx80, b, 0wx9f)
        then stateA (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* byte0 = 0b1111_0001 .. 0b1111_0011 (4-byte sequence) *)
      and stateE (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wx80, b, 0wxbf)
        then stateB (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* byte0 = 0b1111_0000 (4-byte sequence) *)
      and stateF (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wx90, b, 0wxbf)
        then stateB (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* byte0 = 0b1111_1000 (4-byte sequence) *)
      and stateG (src, n, chrs) = let
        val (b, c, src) = getByte src
      in
        if inRange(0wx80, b, 0wx8f)
        then stateB (src, inc n, c::chrs)
        else error' (src, InvalidUTF8)
      end
      (* add the first character to the list of processed characters *)
      val cs = chr0 :: cs
      val n = inc n
    in
      if (byte0 <= 0wx7f)
           (* this case only occurs for non-printing ASCII characters *)
      then error' (src, NonPrintingASCII)
      else if inRange(0wxc2, byte0, 0wxdf)
      then stateA (src, n, cs)
      else if inRange(0wxe1, byte0, 0wxec)
              orelse inRange(0wxee, byte0, 0wxef)
      then stateB (src, n, cs)
      else if (byte0 = 0wxe0)
      then stateC (src, n, cs)
      else if (byte0 = 0wxed)
      then stateD (src, n, cs)
      else if inRange(0wxf1, byte0, 0wxf3)
      then stateE (src, n, cs)
      else if (byte0 = 0wxf0)
      then stateF (src, n, cs)
      else if (byte0 = 0wxf4)
      then stateG (src, n, cs)
      else error' (src, InvalidUTF8)
    end (* scanUTF8 *)
  in
    scan (start, 0, [])
  end (* scanString *)
  and scanStringValue src = let
    val (s, src) = scanString src
  in
    (JSON.STRING s, src)
  end
  (* scan an integer or floating-point number.  If the number of digits
   * for an integer literal exceeds the `maxDigits` limit, then we signal
   * a `NumberTooLarge` error.
   *)
  and scanNumber (src, isNeg, firstDigit) = let
    (* make a JSON `FLOAT` value from pieces.  The lists of digits
     * are in reverse order and are in the range [0..9].
     *)
    fun mkFloat (sign, whole, frac, exp, src) = let
      val f = valOf(Real.fromDecimal {
                       class = IEEEReal.NORMAL,
                       sign = sign,
                       digits = List.revAppend(whole, reverse frac),
                       exp = exp + List.length whole
                   }) handle Overflow => if sign then Real.negInf
                                         else Real.posInf
    in
      if Real.isFinite f
      then (JSON.FLOAT f, src)
      else error' (src, NumberTooLarge)
    end
    (* scan an integer or the whole part of a float *)
    fun scanWhole (src, digits) =
        (case next src of
             (#"0", src) => scanWhole (src, 0::digits)
           | (#"1", src) => scanWhole (src, 1::digits)
           | (#"2", src) => scanWhole (src, 2::digits)
           | (#"3", src) => scanWhole (src, 3::digits)
           | (#"4", src) => scanWhole (src, 4::digits)
           | (#"5", src) => scanWhole (src, 5::digits)
           | (#"6", src) => scanWhole (src, 6::digits)
           | (#"7", src) => scanWhole (src, 7::digits)
           | (#"8", src) => scanWhole (src, 8::digits)
           | (#"9", src) => scanWhole (src, 9::digits)
           | (#".", src) => scanFrac (src, digits)
           | (#"e", src) => scanExp (src, digits, [])
           | (#"E", src) => scanExp (src, digits, [])
           | _ =>
             let
               fun cvt ([], _, n) =
                   if isNeg then (JSON.INT(~n), src)
                   else (JSON.INT n, src)
                 | cvt (d::ds, k, n) =
                   cvt (ds, inc k, 10*n + IntInf.fromInt d)
             in
               cvt (reverse digits, 0, 0)
             end
        (* end case *))
    (* scan the fractional part of a real; the '.' has already been
     * consumed.
     *)
    and scanFrac (src, wDigits) = let
      fun scanF (src, fDigits) =
          (case next src of
               (#"0", src) => scanF (src, 0::fDigits)
             | (#"1", src) => scanF (src, 1::fDigits)
             | (#"2", src) => scanF (src, 2::fDigits)
             | (#"3", src) => scanF (src, 3::fDigits)
             | (#"4", src) => scanF (src, 4::fDigits)
             | (#"5", src) => scanF (src, 5::fDigits)
             | (#"6", src) => scanF (src, 6::fDigits)
             | (#"7", src) => scanF (src, 7::fDigits)
             | (#"8", src) => scanF (src, 8::fDigits)
             | (#"9", src) => scanF (src, 9::fDigits)
             | (#"e", src) => scanExp (src, wDigits, fDigits)
             | (#"E", src) => scanExp (src, wDigits, fDigits)
             | _ => mkFloat (isNeg, wDigits, fDigits, 0, src)
          (* end case *))
    in
      scanF (src, [])
    end
    (* scan the exponent part of a real; the "e"/"E" has already been
     * consumed.
     *)
    and scanExp (src, whole, frac) = let
      val (expSign, exp, seenDigit, src) =
          (case next src of
               (#"-", src) => (~1, 0, false, src)
             | (#"+", src) => (1, 0, false, src)
             | (#"0", src) => (1, 0, true, src)
             | (#"1", src) => (1, 1, true, src)
             | (#"2", src) => (1, 2, true, src)
             | (#"3", src) => (1, 3, true, src)
             | (#"4", src) => (1, 4, true, src)
             | (#"5", src) => (1, 5, true, src)
             | (#"6", src) => (1, 6, true, src)
             | (#"7", src) => (1, 7, true, src)
             | (#"8", src) => (1, 8, true, src)
             | (#"9", src) => (1, 9, true, src)
             | _ => error' (src, InvalidNumber)
          (* end case *))
      fun scanE (src, seenDigit, exp) =
          (case next src of
               (#"0", src) => scanE (src, true, 10 * exp)
             | (#"1", src) => scanE (src, true, 10 * exp + 1)
             | (#"2", src) => scanE (src, true, 10 * exp + 2)
             | (#"3", src) => scanE (src, true, 10 * exp + 3)
             | (#"4", src) => scanE (src, true, 10 * exp + 4)
             | (#"5", src) => scanE (src, true, 10 * exp + 5)
             | (#"6", src) => scanE (src, true, 10 * exp + 6)
             | (#"7", src) => scanE (src, true, 10 * exp + 7)
             | (#"8", src) => scanE (src, true, 10 * exp + 8)
             | (#"9", src) => scanE (src, true, 10 * exp + 9)
             | _ => if seenDigit
                    then mkFloat (isNeg, whole, frac, expSign * exp, src)
                    else error' (src, InvalidNumber)
          (* end case *))
    in
      scanE (src, seenDigit, exp)
      handle Overflow => error' (src, NumberTooLarge)
    end
  in
    if (firstDigit = 0)
    then (case next src
           of (#".", src) => scanFrac(src, [])
            | (#"e", src) => scanExp(src, [], [])
            | (#"E", src) => scanExp(src, [], [])
            | _ => (JSON.INT 0, src)
         (* end case *))
    else scanWhole (src, [firstDigit])
  end (* scanNumber *)
  val src = (case !source
              of SOME src => src
               | NONE => raise Fail "closed JSON source"
            (* end case *))
  val (jv, src) = parseValue src
in
  source := SOME src;
  jv
end (* parse *)

fun parseFile fileName = let
  val inStrm = openFile fileName
  val v = parse inStrm
          handle ex => (close inStrm; raise ex)
in
  close inStrm;
  v
end

end
