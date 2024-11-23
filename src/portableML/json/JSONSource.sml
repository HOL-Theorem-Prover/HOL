(* json-source.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * JSON input sources.  Note that this module is internal the the library.
 *)

structure JSONSource =
struct

(* the state of a source is a functional input stream and a count
 * of lines (starting at 1)
 *)
type state = (TextIO.StreamIO.instream * int)

type source = state option ref

(* open a text input stream as a source *)
fun openStream inS = ref(SOME(TextIO.getInstream inS, 1))

(* open a text file as a source *)
fun openFile file = openStream (TextIO.openIn file)

(* open a string as a source *)
fun openString s = openStream (TextIO.openString s)

(* close a source *)
fun close (source as ref(SOME(inS, _))) = (
  TextIO.StreamIO.closeIn inS;
  source := NONE)
  | close _ = ()

(* syntax-error codes *)
datatype error_code
  = InvalidCharacter
  | InvalidLiteral
  | NumberTooLarge
  | InvalidNumber
  | InvalidArray
  | InvalidObject
  | ExpectedKey
  | ExpectedColon
  | CommentsNotAllowed
  | UnclosedComment
  | UnclosedString
  | InvalidEscape
  | InvalidUTF8
  | IncompleteUTF8
  | InvalidUnicodeSurrogatePair
  | InvalidUnicodeEscape
  | NonPrintingASCII

fun errorMsg (src : state, ec) = let
  val msg = (case ec
              of InvalidCharacter => "invalid character"
               | InvalidLiteral => "invalid literal identifier"
               | NumberTooLarge => "number exceeds maximum number of digits"
               | InvalidNumber => "invalid number syntax"
               | InvalidArray => "invalid array syntax; expected ',' or ']'"
               | InvalidObject => "invalid object syntax; expected ',' or '}'"
               | ExpectedKey => "invalid object syntax; expected key"
               | ExpectedColon => "invalid object syntax; expected ':'"
               | CommentsNotAllowed => "JSON comments not allowed"
               | UnclosedComment => "unclosed comment"
               | UnclosedString => "unclosed string"
               | InvalidEscape => "invalid escape sequence"
               | InvalidUTF8 => "invalid UTF-8"
               | IncompleteUTF8 => "incomplete UTF-8"
               | InvalidUnicodeSurrogatePair => "invalid Unicode surrogate pair"
               | InvalidUnicodeEscape => "invalid Unicode escape sequence"
               | NonPrintingASCII => "non-printing ASCII character"
            (* end case *))
in
  concat("Error at line " :: Int.toString(#2 src) :: ": " :: [msg])
end

end
