(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure TextFormat :>
sig
  type width = int

  val repeatChar: width -> char -> string

  val leftPadWith: char -> width -> string -> string
  val rightPadWith: char -> width -> string -> string
  val centerPadWith: char -> width -> string -> string
  val spreadWith: char -> width -> {left: string, right: string} -> string

  (** Tokenize into words (by spaces) and reflow into the desired width *)
  val textWrap: width -> string -> string
end =
struct

  type width = int

  fun repeatChar n c =
    CharVector.tabulate (n, fn _ => c)

  fun leftPadWith char desiredWidth str =
    if String.size str >= desiredWidth then str
    else repeatChar (desiredWidth - String.size str) char ^ str

  fun rightPadWith char desiredWidth str =
    if String.size str >= desiredWidth then str
    else str ^ repeatChar (desiredWidth - String.size str) char

  fun centerPadWith char desiredWidth str =
    if String.size str >= desiredWidth then
      str
    else
      let
        val count = desiredWidth - String.size str
        val leftCount = count div 2
        val rightCount = count - leftCount
      in
        repeatChar leftCount char ^ str ^ repeatChar rightCount char
      end

  fun spreadWith char desiredWidth {left, right} =
    if String.size left + String.size right >= desiredWidth then
      left ^ right
    else
      let val count = desiredWidth - (String.size left + String.size right)
      in left ^ repeatChar count char ^ right
      end

  fun textWrap desiredWidth str =
    let
      fun finishLine ln =
        String.concatWith " " (List.rev ln)
      fun loop lines (currLine, currLen) toks =
        case toks of
          tok :: remaining =>
            if currLen + String.size tok + 1 > desiredWidth then
              loop (finishLine currLine :: lines) ([], 0) toks
            else
              loop lines (tok :: currLine, currLen + String.size tok + 1)
                remaining
        | [] => String.concatWith "\n" (List.rev (finishLine currLine :: lines))
    in
      loop [] ([], 0) (String.tokens Char.isSpace str)
    end

end
