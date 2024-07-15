structure DBSearchParser :> DBSearchParser =
struct

open HolKernel

val ERR = mk_HOL_ERR "DBSearchParser"

(*
 * We want to parse regular expressions with the following
 * operators: ~ (search by fragments), | (union), and ? (optional)
 * with support for parentheses.
 *
 * The grammar for this is as follows:
 *
 * E  --> E | T
 * E  --> T
 * T  --> T ~ T'
 * T  --> T'
 * T' --> C[?]
 * C  --> ( E' )
 * C  --> string
 * E' --> E
 *)

(* Previous semantics for Twiddle was to search for strings that contained
   all of the twiddle arguments in any order. Now, for the sake of avoiding
   a factorial explosion in compiling many ~ arguments,

     A ~ B

   maps to

     .*A.* & .*B.*

   where & is the intersection operation on regexps. This gives almost
   identical semantics except when A and B can overlap in their matches
*)
datatype search_regexp =
           Optional of search_regexp
         | Or of search_regexp * search_regexp
         | Twiddle of search_regexp * search_regexp
         | Seq of search_regexp * search_regexp
         | Char of char
         | Many of search_regexp
         | Empty
         | Any

datatype token = E of search_regexp
               | T of char
               | Concat
               | Start

(* is_special_char except ‘.’ since we want it to have the precedence of a
   regular character *)
val is_special_char = C Lib.mem [#"~", #"|", #"?", #"(", #")", #"*"]

(* a = top token within stack; b = next input token *)
fun check_precedence (a, b) =
    case (a, b) of
        (T #"(", T #")") => EQUAL
      | (  _   , T #")") => GREATER
      | (T #"~", T #"|") => GREATER
      | (T #".",   _   ) => GREATER
      | (T #")",   _   ) => GREATER
      | (T #"*",   _   ) => GREATER
      | (T #"?",   _   ) => GREATER
      | (Concat, T #"*") => LESS
      | (Concat, T #"?") => LESS
      | (Concat,   _   ) => GREATER
      | (T id  ,   _   ) => if is_special_char id then LESS else GREATER
      |        _         => LESS

fun is_op (T c) = is_special_char c
  | is_op Start = true
  | is_op _ = false

fun parse_regexp input = let
    fun top_token (E _::xs) = top_token xs
      | top_token (x::_) = x
      | top_token [] = raise ERR "top_token" "Empty stack"
                         (* shouldn't be possible *)

    fun parse (stk as (top::_)) input idx =
        if idx = String.size input then eval stk
        else
          let
            val c = String.sub(input, idx)
            val next = T c
        in
            case check_precedence (top_token stk, next) of
                GREATER => parse (reduce stk) input idx
             |  _ => (* shift *)
                if is_special_char c andalso c <> #"(" orelse is_op (hd stk)
                then
                  parse (next::stk) input (idx + 1) (* normal shift *)
                else
                  parse (next::Concat::stk) input (idx + 1)
        end
    and reduce stk =
        case stk of
            T #"."                     :: ts => E Any :: ts
          | E a    :: T #"|" :: E b    :: ts => E (Or(b, a))::ts
          | E a    :: T #"~" :: E b    :: ts => E (Twiddle(b, a))::ts
          | T #"?" :: E a              :: ts => E (Optional a)::ts
          | T #"*" :: E a              :: ts => E (Many a)::ts
          | T #")" :: E x    :: T #"(" :: ts => E x::ts
          | E a    :: Concat :: E b    :: ts => E (Seq(b, a))::ts
          | T c                        :: ts => E (Char c)::ts
          | _ => raise ERR "reduce" "Could not parse expression"
    and eval stk =
        case stk of
            [E x, Start] => x
          | [Start] => Empty
          | _ => eval (reduce stk)
in parse [Start] input 0 end

(* To actually use this regexp we need to translate it into
 the form that ‘regexpMatch’ recognises. *)

open regexpMatch
open POSIX

val any = Star (Symbs word_set)

fun translate_regexp intermediate = let
    val singleton = Binaryset.singleton Char.compare
    fun Br re = Dot(any, Dot(re, any))
in
    case intermediate of
        Optional pat => Sum (translate_regexp pat, Epsilon)
      | Or (a, b)  => Sum (translate_regexp a, translate_regexp b)
      | Seq (a, b) => Dot (translate_regexp a, translate_regexp b)
      | Char c => Symbs (singleton c)
      | Twiddle (a, b) => And (Br (translate_regexp a), Br (translate_regexp b))
      | Many pat => Star (translate_regexp pat)
      | Empty => Epsilon
      | Any => Symbs word_set
end

fun contains_regexp pattern =
    case total parse_regexp pattern of
        NONE => (HOL_WARNING "DBSearchParser" "contains_regexp"
                             "Invalid search-string; will return no results";
                 fn _ => false)
      | SOME intermediate =>
        let
          val compiled_pattern = translate_regexp intermediate
          fun contains pat = Dot (any, Dot (pat, any))
        in
          match (contains compiled_pattern)
        end

end (* struct *)
