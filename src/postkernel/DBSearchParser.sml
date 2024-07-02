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

datatype search_regexp = Optional of search_regexp
                | Or of search_regexp * search_regexp
                | Twiddle of search_regexp * search_regexp
                | Seq of search_regexp * search_regexp
                | Word of char list

datatype token = E of search_regexp
               | T of char
               | Start

val is_special_char = C Lib.mem [#"~", #"|", #"?", #"(", #")"]

fun check_precedence (a, b) =
    case (a, b) of
        (T #"(", T #")") => EQUAL
      | (_, T #")") => GREATER
      | (T #"~", T #"|") => GREATER
      | (T #"?", _) => GREATER
      | (_, T #"?") => LESS
      | (T #")", _) => GREATER
      | (T id, _) => if is_special_char id
                     then LESS
                     else GREATER
      | _ => LESS

fun parse_regexp input = let
    fun top_token (E _::xs) = top_token xs
      | top_token (x::_) = x

    fun parse (stk as (top::_)) input idx =
        if idx = String.size input then eval stk else let
            val next = T (String.sub (input, idx))
        in
            case check_precedence (top_token stk, next) of
                GREATER => parse (reduce stk) input idx
             |  _ => parse (next::stk) input (idx + 1) (* i.e., shift *)
        end
    and reduce stk =
        case stk of
            (E a)::(T(#"|"))::(E b)::ts => E(Or(b, a))::ts
          | (E a)::(T(#"~"))::(E b)::ts => E(Twiddle(b, a))::ts
          | T(#"?")::(E a)::ts => E(Optional(a))::ts
          | T(#"?")::(T c)::ts => E(Optional(Word [c]))::ts
          | (T #")")::(E x)::(T #"(")::ts => E x::ts
          | (E a)::(E b)::ts => E(Seq(b, a))::ts
          | T(c)::E(Word cs)::ts => E(Word(cs@[c]))::ts
          | T(c)::ts => E(Word [c])::ts
          | _ => raise ERR "reduce" "Could not parse expression"
    and eval stk =
        case stk of
            [E x, Start] => x
          | _ => eval (reduce stk)
in parse [Start] input 0 end

(* To actually use this regexp we need to translate it into
 the form that ‘regexpMatch’ recognises. *)

open regexpMatch
open POSIX

val any = Star (Symbs word_set)

fun translate_regexp intermediate = let
    val singleton = Binaryset.singleton Char.compare
    val compile_chars = List.foldl (fn (c, acc) => Dot (acc, Symbs (singleton c))) Epsilon
in
    case intermediate of
        Optional pat => Sum (translate_regexp pat, Epsilon)
      | Or (a, b)  => Sum (translate_regexp a, translate_regexp b)
      | Seq (a, b) => Dot (translate_regexp a, translate_regexp b)
      | Word cs => compile_chars cs
      | Twiddle (a, b) => let
          val (a', b') = (translate_regexp a, translate_regexp b)
          fun ends a b = Dot (a, Dot (any, b))
      in
          Sum (ends a' b', ends b' a')
      end
end

val is_regexp = List.exists is_special_char o String.explode

fun contains_regexp pattern string =
    if is_regexp pattern then
        let val intermediate = parse_regexp pattern
            val compiled_pattern = translate_regexp intermediate
            fun contains pat = Dot (any, Dot (pat, any))
        in
            match (contains compiled_pattern) string
        end
    else
        String.isSubstring pattern string

end
