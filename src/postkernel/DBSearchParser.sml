structure DBSearchParser :> DBSearchParser =
struct

open HolKernel

val ERR = mk_HOL_ERR "DBSearchParser"

datatype token = Tilde
               | Question
               | Pipe
               | LeftBracket
               | RightBracket
               | Word of string
               | EOF

datatype regexp = Maybe of regexp
                | Orderless of regexp * regexp
                | Union of regexp * regexp
                | Then of regexp * regexp
                | Term of string

fun isSpecialChar c = Lib.mem c [#"~", #"(", #")", #"?", #"|"]

fun tokenise str = let
    fun tokenise' [] [] = [EOF]
      | tokenise' acc [] = [Word(String.implode (rev acc)), EOF]
      | tokenise' acc (c::cs) =
        (case (acc, c) of
            ([], #"~") => Tilde :: tokenise' [] cs
          | ([], #"?") => Question :: tokenise' [] cs
          | ([], #"|") => Pipe :: tokenise' [] cs
          | ([], #"(") => LeftBracket :: tokenise' [] cs
          | ([], #")") => RightBracket :: tokenise' [] cs
          | _ => if isSpecialChar c
                 then Word(String.implode (rev acc)) :: tokenise' [] (c::cs)
                 else tokenise' (c::acc) cs
        )
in
    tokenise' [] (String.explode str)
end

val tokens = ref [];

fun tok() = hd (!tokens)

fun advance() = let
    val head = tok()
    val _ = tokens := tl (!tokens)
in head end

fun consume(t) = if tok() = t
             then advance()
             else Word "Unexpected character"

fun E() = let
    val expr = T()
in
    case tok() of
        Question => (advance(); Maybe expr)
      | _ => expr
end

and E'() = C(E())

and T() =
    case tok() of
        Word s => T'(F())
      | LeftBracket => T'(F())
      | _ => raise ERR "T" "Unexpected token"

and T'(a) =
    case tok() of
        Tilde => (advance(); Orderless(a, T'(F())))
      | Pipe => (advance(); Union(a, T'(F())))
      | _ => a

and F() =
    case tok() of
        Word s => (advance(); Term(s))
      | LeftBracket => let
          val _ = consume(LeftBracket)
          val v = E()
          val _ = consume(RightBracket)
      in T'(v) end
      | _ => raise ERR "F" "Unexpected token"

and C(expr) =
    case tok() of
        EOF => expr
      | _ => Then(expr, E'())

fun compile_pattern str = (tokens := tokenise str; E'())

val matches = let
    fun matches' immediate_match regexp str =
        case regexp of
            Union (a, b) => matches' false a str orelse matches' false b str
          | Orderless (a, b) => matches' false a str andalso matches' false b str
          | Then (a, Then (Maybe r, b)) => matches' immediate_match (Then(a, b)) str
                                           orelse matches' immediate_match (Then(a, Then(r, b))) str
          | Then (a, b) => (case split_on_match a str 0 of
                                SOME remainder => matches' true b remainder
                              | NONE => false)
          | Term s => if immediate_match
                      then String.isPrefix s str
                      else String.isSubstring s str
          | Maybe r => true (* the only case where maybe matters is chained Thens *)

    and split_on_match regexp str n =
        if n > String.size str then NONE
        else let
            val length = String.size str
            val current = String.substring (str, 0, n)
        in
            if matches' false regexp current
            then SOME (String.substring (str, n, length - n))
            else split_on_match regexp str (n+1)
        end

in
    matches' false
end

end
