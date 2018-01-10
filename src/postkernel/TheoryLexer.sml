(* =========================================================================  *)
(* FILE          : TheoryLexer.sml                                            *)
(* DESCRIPTION   : Tokenize theory data                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryLexer :> TheoryLexer =
struct

open Feedback Lib Type Term Thm

val ERR = mk_HOL_ERR "TheoryLexer"

(*----------------------------------------------------------------------------
   Token types
 -----------------------------------------------------------------------------*)

fun is_blank c = c = #" " orelse c = #"\n" orelse c = #"\t"

fun is_sep c = c = #"," orelse c = #"[" orelse c = #"]"

fun is_alphanum #"_" = true
  | is_alphanum ch = Char.isAlphaNum ch

(*----------------------------------------------------------------------------
   Lexer
 -----------------------------------------------------------------------------*)

fun wait_char f_char buf charl = case charl of
    []     => (implode (rev buf), [])
  | a :: m =>
    (
    if f_char a
    then (implode (rev buf), charl)
    else wait_char f_char (a :: buf) m
    )

fun wait_endquote buf charl = case charl of
    #"\\" :: #"\\" :: m => wait_endquote (#"\\" :: #"\\" :: buf) m
  | #"\\" :: #"\"" :: m => wait_endquote (#"\"" :: #"\\" :: buf) m
  | #"\"" :: m          => (implode (rev (#"\"" :: buf)), m)
  | a :: m              => wait_endquote (a :: buf) m
  | _                   => raise ERR "wait_endquote" ""

fun lex_helper acc charl = case charl of
    [] => rev acc
  | #"\"" :: m =>
    let val (token, cont) = wait_endquote [#"\""] m in
      lex_helper (token :: acc) cont
    end
  | a :: m     =>
    (
    if is_blank a
      then lex_helper acc m
    else if is_sep a
      then lex_helper (Char.toString a :: acc) m
    else if is_alphanum a
      then
        let val (token, cont) = wait_char (not o is_alphanum) [] charl in
          lex_helper (token :: acc) cont
        end
    else raise ERR "lex_helper" (Char.toString a)
    )

fun lex_thydata s = lex_helper [] (explode s)
  handle HOL_ERR _ => raise ERR "lex_thydata" s

end (* struct *)
