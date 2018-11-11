(* ========================================================================  *)
(* FILE          : smlLexer.sml                                              *)
(* DESCRIPTION   : Partial SML lexer                                         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure smlLexer :> smlLexer =
struct

open HolKernel boolLib aiLib

val ERR = mk_HOL_ERR "smlLexer"

(*---------------------------------------------------------------------------
   Comments
 ----------------------------------------------------------------------------*)

fun rm_comment_aux isq par acc charl =
  if isq then
    case charl of
      []                  => rev acc
    | #"\\" :: #"\\" :: m => rm_comment_aux true 0 (#"\\" :: #"\\" :: acc) m
    | #"\\" :: #"\"" :: m => rm_comment_aux true 0 (#"\"" :: #"\\" :: acc) m
    | #"\"" :: m          => rm_comment_aux false 0 (#"\"" :: acc) m
    | a :: m              => rm_comment_aux true 0 (a :: acc) m
  else if par > 0 then
    (
    case charl of
      []                => rev acc
    | #"(" :: #"*" :: m => rm_comment_aux false (par + 1) acc m
    | #"*" :: #")" :: m => rm_comment_aux false (par - 1) acc m
    | a :: m            => rm_comment_aux false par acc m
    )
  else if par = 0 then
    (
    case charl of
      []                => rev acc
    | #"\"" :: m        => rm_comment_aux true 0 (#"\"" :: acc) m
    | #"(" :: #"*" :: m => rm_comment_aux false 1 acc m
    | #"*" :: #")" :: m => raise ERR "rm_comment" "negative_par"
    | a :: m            => rm_comment_aux false 0 (a :: acc) m
    )
  else raise ERR "rm_comment_aux" (implode (rev acc) ^ " : " ^ implode charl)

fun rm_comment s = implode (rm_comment_aux false 0 [] (explode s))

(* -------------------------------------------------------------------------
   Tokens
   ------------------------------------------------------------------------- *)

fun is_blank c =
  c = #" " orelse c = #"\n" orelse c = #"\t"

fun is_sep c =
  c = #"(" orelse c = #")" orelse c = #"[" orelse c = #"]" orelse
  c = #"{" orelse c = #"}" orelse c = #"," orelse c = #";"

fun is_seps s = mem s ["(",")","[","]","{","}",",",";"]

fun is_dot c = c = #"."

fun is_sml_id #"_" = true
  | is_sml_id #"'" = true
  | is_sml_id ch = Char.isAlphaNum ch

fun in_string str =
  let
    val strlist = String.explode str
    val memb = Lib.C Lib.mem strlist
  in
    memb
  end

val sml_symbolics = "!%&$+/:<=>?@~|#*\\-~^";
val is_sml_symbol = in_string sml_symbolics;

(* -------------------------------------------------------------------------
   Lexer
   ------------------------------------------------------------------------- *)

fun wait_char f_char buf charl = case charl of
    []     => (implode (rev buf), [])
  | a :: m =>
    (if f_char a
     then (implode (rev buf), charl)
     else wait_char f_char (a :: buf) m)

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
    else if is_sep a orelse is_dot a
      then lex_helper (Char.toString a :: acc) m
    else if is_sml_id a
      then
        let val (token, cont) = wait_char (not o is_sml_id) [] charl in
          lex_helper (token :: acc) cont
        end
    else if is_sml_symbol a
      then
        let val (token, cont) = wait_char (not o is_sml_symbol) [] charl in
          lex_helper (token :: acc) cont
        end
    else raise ERR "lex_helper" (Char.toString a)
    )

(* This fix is not perfect if ~ or # is redefined 
   as we forgot if there was a space or not *)
fun reg_char l = case l of
    [] => []
  | "#" :: s :: m => (
                     if String.sub(s,0) = #"\""
                     then ("#" ^ s) :: reg_char m
                     else "#" :: reg_char (s :: m)
                     )
  | "~" :: s :: m => (
                     if Char.isDigit (String.sub(s,0))
                     then ("~" ^ s) :: reg_char m
                     else "~" :: reg_char (s :: m)
                     )                   
  | a :: m        => a :: reg_char m

fun some_acc acc =
  if null acc then [] else [String.concatWith "." (rev acc)]

fun reg_dot acc l = case l of
    [] => some_acc acc
  | "." :: "." :: "." :: m => some_acc acc @ ["..."] @ reg_dot [] m
  | "." :: b :: m          => reg_dot (b :: acc) m
  | a :: m                 => some_acc acc @ reg_dot [a] m

fun partial_sml_lexer s = reg_dot [] (reg_char (lex_helper [] (explode s)))


(* -------------------------------------------------------------------------
   Reserved tokens used in tttUnfold.
   ------------------------------------------------------------------------- *)

val reserved_dict =
  dnew String.compare
  (map (fn x => (x,()))
  ["op", "if", "then", "else", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr", "andalso", "orelse",
   "and", "datatype", "type", "where", ":", ";" , ":>",
   "let", "in", "end", "while", "do",
   "local","=>","case","of","_","|","fn","handle","raise","#",
   "[","(",",",")","]","{","}","..."])

fun is_quoted s = String.sub (s,0) = #"\"" 
  handle Interrupt => raise Interrupt | _ => false
fun is_number s = Char.isDigit (String.sub (s,0)) 
  handle Interrupt => raise Interrupt | _ => false
fun is_chardef s = String.substring (s,0,2) = "#\"" 
  handle Interrupt => raise Interrupt | _ => false

fun is_reserved s =
  dmem s reserved_dict orelse
  is_number s orelse is_quoted s orelse is_chardef s


end (* struct *)
