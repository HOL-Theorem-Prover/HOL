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

val spaces = [#" ",#"\t",#"\n",#"\r"]

(*---------------------------------------------------------------------------
   Escape sequences
 ----------------------------------------------------------------------------*)

fun wait_esc_space acc charl =
  case charl of
    [] => raise ERR "wait_escape" ""
  | #"\\" :: m => (#"\\" :: acc, m)
  | a :: m =>
    if mem a spaces
    then wait_esc_space (a :: acc) m
    else raise ERR "wait_escape" "::space:: expected"

fun wait_esc acc charl =
  case charl of
    [] => raise ERR "wait_esc" ""
  | a :: m =>
    if mem a spaces then wait_esc_space (a :: acc) m else (a :: acc,m)

(*---------------------------------------------------------------------------
   Comments
 ----------------------------------------------------------------------------*)

fun rm_comment_aux isq par acc charl =
  if isq then
    case charl of
      []         => rev acc
    | #"\\" :: m =>
      let val (loc_acc,loc_m) = wait_esc [#"\\"] m in
        rm_comment_aux true 0 (loc_acc @ acc) loc_m
      end
    | #"\"" :: m => rm_comment_aux false 0 (#"\"" :: acc) m
    | a :: m     => rm_comment_aux true 0 (a :: acc) m
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

fun is_blank c = mem c spaces

fun is_sep c =
  c = #"(" orelse c = #")" orelse c = #"[" orelse c = #"]" orelse
  c = #"{" orelse c = #"}" orelse c = #"," orelse c = #";"

fun is_seps s = mem s ["(",")","[","]","{","}",",",";"]

fun is_dot c = c = #"."

fun is_sml_id #"_" = true
  | is_sml_id #"'" = true
  | is_sml_id ch = Char.isAlphaNum ch

fun in_string str = Lib.C Lib.mem (String.explode str)
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
    #"\\" :: m =>
      let val (loc_buf,loc_m) = wait_esc [#"\\"] m in
        wait_endquote (loc_buf @ buf) loc_m
      end
  | #"\"" :: m          => (implode (rev (#"\"" :: buf)), m)
  | a :: m              => wait_endquote (a :: buf) m
  | _                   => raise ERR "wait_endquote" (implode (rev buf))

fun lex_helper acc charl = case charl of
    [] => rev acc
  | #"\"" :: m =>
    let val (token, cont) = wait_endquote [#"\""] m
      handle HOL_ERR _ => raise ERR "lex_helper"
        (String.concatWith " $" (rev acc))
    in
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
