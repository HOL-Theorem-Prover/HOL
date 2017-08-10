(* =========================================================================  *)
(* FILE          : hhsLexer.sml                                               *)
(* DESCRIPTION   : Partial inefficient SML lexer                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsLexer :> hhsLexer =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "hhsLexer"

(*---------------------------------------------------------------------------
   Tests
 ----------------------------------------------------------------------------*)

fun is_squote s = String.sub (s,0) = #"\"" handle _ => false 
fun is_tquote s = String.sub (s,0) = #"`" handle _ => false 
fun is_dtquote s = 
  let val l = explode s in
    (hd l = #"`" andalso hd (tl l) = #"`" ) 
  end
  handle _ => false 

fun is_blank c =
  c = #" " orelse c = #"\n" orelse c = #"\t"

fun is_blank_string s =
  s= " " orelse s = "\n" orelse s = "\t"

fun is_par c =
  c = #"(" orelse c = #")" orelse c = #"[" orelse c = #"]" orelse
  c = #"{" orelse c = #"}"

fun is_sep c =
  is_blank c orelse is_par c orelse c = #"," orelse c = #";"

fun is_alphanumeric #"_" = true
  | is_alphanumeric #"'" = true
  | is_alphanumeric ch = Char.isAlphaNum ch

fun in_string str =
   let val strlist = String.explode str
       val memb = Lib.C Lib.mem strlist
   in memb
   end;

val sml_symbolics = "!%&$+/:<=>?@~|#*\\-~^";
val is_sml_symbol = in_string sml_symbolics;

(*---------------------------------------------------------------------------
   Remove quotations
 ----------------------------------------------------------------------------*)

fun rm_blank s = 
  implode (filter (not o is_blank) (explode s))

fun rm_tquote s =
  implode (filter (fn x => x <> #"`") (explode s))

fun rm_squote s =
  if is_squote s 
  then (implode o rev o tl o rev o tl o explode) s 
  else raise ERR "rm_squote" ""

(*---------------------------------------------------------------------------
   Lexer itself
 ----------------------------------------------------------------------------*)

fun wait_char f_char acc charl =
  if charl = []        then (implode (rev acc),[]) else
  if f_char (hd charl) then (implode (rev acc), charl) 
  else
    wait_char f_char (hd charl :: acc) (tl charl)
  
fun hhs_lexer acc buf iq isq charl =
  if charl = [] then 
    let val some_buf = if buf = [] then [] else [implode (rev buf)] in
      rev (some_buf @ acc)
    end
  else if iq then
    case charl of
        #"`" :: #"`" :: m => cont_lex acc buf "``" false false m
      | #"`" :: m         => cont_lex acc buf "`" false false m
      | a :: m            => hhs_lexer acc (a :: buf) true false m
      | _                 => raise ERR "hhs_lexer" ""
  else if isq then
    case charl of
        #"\\" :: #"\\" :: m =>
        hhs_lexer acc (#"\\" :: #"\\" :: buf) false true m
      | #"\\" :: #"\"" :: m => 
        hhs_lexer acc (#"\"" :: #"\\" :: buf) false true m
      | #"\"" :: m        => cont_lex acc buf "\"" false false m
      | a :: m            => hhs_lexer acc (a :: buf) false true m
      | _                 => raise ERR "hhs_lexer" ""
  else
    let val (a,m) = (hd charl, tl charl) in
      if is_blank a then cont_lex acc buf (implode [a]) false false m else
      if is_sep a then cont_lex acc buf (implode [a]) false false m else 
      if a = #"." then cont_lex acc buf (implode [a]) false false m else
      case charl of
        #"`" :: #"`" :: m => cont_lex acc buf "``" true false m
      | #"`" :: m         => cont_lex acc buf "`" true false m      
      | #"\"" :: m        => cont_lex acc buf "\"" false true m
      | _                 =>
        (
        if is_sml_symbol a 
         then  
           let 
             val (token, contl) = wait_char (not o is_sml_symbol) [] charl
           in
             hhs_lexer (token :: acc) [] false false contl
           end
         else if is_alphanumeric a 
         then  
           let 
             val (token, contl) = wait_char (not o is_alphanumeric) [] charl
           in
             hhs_lexer (token :: acc) [] false false contl
           end
         else raise ERR "hhs_lexer : unknown character: " (Char.toString a)
         )
    end  
and cont_lex acc buf s iq m = 
  let 
    val some_s = if s = "" then [] else [s]
    val some_buf = if buf = [] then [] else [implode (rev buf)]
  in
    hhs_lexer (some_s @ some_buf @ acc) [] iq m
  end

fun reg_tquote sl = case sl of
    [] => []
  | "``" :: a :: "``" :: m => ("``" ^ a ^ "``") :: reg_tquote m
  | "`" :: a :: "`" :: m   => ("`" ^ a ^ "`") :: reg_tquote m
  | "#" :: "\"" :: a :: "\"" :: m => ("#\"" ^ a ^ "\"") :: reg_tquote m
  | "\"" :: a :: "\"" :: m => ("\"" ^ a ^ "\"") :: reg_tquote m
  | "\"" :: "\"" :: m => ("\"" ^ "\"") :: reg_tquote m
  | a :: "." :: m => reg_dot [] sl
  | a :: m => a :: reg_tquote m
and reg_dot acc sl = case sl of
    [] => raise ERR "reg_dot" ""
  | a :: "." :: m => reg_dot ("." :: a :: acc) m
  | a :: m => (String.concat (rev (a :: acc))) :: reg_tquote m

fun hhs_lex_blank s =
  reg_tquote (hhs_lexer [] [] false false (explode s))

fun hhs_lex s = filter (not o is_blank_string) (hhs_lex_blank s)

(*---------------------------------------------------------------------------
   Removing comments
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

end (* struct *)
