(* ========================================================================= *)
(* FILE          : smlPrettify.sml                                           *)
(* DESCRIPTION   : Prettify SML strings                                      *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlPrettify :> smlPrettify =
struct

open HolKernel Abbrev boolLib Tactical aiLib smlTimeout smlLexer smlExecute

val ERR = mk_HOL_ERR "smlPrettify"

(*---------------------------------------------------------------------------
  Removing unnecessary parentheses
  ----------------------------------------------------------------------------*)

fun elim_par sl = case sl of
    [] => []
  | ["(",a,")"] => [a]
  | ["(","(",a,")",")"] => [a]
  | "(" :: a :: ")" :: m => a :: elim_par m
  | "(" :: "(" :: a :: ")" :: ")" :: m => a :: elim_par m
  | a :: m => a :: elim_par m

(*----------------------------------------------------------------------------
  Remove infix guards
  ----------------------------------------------------------------------------*)

fun is_infix_open s =
  String.isPrefix "sml_infix" s andalso
  String.isSuffix "open" s

fun is_infix_close s =
  String.isPrefix "sml_infix" s andalso
  String.isSuffix "close" s

fun elim_infix sl = case sl of
    [] => []
  | a :: b :: c :: m =>
    if is_infix_open a andalso is_infix_close c
    then b :: elim_infix m
    else a :: elim_infix (b :: c :: m)
  | a :: m => a :: elim_infix m

(*----------------------------------------------------------------------------
  Removing structure prefixes
  ----------------------------------------------------------------------------*)

fun drop_struct long =
  let
    val l = String.tokens (fn x => x = #".") long
    val short = last l
  in
    if length l = 1 orelse not (is_pointer_eq long short) then long else short
  end

fun elim_struct sl = map drop_struct sl

(* -------------------------------------------------------------------------
   Prettify theorems
   ------------------------------------------------------------------------- *)

fun elim_dbfetch sl = case sl of
    [] => []
  | ["DB.fetch",a,b] =>
    ((
    if unquote_string a = current_theory ()
    then ["DB.fetch",a,b]
    else [unquote_string a ^ "Theory." ^ unquote_string b]
    )
    handle _ => ["DB.fetch",a,b])
  | "DB.fetch" :: a :: b :: m =>
    ((
    if unquote_string a = current_theory ()
    then ["DB.fetch",a,b]
    else [unquote_string a ^ "Theory." ^ unquote_string b]
    )
    handle _ => ["DB.fetch",a,b])
    @
    elim_dbfetch m
  | a :: m => a :: elim_dbfetch m

(* -------------------------------------------------------------------------
   Requoting terms
   ------------------------------------------------------------------------- *)

fun is_quoted s = String.sub (s,0) = #"\""
  handle Interrupt => raise Interrupt | _ => false

fun requote sl = case sl of
   [] => []
  | "[" :: "QUOTE" :: s :: "]" :: m =>
    if is_quoted s
    then ("`" ^ rm_space (rm_comment (rm_squote s)) ^ "`") :: requote m
    else hd sl :: requote (tl sl)
  | "Term" :: "[" :: "QUOTE" :: s :: "]" :: m =>
    if is_quoted s
    then ("``" ^ rm_space (rm_comment (rm_squote s)) ^ "``") :: requote m
    else hd sl :: requote (tl sl)
  | a :: m => a :: requote m

(* -------------------------------------------------------------------------
   Concatenate tokens with smart spaces
   ------------------------------------------------------------------------- *)

fun smart_space sl = case sl of
    [] =>  ""
  | [a] => a
  | a :: b :: m =>
    (
    if mem a ["[","("] orelse mem b ["]",")",",",";"]
    then a ^ smart_space (b :: m)
    else a ^ " " ^ smart_space (b :: m)
    )


end (* struct *)
