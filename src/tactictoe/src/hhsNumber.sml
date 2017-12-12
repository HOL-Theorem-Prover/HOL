(* ========================================================================== *)
(* FILE          : hhsNumber.sml                                              *)
(* DESCRIPTION   : Tagging each SML token with a number                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)


structure hhsNumber :> hhsNumber =
struct

open HolKernel boolLib hhsTools hhsLexer

val ERR = mk_HOL_ERR "hhsNumber"

(*---------------------------------------------------------------------------
 *  Tokens
 *---------------------------------------------------------------------------*)

(* either real numbers or already prefixed *)
fun contain_dot s = mem #"." (explode s)

(*---------------------------------------------------------------------------
 * Number tokens of a string
 *---------------------------------------------------------------------------*)

val hhs_fst = fst

fun number_token n s =
  hhs_lex ("(hhsNumber.hhs_fst ( " ^ s ^ "," ^ int_to_string n ^ "))")

fun number_tokenl n sl =
  if sl = [] then [] else
  let val (a,m) = (hd sl,tl sl) in
    if mem a ["|","of","handle","fn"] then
      let val (head,cont) = split_level "=>" m in
        (a :: head) @ ["=>"] @ number_tokenl n cont
      end
    else if mem a ["val","fun","structure"] then
      let val (head,cont) = split_level "=" m in   
        (a :: head) @ ["="] @ number_tokenl n cont
      end 
    else if contain_dot a
      then (number_token n a) @ number_tokenl (n + 1) m
    else a :: number_tokenl n m
  end

fun number_stac s =
  String.concatWith " " (number_tokenl 0 (hhs_lex s))

(*---------------------------------------------------------------------------
 * Drop numbering
 *---------------------------------------------------------------------------*)

fun drop_numbering sl = case sl of
   "(" :: "hhsNumber.hhs_fst" :: "(" :: v :: "," :: n :: ")" :: ")" :: m =>
    v :: drop_numbering m
  | "hhsNumber.hhs_fst" :: "(" :: v :: "," :: n :: ")" :: m =>
    v :: drop_numbering m
  | a :: m => a :: drop_numbering m
  | []  => []

(*---------------------------------------------------------------------------
 * Use the numbering for replacing at a certain point in a string list
 *---------------------------------------------------------------------------*)

fun prefix l1 l2 = case (l1,l2) of
    ([],r) => r
  | (_,[]) => raise ERR "prefix" ""
  | (a1 :: m1, a2 :: m2) =>
    if a1 = a2
    then prefix m1 m2
    else raise ERR "prefix" ""

fun replace_at (l1,lrep) l2 = case l2 of
    []       => raise ERR "replace_at" (String.concatWith " " l1)
  | a2 :: m2 =>
    (
    let val r = prefix l1 l2 in lrep @ r end
    handle _ => (a2 :: replace_at (l1,lrep) m2)
    )

end (* struct *)
