(* ========================================================================== *)
(* FILE          : hhsQuote.sml                                               *)
(* DESCRIPTION   : Transforming term quotation into strings                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsQuote :> hhsQuote =
struct

open HolKernel boolLib hhsTools

val ERR = mk_HOL_ERR "hhsQuote"

fun unquote file1 file2 =
  ignore 
  (OS.Process.system (HOLDIR ^ "/bin/unquote" ^ " " ^  file1 ^ " " ^ file2))

fun unquoteString s =
  let
    val file1 = tactictoe_dir ^ "/code/quoteString1"
    val file2 = tactictoe_dir ^ "/code/quoteString2"
  in
    writel file1 [s];
    unquote file1 file2;
    String.concatWith " " (readl file2)
  end

end
