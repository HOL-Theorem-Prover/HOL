(* ===================================================================== *)
(* FILE          : hhsData.sml                                           *)
(* DESCRIPTION   : Storing feature vectors                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhsData :> hhsData =
struct

open HolKernel boolLib hhsLexer hhsTools hhsLog

val ERR = mk_HOL_ERR "hhsData"

(* ----------------------------------------------------------------------
   Read feature vectors from disk.
   ---------------------------------------------------------------------- *)
val hhs_read_list = ref []
val hht_read_list = ref []
val hhs_cat_dir = HOLDIR ^ "/src/tactictoe/in"

fun cmd_in_dir dir cmd =
  OS.Process.system ("cd " ^ dir ^ "; " ^ cmd);

fun hhs_recname thyname = hhs_record_dir ^ "/" ^ thyname ^ "HHS"
fun hht_recname thyname = hhs_record_dir ^ "/" ^ thyname ^ "HHT"

fun read_data thyl =
  let
    val out = hhs_cat_dir ^ "/record"
    val out_error = hhs_cat_dir ^ "/record_error"
    val hhsl = String.concatWith " " (map hhs_recname thyl)
    val hhtl = String.concatWith " " (map hht_recname thyl)
    val head = hhs_record_dir ^ "/" ^ "a_head"
    val foot = hhs_record_dir ^ "/" ^ "a_foot"
    val cmd = 
      String.concatWith " " ["cat",head,hhsl,hhtl,foot,">",out,"2>",out_error]
    val _ = OS.Process.system cmd
    val _ = use out
    val r = (!hhs_read_list, !hht_read_list)
  in
    hhs_read_list := [];
    hht_read_list := [];
    r
  end

end (* struct *)
