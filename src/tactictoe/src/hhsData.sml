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

fun read_hhs thyname = 
  let 
    val file = hhs_record_dir ^ "/" ^ thyname ^ "HHS"
    val _ = hhs_read_list := []; 
    val _ = use file; 
    val r = !hhs_read_list
  in
    hhs_read_list := [];
    r
  end

fun read_hht thyname = 
  let 
    val file = hhs_record_dir ^ "/" ^ thyname ^ "HHT"
    val _ = hhs_read_list := []; 
    val _ = use file; 
    val r = !hht_read_list
  in
    hht_read_list := [];
    r
  end

fun read_hhs_error thyname =
  (
  read_hhs thyname
  handle Io _ => 
    (
    if mem thyname ["sat","bool","min","basicSize","integer_word"] 
    then () 
    else print ("  warning: read_hhs_error " ^ thyname)
    ;
    []
    )
  )

fun read_hht_error thyname =
  (
  read_hht thyname
  handle Io _ => 
    (
    if mem thyname ["sat","bool","min","basicSize","integer_word"] 
    then () 
    else print ("  warning: read_hht_error " ^ thyname)
    ;
    []
    )
  )

fun read_data thyl =
  let
    val l1 = map read_hhs_error thyl
    val l2 = map read_hht_error thyl
  in
    (List.concat l1, List.concat l2)
  end

end (* struct *)

