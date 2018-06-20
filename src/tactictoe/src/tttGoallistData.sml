(* ========================================================================== *)
(* FILE          : tttGoallistData.sml                                        *)
(* DESCRIPTION   :                                                            *)
(*                                                                            *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttGoallistData :> tttGoallistData =
struct

open HolKernel boolLib Abbrev tttTools tttExec tttLexer tttFeature tttPredict
tttSetup

val ERR = mk_HOL_ERR "tttGoallistData"

(*----------------------------------------------------------------------------
 * Export
 *----------------------------------------------------------------------------*)

fun export_glfea cthy =
  let
    val file = ttt_glfea_dir ^ "/" ^ cthy
    val l = dlist (!ttt_glfea_cthy)
    fun f (fea,(b,n)) =
      String.concatWith " "
        (int_to_string n :: (if b then "T" else "F") :: map int_to_string fea)
  in
    writel file (map f l)
  end

(*----------------------------------------------------------------------------
 * Import
 *----------------------------------------------------------------------------*)

fun init_glfea fea (b,n) =
  let val b' = fst (dfind fea (!ttt_glfea)) handle _ => false in
    if b' then () else ttt_glfea := dadd fea (b,n) (!ttt_glfea)
  end

fun read_glfea thy =
  let
    val file = ttt_glfea_dir ^ "/" ^ thy
    val l = readl file handle _ => (debug ("import_glfea " ^ thy); [])
    fun f s = case String.tokens Char.isSpace s of
        a :: "T" :: m =>
        init_glfea (map string_to_int m) (true, string_to_int a)
      | b :: "F" :: m =>
        init_glfea (map string_to_int m) (false, string_to_int b)
      | _ => raise ERR "read_gl" thy
  in
    app f l
  end

fun import_glfea thyl = app read_glfea thyl

(*----------------------------------------------------------------------------
 * Update
 *----------------------------------------------------------------------------*)

fun update_glfea fea (b,n) =
  if (fst (dfind fea (!ttt_glfea)) handle _ => false) then () else
  (
  ttt_glfea := dadd fea (b,n) (!ttt_glfea);
  ttt_glfea_cthy := dadd fea (b,n) (!ttt_glfea_cthy)
  )

end (* struct *)
