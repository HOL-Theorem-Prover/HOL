(* ========================================================================== *)
(* FILE          : hhsMetis.sml                                               *)
(* DESCRIPTION   :                                                            *)
(*                                                                            *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsMetis :> hhsMetis =
struct

open HolKernel boolLib Abbrev hhsTools hhsExec hhsLexer hhsFeature hhsPredict
hhsSetup

val ERR = mk_HOL_ERR "hhsMetis"

(* --------------------------------------------------------------------------
   Metis: 
   Todo: Orthogonalization could be done during predictions but would
   be a bit slow.
   -------------------------------------------------------------------------- *)

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

fun mk_metis_call sl =
  "metisTools.METIS_TAC " ^ 
  "[" ^ String.concatWith " , " (map dbfetch_of_string sl) ^ "]"

(* very slow: since thmknn_std is slow *)
fun metis_provable n tim g =
  !hhs_metisexec_flag andalso
  let
    val sl   = thmknn_std n g
    val stac = mk_metis_call sl
    val tac  = tactic_of_sml stac
    val glo  = app_tac tim tac g
  in
    glo = SOME []
  end

(* --------------------------------------------------------------------------
   Metis dictionary input/output.
   -------------------------------------------------------------------------- *)

fun read_thmfea s = case hhs_lex s of
    a :: "T" :: m => 
    (dest_thm (thm_of_string a), (a, true, map string_to_int m))
  | a :: "F" :: m => 
    (dest_thm (thm_of_string a), (a, false, map string_to_int m))
  | _ => raise ERR "read_thmfea" s
    
fun readthy_mdict thy =
  let
    val l0 = readl (hhs_mdict_dir ^ "/" ^ thy)
      handle _ => (if mem thy ["min"] then () else debug thy; [])
    val l1 = map read_thmfea l0
  in
    hhs_mdict := daddl l1 (!hhs_mdict)
  end

fun import_mdict () = app readthy_mdict (ancestry (current_theory ()))

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm

fun order_thml thml =
  let fun compare ((_,th1),(_,th2)) =
    Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
  in
    dict_sort compare thml
  end

fun is_localthy s = s = "local_namespace_holyhammer"

fun update_mdict cthy =
  let
    val thml = DB.thms cthy
    fun f (s,thm) =
      let 
        val name = cthy ^ "Theory." ^ s
        val goal = dest_thm thm
        val fea = #3 (dfind goal (!hhs_mdict)) 
          handle _ => fea_of_goal goal
        val b = #2 (dfind goal (!hhs_mdict)) 
          handle _ => not (metis_trivial 0.1 goal)
      in
        hhs_mdict := dadd goal (name, b, fea) (!hhs_mdict)
      end
  in
    app f thml
  end
  
fun export_mdict cthy = 
  let 
    val _ = update_mdict cthy
    val namel = map fst (DB.thms cthy)
    fun in_curthy (_,(s,_,_)) =  
      let val (thy,name) = split_string "Theory." s in
        thy = cthy andalso mem name namel
      end
    val fname = hhs_mdict_dir ^ "/" ^ cthy
    val l0 = filter in_curthy (dlist (!hhs_mdict))
    fun f (_,(name,b,fea)) = 
      String.concatWith " " (name :: string_of_bool b :: map int_to_string fea)
    val l1 = map f l0
  in 
    writel fname l1
  end
 

end
