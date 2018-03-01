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

(* --------------------------------------------------------------------------
   Metis dictionary input/output. Precomputing features of theorems. 
   -------------------------------------------------------------------------- *)

fun read_thmfea s = case hhs_lex s of
    a :: m => (SOME (dest_thm (thm_of_string a), (a, map string_to_int m)) handle _ => NONE)
  | _ => raise ERR "read_thmfea" s
    
fun readthy_mdict thy =
  let
    val l0 = readl (hhs_mdict_dir ^ "/" ^ thy)
      handle _ => (if mem thy ["min","bool"] then () else debug thy; [])
    val l1 = List.mapPartial read_thmfea l0
  in
    hhs_mdict := daddl l1 (!hhs_mdict)
  end

fun import_mdict () = 
  app readthy_mdict (ancestry (current_theory ()))

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm

fun order_thml thml =
  let fun compare ((_,th1),(_,th2)) =
    Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
  in
    dict_sort compare thml
  end

fun update_mdict cthy =
  let
    val thml = DB.thms cthy
    fun f (s,thm) =
      let 
        val name = cthy ^ "Theory." ^ s
        val goal = dest_thm thm
        val fea = snd (dfind goal (!hhs_mdict)) 
          handle _ => fea_of_goal goal
      in
        hhs_mdict := dadd goal (name,fea) (!hhs_mdict)
      end
  in
    app f thml
  end
  
fun export_mdict cthy = 
  let 
    val _ = update_mdict cthy
    val namel = map fst (DB.thms cthy)
    fun in_curthy (_,(s,_)) =  
      let val (thy,name) = split_string "Theory." s in
        thy = cthy andalso mem name namel
      end
    val fname = hhs_mdict_dir ^ "/" ^ cthy
    val l0 = filter in_curthy (dlist (!hhs_mdict))
    fun f (_,(name,fea)) = 
      String.concatWith " " (name :: map int_to_string fea)
    val l1 = map f l0
  in 
    writel fname l1
  end

end
