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
   Set of theorems available for theorem predictions.
   local.theorems.
   
   Set of theorems available in tactics.
   
   Make a list of local tactic and do not export them. loctacdict
   
   Add namespace theorems to a list of theorems. 
   A theorem should just be referenced by a string?.  
   -------------------------------------------------------------------------- *)

(* fun add_internal_theorems thmfeav = *)
  

(* --------------------------------------------------------------------------
   Internal theorems

load "hhsExec";
open hhsExec;







load "hhsMetis";
open hhsMetis;
import_mdict ();

fun goal_of_string s =
  let val (a,b) = split_string "Theory." s in dest_thm (DB.fetch a b) end

val goaldict = 
  let 
    val l = dlist (!hhs_mdict)
    fun f (name,_) = (goal_of_string name, ())
  in
    dnew goal_compare (mapfilter f l) 
  end






fun ex_thm thm = dmem (dest_thm thm) goaldict;
fun is_term term thm = concl thm = term;

val l2 = map lift_thm l1;
val l3 = filter (not o is_trivthm) l2;
val l4 = filter (not o ex_thm) l3;

-------------------------------------------------------------------------- *)


(* --------------------------------------------------------------------------
   Metis
   -------------------------------------------------------------------------- *)

fun parfetch_of_string s =
  let val (a,b) = split_string "Theory." s in 
    if a = current_theory ()
    then String.concatWith " " ["(","DB.fetch",mlquote a,mlquote b,")"] 
    else s
  end

fun mk_metis_call sl =
  "metisTools.METIS_TAC " ^ 
  "[" ^ String.concatWith " , " (map dbfetch_of_string sl) ^ "]"
  
fun metis_provable n tim goal =
  let
    val sl   = thmknn_std n goal
    val stac = mk_metis_call sl
    val tac  = tactic_of_sml stac
    val glo  = app_tac tim tac goal
  in
    glo = SOME []
  end

(* --------------------------------------------------------------------------
   Metis dictionary input/output.
   -------------------------------------------------------------------------- *)

fun read_thmfea s = case hhs_lex s of
    a :: "T" :: m => (a,(true, map string_to_int m))
  | a :: "F" :: m => (a,(false, map string_to_int m))
  | _ => raise ERR "read_thmfea" s
    
fun readthy_mdict thy =
  if mem thy ["min","bool"] then () else
  let
    val l0 = readl (hhs_mdict_dir ^ "/" ^ thy) handle _ => (debug thy;[])
    val l1 = map read_thmfea l0
  in
    hhs_mdict := daddl l1 (!hhs_mdict)
  end

fun import_mdict () = app readthy_mdict (ancestry (current_theory ()))

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm

fun order_thml thml =
  let
    fun compare ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
  in
    dict_sort compare thml
  end

fun update_mdict cthy =
  let
    val thml = order_thml (DB.thms cthy) (* try oldest first *)
    fun f (s,thm) =
      let 
        val name = cthy ^ "Theory." ^ s
        val goal = dest_thm thm
      in
        if dmem name (!hhs_mdict) then () else 
          let val b =
            !hhs_thmortho_flag andalso 
            metis_provable (!hhs_metis_npred) (!hhs_metis_time) goal
          in
            hhs_mdict := dadd name (not b, fea_of_goal goal) (!hhs_mdict)
          end
      end
  in
    app f thml
  end
  
fun export_mdict cthy = 
  let 
    val _ = update_mdict cthy
    val namel = map fst (DB.thms cthy)
    (* test if these theorems still exists in the current theory *)
    fun test (s,_) =  
      let val (thy,name) = split_string "Theory." s in
        thy = cthy andalso mem name namel
      end
    val fname = hhs_mdict_dir ^ "/" ^ cthy
    val l0 = filter test (dlist (!hhs_mdict))
    fun f (name,(b,fea)) = 
      String.concatWith " " (name :: string_of_bool b :: map int_to_string fea)
    val l1 = map f l0
  in 
    writel fname l1
  end 
 

end
