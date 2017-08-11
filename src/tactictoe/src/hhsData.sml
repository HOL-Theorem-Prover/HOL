(* ========================================================================== *)
(* FILE          : hhsData.sml                                                *)
(* DESCRIPTION   : Storing feature vectors                                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsData :> hhsData =
struct

open HolKernel boolLib Abbrev hhsTools hhsTimeout hhsExec hhsLearn

val ERR = mk_HOL_ERR "hhsData"

val feav_reader = ref []

(*----------------------------------------------------------------------------
 * Saving feature vectors to disk.
 *----------------------------------------------------------------------------*)

val feav_reader = ref []

fun mk_string_list sl = "[" ^ String.concatWith "," sl ^ "]"

fun readable_goal (asl,w) =
  "(" ^ mk_string_list (map Parse.minprint asl) ^ "," ^ Parse.minprint w ^ ")"

fun save_lbl (lbl0 as (stac0,t0,g0,gl0)) =
  if mem g0 gl0 then () else
    let
      val fea = hhsFeature.fea_of_goal g0
      val (lbl as (stac,t,g,gl)) = orthogonalize (lbl0,fea)
      val feav = (lbl,fea)
    in
      if exists (fn x => feav_compare (x,feav) = EQUAL) (!hhs_stacfea) 
      then () 
      else
        let 
          val s = "(" ^
                  "(" ^ 
                  mlquote stac ^ "," ^
                  Real.toString t ^ "," ^
                  readable_goal g ^ "," ^
                  mk_string_list (map readable_goal gl) ^ ")," ^
                  mk_string_list (map mlquote fea) ^
                  ")"
          val dir = current_theory ()
          
        in
        update_stacfea_ddict feav;
        export_feav s
        end
    end

(*----------------------------------------------------------------------------
 * Reading feature vectors from disk.
 *----------------------------------------------------------------------------*)

fun read_feav thy =
  if mem thy ["min","bool"] then () else
  let
    val sl = readl (hhs_tacfea_dir ^ "/" ^ thy) 
             handle _ => (print (thy ^ "\n"); [])
    val b =
      if sl = [] then true
      else
        hhsExec.exec_sml "data"
        ("hhsData.feav_reader := " ^ mk_string_list sl ^ 
          " @ (!hhsData.feav_reader)")
  in
    if b then () else print (thy ^ "\n")
  end

fun import_feav thyl = (app read_feav thyl; !feav_reader)


end (* struct *)
