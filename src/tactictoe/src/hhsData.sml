(* ========================================================================== *)
(* FILE          : hhsData.sml                                                *)
(* DESCRIPTION   : Storing feature vectors                                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsData :> hhsData =
struct

open HolKernel boolLib Abbrev hhsTools hhsTimeout hhsExec hhsPredict

val ERR = mk_HOL_ERR "hhsData"

val data_glob = ref []
val data2_glob = ref []

(*----------------------------------------------------------------------------
 * Orthogonalization
 *----------------------------------------------------------------------------*)

val hhs_ortho_flag = ref false

(* should move hhs_tactic_time to tools *)
fun is_better_lbl (_,t1,g1,gl1) (_,t2,g2,gl2) =  
  t1 < 0.02 andalso g1 = g2 andalso all (fn x => mem x gl2) gl1 

fun find_better_stac (lbl2 as (stac2,t2,g2,gl2)) stacl =
  if null stacl then lbl2 else
    let 
      val lbl1 =
        let 
          val stac1 = hd stacl
          val ((gl1,_),t1) = add_time (timeOut 0.2 (tactic_of_sml stac1)) g2 
        in
          (stac1,t1,g2,gl1)
        end
        handle _ => ("Error",100.0,g2,gl2) 
        (* 100.0 guarantees that it will not be better than original tactic *)
    in  
      if is_better_lbl lbl1 lbl2 
      then lbl1 
      else find_better_stac lbl2 (tl stacl)
    end  

fun ortho fea (lbl as (_,t,g,gl)) =
  let 
    val feavectl = stacknn_ext 20 (!hhs_stacfea) fea
    val stacl    = map (#1 o fst) feavectl
  in
    find_better_stac lbl stacl
  end

(*----------------------------------------------------------------------------
 * Saving feature vectors to disk.
 *----------------------------------------------------------------------------*)

fun mk_string_list sl = "[" ^ String.concatWith "," sl ^ "]"

fun readable_goal (asl,w) =
  "(" ^ mk_string_list (map Parse.minprint asl) ^ "," ^ Parse.minprint w ^ ")"

fun save_lbl (old_lbl as (stac2,t2,g2,gl2)) =
  if mem g2 gl2 
    then ()
    else
      let
        val fea = hhsFeature.fea_of_goal g2
        val (lbl1 as (stac,t,g,gl)) = 
          if !hhs_ortho_flag then ortho fea old_lbl else old_lbl
        val feav = (lbl1,fea)
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

val tactic_dir = hhs_feature_dir ^ "/tactic"

fun read_fea_aux thy =
  if mem thy ["min","bool"] then () else
  let
    val sl = readl (tactic_dir ^ "/" ^ thy) 
             handle _ => (print (thy ^ "\n"); [])
    val b =
      if sl = [] then true
      else
      hhsExec.exec_sml "data"
      ("hhsData.data_glob := " ^ mk_string_list sl ^ " @ (!hhsData.data_glob)")
  in
    if b then () else print (thy ^ "\n")
  end

fun read_fea thyl =
  (
  print "Reading feature vectors...\n";
  app read_fea_aux thyl;
  !data_glob
  )

(*----------------------------------------------------------------------------
 * Reading success rates from disk
 *----------------------------------------------------------------------------*)

val succrate_dir = tactictoe_dir ^ "/tactic_success"

fun read_succ_aux thy =
  if mem thy ["min","bool"] then () else
  let
    val sl = readl (succrate_dir ^ "/" ^ thy) 
             handle _ => (print (thy ^ "\n"); [])
    val b =
      if sl = [] 
        then true
        else
        hhsExec.exec_sml "data"
        ("hhsData.data2_glob := " ^ mk_string_list sl ^ 
        " @ (!hhsData.data2_glob)")
  in
    if b then () else print (thy ^ "\n")
  end

fun read_succ thyl =
  (
  print "Reading success rates...\n";
  app read_succ_aux thyl;
  !data2_glob
  )




end (* struct *)
