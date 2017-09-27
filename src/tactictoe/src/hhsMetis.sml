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

val ERR = mk_HOL_ERR "hhsMetis"

val hhs_metis_flag  = ref false
val hhs_metis_time  = ref 0.1
val hhs_metis_npred = ref 16
val hhs_thmortho_flag = ref false
val hhs_stacpred_flag = ref false
val hh_stac_flag  = ref false (* predict dependencies using holyhammer *)

(* ----------------------------------------------------------------------
   Theorems dependencies
   ---------------------------------------------------------------------- *)

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm
  
fun depidl_of_thm thm =
  (Dep.depidl_of o Tag.dep_of o Thm.tag) thm   

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

val did_cache = ref (dempty (cpl_compare String.compare Int.compare))

fun load_did_cache thy =
  let
    val thml = DB.thms thy
    fun f (name,thm) = 
      let 
        val fullname = thy ^ "Theory." ^ name
        val n = depnumber_of_thm thm
      in
        did_cache := dadd (thy,n) fullname (!did_cache)
      end
  in
    app f thml  
  end 

fun thm_of_did (did as (thy,n)) =
  (
  dfind did (!did_cache) 
  handle _ => (load_did_cache thy; dfind did (!did_cache))
  )
  handle _ => raise ERR "thm_of_did" "Not found"

fun dependency_of_thm s =
  mapfilter thm_of_did (depidl_of_thm (thm_of_string s))

(* --------------------------------------------------------------------------
   Metis
   -------------------------------------------------------------------------- *)

fun dbfetch_of_string s =
  let val (a,b) = split_string "Theory." s in 
    if a = current_theory ()
    then String.concatWith " " ["DB.fetch",mlquote a,mlquote b] 
    else s
  end

fun parfetch_of_string s =
  let val (a,b) = split_string "Theory." s in 
    if a = current_theory ()
    then String.concatWith " " ["(","DB.fetch",mlquote a,mlquote b,")"] 
    else s
  end

fun mk_metis_call sl =
  "metisTools.METIS_TAC " ^ 
  "[" ^ String.concatWith ", " (map dbfetch_of_string sl) ^ "]"
  
fun solved_by_metis npred tim goal =
  let 
    val thmfeav = dlist (!mdict_glob)
    val thmsymweight = learn_tfidf thmfeav
    fun predictor x = 
      map fst (thmknn thmsymweight npred thmfeav (fea_of_goal x))
    val sl   = predictor goal
    val stac = mk_metis_call sl
    val glo  = (app_tac tim (tactic_of_sml stac)) goal
      handle _ => NONE
  in
    glo = SOME []
  end

(* --------------------------------------------------------------------------
   Theorems I/O + orthogonalization
   -------------------------------------------------------------------------- *)

fun read_thmfea s = case hhs_lex s of
    [] => raise ERR "read_thmfea" s
  | a :: m => (a, map string_to_int m)
    
fun readthy_mdict thy =
  if mem thy ["min","bool"] then () else
  let
    val l0 = readl (hhs_mdict_dir ^ "/" ^ thy) handle _ => (debug thy;[])
    val l1 = map read_thmfea l0
  in
    mdict_glob := daddl l1 (!mdict_glob)
  end

fun init_mdict () = app readthy_mdict (ancestry (current_theory ()))

fun order_thml thml =
  let
    fun compare ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
  in
    dict_sort compare thml
  end

fun update_mdict cthy =
  let
    val thml = order_thml (DB.thms cthy)
    fun f (s,thm) =
      let 
        val name = cthy ^ "Theory." ^ s
        val goal = dest_thm thm
      in
        if dmem name (!mdict_glob) orelse dmem name (!negmdict_glob)
        then ()
        else if
          (
          !hhs_thmortho_flag andalso !hhs_metis_flag andalso
          solved_by_metis (!hhs_metis_npred) (!hhs_metis_time) goal
          )
          then negmdict_glob := dadd name () (!negmdict_glob)
          else mdict_glob := dadd name (fea_of_goal goal) (!mdict_glob)
      end
  in
    app f thml
  end
  
fun export_mdict cthy = 
  let 
    val _ = update_mdict cthy
    val namel = map fst (DB.thms cthy)
    fun test (s,_) = 
      let val (thy,name) = split_string "Theory." s in
        thy = cthy andalso mem name namel
      end
    val fname = hhs_mdict_dir ^ "/" ^ cthy
    val l0 = filter test (dlist (!mdict_glob))
    fun f (name,fea) = String.concatWith " " (name :: map int_to_string fea)
    val l1 = map f l0
  in 
    writel fname l1
  end

(* ---------------------------------------------------------------------------
   Add a metis call with generated arguments on top of the predictions.
   -------------------------------------------------------------------------- *)

val stactime_dict = ref (dempty String.compare)

fun add_metis tacdict thmpredictor (g,pred) =
  if !hhs_metis_flag
  then
    let
      val stac = 
        if !hh_stac_flag
        then 
          (
          debug "calling holyhammer";
          case (!hh_stac_glob) g of 
            NONE => (debug "failure"; mk_metis_call ((!thmpredictor) g))
          | SOME x => (debug "success"; x)
          )
        else mk_metis_call ((!thmpredictor) g)
      val _ = stactime_dict := dadd stac (!hhs_metis_time) (!stactime_dict)
      val tac = tactic_of_sml stac
      val score = if null pred then 0.0 else snd (hd pred) 
    in
      tacdict := dadd stac tac (!tacdict);
      (g, ((stac,0.0,([],F),[]), score) :: pred)
    end
    handle _ => (g,pred)
  else (g,pred)


(* ---------------------------------------------------------------------------
   Add an accept call on top of the predictions.
   -------------------------------------------------------------------------- *)

val thml_glob = ref (dempty goal_compare)

fun init_thml_glob_aux thy =
  let
    val l = DB.thms thy
    fun f (name,thm) = 
      thml_glob := dadd (dest_thm thm) (thy ^ "Theory." ^ name) (!thml_glob)
  in
    app f l
  end
    
fun init_thml_glob () =
  let 
    val _ = thml_glob := dempty goal_compare
    val thyl = (current_theory () :: ancestry (current_theory ()))
  in
    app init_thml_glob_aux thyl
  end

fun add_accept tacdict (g,pred) =
  if dmem g (!thml_glob)
  then
    let
      val s = dfind g (!thml_glob)
      val stac = "Tactical.ACCEPT_TAC " ^ parfetch_of_string s
      val tac = tactic_of_sml stac
      val fake_lbl = (stac,0.0,([],F),[])
      val score = 0.0
    in
      tacdict := dadd stac tac (!tacdict);
      (g, (fake_lbl,score) :: pred)
    end
    handle _ => (g,pred)
  else (g,pred) 
  
(* ---------------------------------------------------------------------------
   Premise selection for other tactics
   -------------------------------------------------------------------------- *)  

val addpred_flag = ref false

val thm_cache = ref (dempty String.compare)

fun is_thm_cache s =
  dfind s (!thm_cache) handle _ => 
    let val b = is_thm s in
      thm_cache := dadd s b (!thm_cache);
      b
    end 
  

fun addpred thml l  = case l of
    [] => []
  | "[" :: m => 
    let 
      val (el,m) = split_level "]" m
      val e = fst (split_level "," el) handle _ => el
    in
      (
      if not (null thml) andalso is_thm_cache (String.concatWith " " e)
      then 
        (
        addpred_flag := true; 
        ["["] @ el @ [","] @ [String.concatWith "," thml] @ ["]"]
        )
      else ["["] @ el @ ["]"]
      )
      @
      addpred thml m
    end
  | a :: m   => a :: addpred thml m

fun install_stac tacdict stac =
  if !addpred_flag then
    let 
      val tac = hhsTimeout.timeOut 1.0 tactic_of_sml stac handle e => 
      (debug ("Error: addpred:" ^ stac); raise e)
    in
      tacdict := dadd stac tac (!tacdict)
    end
  else ()

(* doesn't work with the empty list *)
fun addpred_stac tacdict thmpredictor (g,pred) =
  if !hhs_stacpred_flag then
    let 
      val (al,bl) = part_n 10 pred
      val sl = map dbfetch_of_string ((!thmpredictor) g)
      fun change_entry (lbl,score) =
        let
          val _ = addpred_flag := false
          val stac = #1 lbl
          val new_stac = String.concatWith " " (addpred sl (hhs_lex stac))
          val _ = install_stac tacdict new_stac handle _ =>
                  addpred_flag := false
          val fake_lbl = 
            (if !addpred_flag then new_stac else stac,0.0,([],F),[])
          val _ =
            if !addpred_flag 
            then debug (stac ^ " ==>\n  " ^ new_stac)
            else ()
        in
          (fake_lbl,score)
        end
    in
      (g,map change_entry al @ bl)
    end
  else (g,pred) 
  
(* 
val thml = ["arithmeticTheory.SUB_ADD"];

val stac = "METIS_TAC [arithmeticTheory.SUB_ADD]";
val l = hhsLexer.hhs_lex stac;

val new_stac = String.concatWith " " (addpred thml l);
*)

  
end
