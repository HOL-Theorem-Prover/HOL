(* ========================================================================= *)
(* FILE          : mlThmData.sml                                             *)
(* DESCRIPTION   : Theorem data used by the nearest neighbor predictor       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure mlThmData :> mlThmData =
struct

open HolKernel boolLib aiLib smlLexer smlExecute smlRedirect mlFeature

val ERR = mk_HOL_ERR "mlThmData"

type thmdata =
  (int, real) Redblackmap.dict * (string, fea) Redblackmap.dict

val thmlintac_cthy = ref []
val thmlintac_flag = ref false

val empty_thmdata = (dempty Int.compare, dempty String.compare)

(* -------------------------------------------------------------------------
   Artificial theory name for theorems from the namespace.
   Warning: conflict if a theory is named namespace_tag.
   ------------------------------------------------------------------------- *)

val namespace_tag = "namespace_tag"
val thmlintac_tag = "thmlintac_tag"

(* -------------------------------------------------------------------------
   Namespace theorems
   ------------------------------------------------------------------------- *)

fun unsafe_namespace_thms () =
  let
    val l0 = #allVal (PolyML.globalNameSpace) ()
    val l1 = filter (is_thm_value l0) (map fst l0)
  in
    case thml_of_sml l1 of
      SOME l2 => l2
    | NONE => List.mapPartial thm_of_sml l1
  end

fun safe_namespace_thms () =
  let
    val l0 = #allVal (PolyML.globalNameSpace) ()
    val l1 = (map fst l0)
  in
    List.mapPartial thm_of_sml l1
  end

(* -------------------------------------------------------------------------
   Metis string
   ------------------------------------------------------------------------- *)

fun dbfetch_of_thmid s =
  let val (a,b) = split_string "Theory." s in
    if a = current_theory ()
      then String.concatWith " " ["DB.fetch", mlquote a, mlquote b]
    else
      if mem a [namespace_tag,thmlintac_tag] then b else s
  end

fun mk_metis_call sl =
  "metisTools.METIS_TAC " ^
  "[" ^ String.concatWith " , " (map dbfetch_of_thmid sl) ^ "]"

(* -------------------------------------------------------------------------
   Theorem dependencies
   ------------------------------------------------------------------------- *)

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm
  handle HOL_ERR _ => raise ERR "depnumber_of_thm" ""

fun depidl_of_thm thm =
  (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
  handle HOL_ERR _ => raise ERR "depidl_of_thm" ""

fun depid_of_thm thm =
  (Dep.depid_of o Tag.dep_of o Thm.tag) thm
  handle HOL_ERR _ => raise ERR "depidl_of_thm" ""

fun thmid_of_depid (thy,n) =
  let fun has_depnumber n (_,thm) = n = depnumber_of_thm thm in
    case List.find (has_depnumber n) (DB.thms thy) of
      SOME (name,_) =>
        if can (DB.fetch thy) name andalso uptodate_thm (DB.fetch thy name)
        then SOME (thy ^ "Theory." ^ name)
        else NONE
    | NONE => NONE
  end

fun intactdep_of_thm thm =
  let
    val l0 = depidl_of_thm thm
    val l1 = List.mapPartial thmid_of_depid l0
  in
    (length l0 = length l1, l1)
  end

fun validdep_of_thmid thmid =
  let val (a,b) = split_string "Theory." thmid in
    if mem a [namespace_tag, thmlintac_tag] 
    then []
    else List.mapPartial thmid_of_depid (depidl_of_thm (DB.fetch a b))
  end

(* -------------------------------------------------------------------------
   Theorem features
   ------------------------------------------------------------------------- *)

val goalfea_cache = ref (dempty goal_compare)

fun clean_goalfea_cache () = goalfea_cache := dempty goal_compare

fun fea_of_goal_cached g =
  dfind g (!goalfea_cache) handle NotFound =>
  let val fea = feahash_of_goal g in
    goalfea_cache := dadd g fea (!goalfea_cache); fea
  end

fun add_thmfea thy ((name,thm),(thmfeadict,nodupl)) =
  let 
    val g = dest_thm thm 
    val thmid = thy ^ "Theory." ^ name
    val newnodupl = dappend (g,thmid) nodupl
  in
    if not (dmem g nodupl) andalso uptodate_thm thm
    then (dadd thmid (fea_of_goal_cached g) thmfeadict, newnodupl)
    else (thmfeadict, newnodupl)
  end

fun add_thmfea_from_thy (thy,(thmfeadict,nodupl)) =
  foldl (add_thmfea thy) (thmfeadict,nodupl) (DB.thms thy)

fun thmfea_from_thyl thyl =
  foldl add_thmfea_from_thy (dempty String.compare, dempty goal_compare) thyl

fun add_namespacethm (thmfeadict,nodupl) =
  let val l = unsafe_namespace_thms () in
    foldl (add_thmfea namespace_tag) (thmfeadict,nodupl) l
  end

fun create_thmdata () =
  let
    val thyl = current_theory () :: ancestry (current_theory ())
    val (d,nodupl) = thmfea_from_thyl thyl
    val (thmfeadict,newnodupl) = add_namespacethm (d,nodupl)
    val thmfeadict' = 
      if !thmlintac_flag 
      then daddl (!thmlintac_cthy) thmfeadict
      else thmfeadict
    val n = int_to_string (dlength thmfeadict')
  in
    print_endline ("Loading " ^ n ^ " theorems");
    (learn_tfidf (dlist thmfeadict'), thmfeadict')
  end

(* -------------------------------------------------------------------------
   Convert theorem identifier to a theorem value (used by holyhammer)
   ------------------------------------------------------------------------- *)

fun in_namespace s = fst (split_string "Theory." s) = namespace_tag

fun thm_of_name s =
  if in_namespace s
  then (case thm_of_sml (snd (split_string "Theory." s)) of
      SOME (_,thm) => SOME (s,thm)
    | NONE => NONE)
  else
    let val (a,b) = split_string "Theory." s in
      SOME (s, DB.fetch a b)
    end

fun thml_of_namel sl = List.mapPartial thm_of_name sl

(* -------------------------------------------------------------------------
   Convert a theorem value to sml code.
   ------------------------------------------------------------------------- *)

fun dbfetch_of_depid thm =
  if can depid_of_thm thm then
    let
      val (thy,n) = depid_of_thm thm
      val thml = DB.thms thy
      val thmdict = dnew goal_compare (map (fn (a,b) => (dest_thm b,a)) thml)
      val goal = dest_thm thm
    in
      if dmem goal thmdict
      then
        let val name = dfind goal thmdict in
          SOME (String.concatWith " "
            ["(","DB.fetch",mlquote thy,mlquote name,")"])
        end
      else NONE
    end
  else NONE


end (* struct *)
