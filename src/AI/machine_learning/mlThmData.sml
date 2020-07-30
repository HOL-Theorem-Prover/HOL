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

type thmid = string
type thmdata = (int, real) Redblackmap.dict * (thmid * fea) list
val empty_thmdata = (dempty Int.compare,[])

(* -------------------------------------------------------------------------
   Artificial theory name for theorems from the namespace.
   Warning: conflict if a theory is named namespace_tag.
   ------------------------------------------------------------------------- *)

val namespace_tag = "namespace_tag"

(* -------------------------------------------------------------------------
   Namespace theorems
   ------------------------------------------------------------------------- *)

fun unsafe_namespace_thms () =
  let
    val l0 = #allVal (PolyML.globalNameSpace) ()
    val l1 = filter (is_thm_value l0) (map fst l0)
  in
    case thml_of_sml l1 of
      SOME l2 => combine (l1,l2)
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
      if mem a [namespace_tag] then b else s
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
    if mem a [namespace_tag]
    then []
    else List.mapPartial thmid_of_depid (depidl_of_thm (DB.fetch a b))
  end

(* -------------------------------------------------------------------------
   Theorem features
   ------------------------------------------------------------------------- *)

fun add_thmfea thy ((name,thm),(thmfea,symfreq,nodupl)) =
  let
    val g = dest_thm thm
    val thmid = thy ^ "Theory." ^ name
    val newnodupl = dadd g () nodupl
  in
    if not (dmem g nodupl) andalso uptodate_thm thm
    then
      let
        val fea = fea_of_goal_cached true g
        val newthmfea = (thmid,fea) :: thmfea
        val newsymfreq = count_dict symfreq fea
      in
        (newthmfea,newsymfreq,newnodupl)
      end
    else (thmfea,symfreq,newnodupl)
  end

fun add_thmfea_from_thy (thy,acc) =
  foldl (add_thmfea thy) acc (DB.thms thy)

fun thmfea_from_thyl thyl =
  foldl add_thmfea_from_thy ([], dempty Int.compare, dempty goal_compare) thyl

fun add_namespacethm acc =
  let val l = unsafe_namespace_thms () in
    foldl (add_thmfea namespace_tag) acc l
  end

val create_thmdata_time = ref 0.0

val create_thmdata_cache = ref (dempty (list_compare String.compare))

fun clean_create_thmdata_cache () =
  create_thmdata_cache := dempty (list_compare String.compare)

val add_cthy_time = ref 0.0
val add_namespace_time = ref 0.0
val thmdata_tfidf_time = ref 0.0

fun create_thmdata () =
  let
    val thy = current_theory ()
    val thyl = ancestry thy
    val acc1 =
      dfind thyl (!create_thmdata_cache) handle NotFound =>
      let val r = thmfea_from_thyl thyl in
        create_thmdata_cache := dadd thyl r (!create_thmdata_cache); r
      end
    val acc2 = total_time add_cthy_time add_thmfea_from_thy (thy,acc1)
    val (thmfea3,symfreq3,_) = total_time add_namespace_time
      add_namespacethm acc2
    val n = int_to_string (length thmfea3)
  in
    print_endline ("Loading " ^ n ^ " theorems");
    (total_time thmdata_tfidf_time
     (learn_tfidf_symfreq_nofilter (length thmfea3)) symfreq3, thmfea3)
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
            ["(","DB.fetch", mlquote thy, mlquote name,")"])
        end
      else NONE
    end
  else NONE


end (* struct *)
