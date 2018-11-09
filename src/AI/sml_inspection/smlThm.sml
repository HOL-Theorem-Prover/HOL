(* ========================================================================= *)
(* FILE          : smlThm.sml                                                *)
(* DESCRIPTION   : Manipulating string representation of theorems            *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure smlThm :> smlThm =
struct

open HolKernel boolLib anotherLib smlLexer smlExecute smlRedirect mlFeature

val ERR = mk_HOL_ERR "smlThm"

(* -------------------------------------------------------------------------
   Artificial theory name for theorems from the namespace.
   Warning: conflict if a theory is named namespace_tag.
   ------------------------------------------------------------------------- *)

val namespace_tag = "namespace_tag"

(* -------------------------------------------------------------------------
   Namespace theorems
   ------------------------------------------------------------------------- *)

fun string_of_pretty p =
  let
    val acc = ref []
    fun f s = acc := s :: !acc
  in
    PolyML.prettyPrint (f,80) p;
    String.concatWith " " (rev (!acc))
  end

fun smltype_of_value l s =
  let
    val v = assoc s l handle _ => raise ERR "type_of_value" s
    val t = PolyML.NameSpace.Values.typeof v;
    val p = PolyML.NameSpace.Values.printType (t,0,NONE)
  in
    string_of_pretty p
  end

fun is_thm_value l s =
  let
    val s1 = smltype_of_value l s
    val s2 = smlLexer.partial_sml_lexer s1
  in
    case s2 of
      [a] => (drop_sig a = "thm" handle _ => false)
    | _   => false
  end

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

fun dbfetch_of_sthm s =
  let val (a,b) = split_string "Theory." s in
    if a = current_theory ()
      then String.concatWith " " ["DB.fetch",mlquote a,mlquote b]
    else
      if a = namespace_tag then b else s
  end

fun mk_metis_call sl =
  "metisTools.METIS_TAC " ^
  "[" ^ String.concatWith " , " (map dbfetch_of_sthm sl) ^ "]"

(* -------------------------------------------------------------------------
   Theorem features: live database shared by TacticToe and HolyHammer
   ------------------------------------------------------------------------- *)

val goalfea_cache = ref (dempty goal_compare)

fun clean_goalfea_cache () = goalfea_cache := dempty goal_compare

fun fea_of_goal_cached g = 
  dfind g (!goalfea_cache) handle NotFound =>
  let val fea = feahash_of_goal g in
    goalfea_cache := dadd g fea (!goalfea_cache); fea
  end

fun add_thmfea ((name,thm),(thmfeadict,nodupl)) =
  let val g = dest_thm thm in
    if not (dmem g nodupl) andalso uptodate_thm thm
    then (dadd name (g, fea_of_goal_cached g) thmfeadict, dadd g () nodupl)
    else (thmfeadict,nodupl)
  end

fun add_thmfea_from_thy (thy,(thmfeadict,nodupl)) =
  foldl add_thmfea (thmfeadict,nodupl) (DB.thms thy)
    
fun thmfea_from_thyl thyl = 
  foldl add_thmfea_from_thy (dempty String.compare, dempty goal_compare) thyl

fun add_namespacethm (thmfeadict,nodupl) =
  let
    fun f (x,y) = (namespace_tag ^ "Theory." ^ x, y)
    val l1 = hide_out unsafe_namespace_thms ()
    val l2 = map f l1
  in
    foldl add_thmfea (thmfeadict,nodupl) l2
  end



(* should include dependencies maybe *)
fun create_thmdata () =
  let
    val thyl = current_theory () :: ancestry (current_theory ())
    val (d0,nodupl) = thmfea_from_thyl thyl
    val (d1,_) = add_namespacethm (d0,nodupl)
    val is = int_to_string (dlength d1)
    val feav = map (fn (a,(b,c)) => (a,c)) (dlist d1)
  in
    print_endline ("Loading " ^ is ^ " theorems ");
    (learn_tfidf feav ,feav)
  end

(* -------------------------------------------------------------------------
   Named
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

fun thml_of_namel sl = hide_out (List.mapPartial thm_of_name) sl



end (* struct *)
