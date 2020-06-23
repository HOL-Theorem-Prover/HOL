(* ========================================================================= *)
(* FILE          : mlTacticData.sml                                          *)
(* DESCRIPTION   : Tactic calls from TacticToe recording                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTacticData :> mlTacticData =
struct

open HolKernel boolLib Abbrev SharingTables Portable aiLib smlLexer mlFeature

val ERR = mk_HOL_ERR "mlTacticData"

(* -------------------------------------------------------------------------
   Tactictoe database data type
   ------------------------------------------------------------------------- *)

type stac = string

type call = 
  {
  stac : stac, ortho : stac, nntm : term, time : real,
  ig : goal, ogl : goal list,
  loc : ((string * int) * string), 
  fea : fea
  }

fun call_compare (c1,c2) = 
  cpl_compare String.compare goal_compare 
    ((#ortho c1,#ig c1),(#ortho c2,#ig c2))

fun call_to_tuple {stac,ortho,nntm,time,ig,ogl,loc,fea} =
  ((stac,ortho,nntm,time),(ig,ogl),loc,fea)

fun tuple_to_call ((stac,ortho,nntm,time),(ig,ogl),loc,fea) =
  {
  stac = stac, ortho = ortho, nntm = nntm, time = time,
  ig = ig, ogl = ogl,
  loc = loc, 
  fea = fea
  }

type tacdata =
  {
  calls : call list,
  calls_cthy : call list,
  taccov : (stac, int) Redblackmap.dict,
  calldep : (goal, call list) Redblackmap.dict,
  symfreq : (int, int) Redblackmap.dict
  }

val empty_tacdata : tacdata =
  {
  calls = [],
  calls_cthy = [],
  taccov = dempty String.compare,
  calldep = dempty goal_compare,
  symfreq = dempty Int.compare
  }

(* -------------------------------------------------------------------------
   Check if data is up-to-date before export
   ------------------------------------------------------------------------- *)

fun uptodate_goal (asl,w) = all uptodate_term (w :: asl)
fun uptodate_call call = all uptodate_goal (#ig call :: #ogl call)

(* -------------------------------------------------------------------------
   Exporting terms
   ------------------------------------------------------------------------- *)

fun pp_tml tml =
  let
    val ed = {unnamed_terms = tml, named_terms = [], unnamed_types = [],
              named_types = [], theorems = []}
    val sdo = build_sharing_data ed
    val sexp = enc_sdata sdo
  in
    HOLsexp.printer sexp
  end

fun export_terml file tml =
  let
    val tml' = filter uptodate_term tml
    val _ = if length tml <> length tml'
            then print_endline "Warning: out-of-date terms are not exported"
            else ()
    val ostrm = Portable.open_out file
  in
    (PP.prettyPrint (curry TextIO.output ostrm, 75) (pp_tml tml');
     TextIO.closeOut ostrm)
  end

fun export_goal file (goal as (asl,w)) = export_terml file (w :: asl)

(* -------------------------------------------------------------------------
   Exporting tactic data
   ------------------------------------------------------------------------- *)

open HOLsexp

fun enc_goal enc_tm (asl,w) = list_encode enc_tm (w::asl)
fun dec_goal dec_tm =
  Option.map (fn (w,asl) => (asl,w)) o
  Option.mapPartial List.getItem o
  list_decode dec_tm

fun enc_goal_list enc_tm = list_encode (enc_goal enc_tm)
fun dec_goal_list dec_tm = list_decode (dec_goal dec_tm)
val enc_fea = Integer
val dec_fea = int_decode

fun enc_call enc_tm =
  tagged_encode "call" (
    pair4_encode (
      pair4_encode (String, String, enc_tm, String o Real.toString),
      pair_encode (enc_goal enc_tm, enc_goal_list enc_tm),
      pair_encode (pair_encode (String, Integer), String),
      list_encode enc_fea
    )
  )

fun dec_call dec_tm =
  tagged_decode "call" (
    pair4_decode (
      pair4_decode (string_decode, string_decode, dec_tm,
                    Option.mapPartial Real.fromString o string_decode),
      pair_decode (dec_goal dec_tm, dec_goal_list dec_tm),
      pair_decode (pair_decode (string_decode, int_decode), string_decode),
      list_decode dec_fea
    )
  )

fun enc_calls calls =
  let
    fun goal_terms ((asl,w),A) = (w::asl) @ A
    fun call_terms (call,A) = 
      List.foldl goal_terms A (
        ([],#3 (#1 call)) :: fst (#2 call) :: snd (#2 call)
      )
    val all_terms = List.foldl call_terms [] calls
    val ed = {named_terms = [], unnamed_terms = [], named_types = [],
              unnamed_types = [], theorems = []}
    val sdi = build_sharing_data ed
    val sdi = add_terms all_terms sdi
    fun write_term_aux sdi t = write_term sdi t
      handle NotFound => 
      (print_endline ("write_term: " ^ term_to_string t); 
       raise ERR "write_term" (term_to_string t))
    val enc_callsdata = list_encode (enc_call (String o write_term_aux sdi))
  in
    tagged_encode "calls" (pair_encode (enc_sdata, enc_callsdata)) (sdi,calls)
  end

fun dec_calls t =
  let
    val a = {with_strings = fn _ => (), with_stridty = fn _ => ()}
    val (sdo, calls) =
      valOf (tagged_decode "calls" (pair_decode (dec_sdata a, SOME)) t)
    val dec_tm = Option.map (read_term sdo) o string_decode
  in
    list_decode (dec_call dec_tm) calls
  end

fun export_calls file calls =
  let
    val ostrm = Portable.open_out file
    val _ = debug ("export_calls: " ^ its (length calls) ^ " calls")
    val calls1 = filter uptodate_call calls
    fun is_local stac = mem "tttRecord.local_tag" (partial_sml_lexer stac)
    fun test call = not (is_local (#ortho call))
    val calls2 = filter test calls1
    val calls3 = mk_sameorder_set call_compare (rev calls2)
    val calls4 = map call_to_tuple calls3
    val _ = debug ("export_calls: " ^ its (length calls3) ^ " filtered calls")
  in
    PP.prettyPrint (curry TextIO.output ostrm, 75)
                   (HOLsexp.printer (enc_calls calls4));
    TextIO.closeOut ostrm
  end

(* -------------------------------------------------------------------------
   Importing terms
   ------------------------------------------------------------------------- *)

fun import_terml file =
  let
    val t = HOLsexp.fromFile file
    val sdo = valOf (dec_sdata {with_strings = fn _ => (),
                                with_stridty = fn _ => ()} t)
  in
    #unnamed_terms (export_from_sharing_data sdo)
  end

fun import_goal file = let val l = import_terml file in (tl l, hd l) end

(* -------------------------------------------------------------------------
   Importing tactic data
   ------------------------------------------------------------------------- *)

fun import_calls file = 
  map tuple_to_call (valOf (dec_calls (HOLsexp.fromFile file)))

fun init_taccov calls =
  count_dict (dempty String.compare) (map #ortho calls)

fun init_symfreq calls =
  count_dict (dempty Int.compare) (List.concat (map #fea calls))

fun update_calldep (call,calldep) =
  let
    val oldl = dfind (#ig call) calldep handle NotFound => []
    val newl = call :: oldl
  in
    dadd (#ig call) newl calldep
  end

fun init_calldep calls =
  foldl update_calldep (dempty goal_compare) calls

fun init_tacdata calls =
  {
  calls      = calls,
  calls_cthy = [],
  calldep    = init_calldep calls,
  taccov     = init_taccov calls,
  symfreq    = init_symfreq calls
  }

fun import_tacdata filel =
  let val calls = List.concat (map import_calls filel) in
    init_tacdata calls
  end

fun export_tacdata file tacdata =
  (
  print_endline ("Exporting tactic data to: " ^ file);
  export_calls file (#calls_cthy tacdata)
  )

(* -------------------------------------------------------------------------
   Tactictoe database management
   ------------------------------------------------------------------------- *)

val ttt_tacdata_dir = HOLDIR ^ "/src/tactictoe/ttt_tacdata"

fun exists_tacdata_thy thy =
  let val file = ttt_tacdata_dir ^ "/" ^ thy in
    exists_file file andalso (not o null o readl) file
  end

fun create_tacdata () =
  let
    fun test file = exists_file file andalso (not o null o readl) file
    val thyl = ancestry (current_theory ())
    fun f x = ttt_tacdata_dir ^ "/" ^ x
    val filel = filter test (map f thyl)
    val thyl1 = map OS.Path.file filel
    val thyl2 = list_diff thyl thyl1
    val thyl3 = filter (fn x => not (mem x ["bool","min"])) thyl2
    val _ = if null thyl3 then () else
      (
      print_endline ("Missing tactic data: " ^  String.concatWith " " thyl3);
      print_endline "Run tttUnfold.ttt_record ()"
      )
    val _ = print_endline
    val tacdata = import_tacdata filel
  in
    print_endline ("Loading " ^ its (length (#calls tacdata)) ^
      " tactic calls");
    tacdata
  end

fun ttt_update_tacdata (call, {calls,calls_cthy,taccov,calldep,symfreq}) =
  {
  calls      = call :: calls,
  calls_cthy = call :: calls_cthy,
  calldep    = update_calldep (call,calldep),
  taccov     = count_dict taccov [#ortho call],
  symfreq    = count_dict symfreq (#fea call)
  }

fun ttt_export_tacdata thy tacdata =
  let
    val _ = mkDir_err ttt_tacdata_dir
    val file = ttt_tacdata_dir ^ "/" ^ thy
  in
    export_tacdata file tacdata
  end

(* ------------------------------------------------------------------------
   Export value examples
   ------------------------------------------------------------------------ *)

val enc_bool = String o bts
val dec_bool = Option.map string_to_bool o string_decode

fun enc_value enc_tm = pair_encode (enc_goal_list enc_tm, enc_bool)
fun dec_value dec_tm = pair_decode (dec_goal_list dec_tm, dec_bool)

fun enc_valuel valuel =
  let
    fun goal_terms ((asl,w),A) = (w::asl) @ A
    fun value_terms ((gl,_),A) = List.foldl goal_terms A gl
    val all_terms = List.foldl value_terms [] valuel
    val ed = {named_terms = [], unnamed_terms = [], named_types = [],
              unnamed_types = [], theorems = []}
    val sdi = build_sharing_data ed
    val sdi = add_terms all_terms sdi
    fun write_term_aux sdi t = write_term sdi t
      handle NotFound => 
      (print_endline ("write_term: " ^ term_to_string t); 
       raise ERR "write_term" (term_to_string t))
    val enc_valueldata = list_encode (enc_value (String o write_term_aux sdi))
  in
    tagged_encode "valuel" (pair_encode (enc_sdata, enc_valueldata))
      (sdi,valuel)
  end

fun dec_valuel t =
    let
      val a = {with_strings = fn _ => (), with_stridty = fn _ => ()}
      val (sdo, value_data) =
          valOf (tagged_decode "valuel" (pair_decode(dec_sdata a, SOME)) t)
      val dec_tm = Option.map (read_term sdo) o string_decode
    in
      list_decode (dec_value dec_tm) value_data
    end

fun uptodate_value (gl, _) = all uptodate_goal gl

fun ttt_export_value thmid valuel1 =
  let
    val dir = HOLDIR ^ "/src/tactictoe/value"
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ thmid
    val ostrm = Portable.open_out file
    val valuel2 = filter uptodate_value valuel1
    val _ = if length valuel1 <> length valuel2 
            then print_endline "warning: some goals were not up-to-date"
            else ()
  in
    PP.prettyPrint (curry TextIO.output ostrm, 75)
                   (HOLsexp.printer (enc_valuel valuel2));
    TextIO.closeOut ostrm
  end

fun ttt_import_value thmid =
  let
    val dir = HOLDIR ^ "/src/tactictoe/value"
    val file = dir ^ "/" ^ thmid
  in
    valOf (dec_valuel (HOLsexp.fromFile file))
  end

(* ------------------------------------------------------------------------
   Export policy
   ------------------------------------------------------------------------ *)

fun enc_policy enc_tm = 
  pair_encode (pair_encode (enc_goal enc_tm, enc_tm), enc_bool)
fun dec_policy dec_tm = 
  pair_decode (pair_decode (dec_goal dec_tm, dec_tm), dec_bool)

fun enc_policyl policyl =
  let
    fun policy_terms ((((asl,w),tm),_),A) = (tm :: w :: asl) @ A
    val all_terms = List.foldl policy_terms [] policyl
    val ed = {named_terms = [], unnamed_terms = [], named_types = [],
              unnamed_types = [], theorems = []}
    val sdi = build_sharing_data ed
    val sdi = add_terms all_terms sdi
    fun write_term_aux sdi t = write_term sdi t
      handle NotFound => 
      (print_endline ("write_term: " ^ term_to_string t); 
       raise ERR "write_term" (term_to_string t))
    val enc_policyldata = list_encode 
      (enc_policy (String o write_term_aux sdi))
  in
    tagged_encode "policyl" (pair_encode (enc_sdata, enc_policyldata))
      (sdi,policyl)
  end

fun dec_policyl t =
    let
      val a = {with_strings = fn _ => (), with_stridty = fn _ => ()}
      val (sdo, policy_data) =
        valOf (tagged_decode "policyl" (pair_decode (dec_sdata a, SOME)) t)
      val dec_tm = Option.map (read_term sdo) o string_decode
    in
      list_decode (dec_policy dec_tm) policy_data
    end

fun uptodate_policy ((g,stac), _) = uptodate_goal g

fun ttt_export_policy thmid policyl1 =
  let
    val dir = HOLDIR ^ "/src/tactictoe/policy"
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ thmid
    val ostrm = Portable.open_out file
    val policyl2 = filter uptodate_policy policyl1
    val _ = if length policyl1 <> length policyl2 
            then print_endline "warning: some goals were not up-to-date"
            else ()
  in
    PP.prettyPrint (curry TextIO.output ostrm, 75)
                   (HOLsexp.printer (enc_policyl policyl2));
    TextIO.closeOut ostrm
  end

fun ttt_import_policy thmid =
  let
    val dir = HOLDIR ^ "/src/tactictoe/policy"
    val file = dir ^ "/" ^ thmid
  in
    valOf (dec_policyl (HOLsexp.fromFile file))
  end


end (* struct *)
