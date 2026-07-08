(* ========================================================================= *)
(* FILE          : mlTacticData.sml                                          *)
(* DESCRIPTION   : Tactic calls from TacticToe recording                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTacticData :> mlTacticData =
struct

open HolKernel boolLib Abbrev aiLib smlLexer mlFeature

val ERR = mk_HOL_ERR "mlTacticData"

(* -------------------------------------------------------------------------
   Tactictoe database data type
   ------------------------------------------------------------------------- *)

type stac = string
type loc = string * int * int
type call = {stac : stac, ogl : int list, fea : fea}

val loc_compare = triple_compare String.compare Int.compare Int.compare
fun call_compare (c1,c2) =
  cpl_compare String.compare fea_compare
    ((#stac c1,#fea c1),(#stac c2,#fea c2))

type tacdata =
  {
  calld : (string * int * int, call) Redblackmap.dict,
  taccov : (stac,int) Redblackmap.dict,
  symfreq : (int,int) Redblackmap.dict
  }

val empty_tacdata : tacdata =
  {
  calld = dempty loc_compare,
  taccov = dempty String.compare,
  symfreq = dempty Int.compare
  }

val format_version = 3

(* -------------------------------------------------------------------------
   Exporting tactic data
   ------------------------------------------------------------------------- *)

fun loc_to_string (s,i1,i2) =
  String.concatWith " " [s, its i1, its i2]

fun ilts il = String.concatWith " " (map its il)

fun call_to_string (loc,{stac,ogl,fea}) =
  [loc_to_string loc, stac, ilts ogl, ilts fea]

fun export_calls file calls1 =
  let
    fun is_local stac = mem "tttRecord.local_tag" (partial_sml_lexer stac)
    fun test call = not (is_local (#stac call))
    val calls2 = filter (test o snd) calls1
    val _ = debug ("export_calls: " ^ its (length calls2) ^ " filtered calls")
  in
    writel_atomic file (List.concat (map call_to_string calls2))
  end

fun export_tacdata thy file tacdata =
  let
    fun test (x,_,_) = (x = thy)
    val calls = filter (test o fst) (dlist (#calld tacdata))
  in
    print_endline ("Exporting tactic data to: " ^ file);
    export_calls file calls
  end

(* -------------------------------------------------------------------------
   Importing tactic data
   ------------------------------------------------------------------------- *)

fun loc_from_string s =
  let val (a,b,c) = triple_of_list (String.tokens Char.isSpace s) in
    (a, string_to_int b, string_to_int c)
  end

fun string_to_il s = map string_to_int (String.tokens Char.isSpace s)

fun call_from_string (s1,s2,s3,s4) =
  (loc_from_string s1,
   {stac = s2, ogl = string_to_il s3, fea = string_to_il s4})

fun import_calls file =
  let val l = mk_batch_full 4 (readl_empty file) in
    map (call_from_string o quadruple_of_list) l
  end

fun init_taccov calls =
  count_dict (dempty String.compare) (map (#stac o snd) calls)

fun init_symfreq calls =
  count_dict (dempty Int.compare) (List.concat (map (#fea o snd) calls))

fun init_tacdata calls =
  {
  calld = dnew loc_compare calls,
  taccov = init_taccov calls,
  symfreq = init_symfreq calls
  }

fun import_tacdata filel =
  let val calls = List.concat (map import_calls filel) in
    init_tacdata calls
  end

(* -------------------------------------------------------------------------
   Tactictoe database management
   ------------------------------------------------------------------------- *)

val ttt_tacdata_dir = tactictoe_cache_dir ^ "/ttt_tacdata"
fun ttt_tacdata_dir_of () = current_tactictoe_cache_dir () ^ "/ttt_tacdata"
fun ttt_tacdata_data_dir_of () = ttt_tacdata_dir_of () ^ "/data"
val ttt_tacdata_file_override = ref (NONE : string option)

type provenance = {format_hash : string, global_hash : string, hol_hash : string}

type manifest_entry =
  { thy : string, data_sha256 : string, src_sha256 : string,
    anc_version : int, recorded_at : int, failed : bool,
    format_hash : string, global_hash : string, hol_hash : string }

type manifest =
  { format_version : int, format_hash : string, global_hash : string,
    hol_hash : string, entries : manifest_entry list }

fun safe_sha256_file file = if exists_file file then sha256_file file else ""

fun find_script thy =
  let val dir =
    Binarymap.find(fileDirMap(),thy ^ "Theory.sml")
    handle NotFound => raise ERR "find_script" ("please load " ^ thy ^ "Theory")
  in
    dir ^ "/" ^ thy ^ "Script.sml"
  end

fun ttt_ancestry thy =
  filter (fn x => not (mem x ["min","bool"])) (sort_thyl (ancestry thy))

fun source_hash thy = safe_sha256_file (find_script thy)

fun global_srcs () =
  ["src/AI/machine_learning/mlFeature.sml",
   "src/AI/sml_inspection/smlLexer.sml",
   "src/AI/sml_inspection/smlParser.sml",
   "src/tactictoe/src/tttToken.sml",
   "src/tactictoe/src/tttRecord.sml",
   "src/tactictoe/src/tttUnfold.sml",
   "src/AI/machine_learning/mlTacticData.sml",
   "src/AI/machine_learning/mlThmData.sml",
   "src/tactictoe/src/tttLearn.sml",
   "src/AI/sml_inspection/infix_file.sml",
   "bin/hol.state0"]

fun global_hash () =
  let
    fun h rel = rel ^ " " ^ safe_sha256_file (HOLDIR ^ "/" ^ rel)
  in
    sha256_string (String.concatWith "\n" (map h (global_srcs ())) ^ "\n")
  end

fun current_provenance () =
  { format_hash =
      safe_sha256_file (HOLDIR ^ "/src/AI/machine_learning/mlTacticData.sml"),
    global_hash = global_hash (),
    hol_hash = safe_sha256_file (HOLDIR ^ "/bin/hol.state0") }

fun int_of_string s =
  case Int.fromString s of
    SOME i => i
  | NONE => raise ERR "int_of_string" s

fun identity_hash thy src anc (prov : provenance) =
  sha256_string (String.concatWith "\n"
    ["thy=" ^ thy,
     "src_sha256=" ^ src,
     "anc_version=" ^ its anc,
     "format_hash=" ^ #format_hash prov,
     "global_hash=" ^ #global_hash prov,
     "hol_hash=" ^ #hol_hash prov] ^ "\n")

fun tacdata_file_of_identity thy src anc prov =
  ttt_tacdata_data_dir_of () ^ "/" ^ thy ^ "-" ^ identity_hash thy src anc prov

fun current_tacdata_file thy =
  tacdata_file_of_identity thy (source_hash thy) (length (ttt_ancestry thy))
    (current_provenance ())

fun manifest_file () = ttt_tacdata_dir_of () ^ "/MANIFEST"

fun parse_manifest_line line (m : manifest) =
  let val tok = String.tokens Char.isSpace line in
    case tok of
      [] => m
    | a :: _ =>
      if String.isPrefix "#" a then m else
      case tok of
        ["format",v,h] =>
          {format_version = int_of_string v, format_hash = h,
           global_hash = #global_hash m, hol_hash = #hol_hash m,
           entries = #entries m}
      | ["global",h] =>
          {format_version = #format_version m, format_hash = #format_hash m,
           global_hash = h, hol_hash = #hol_hash m, entries = #entries m}
      | ["hol"] =>
          {format_version = #format_version m, format_hash = #format_hash m,
           global_hash = #global_hash m, hol_hash = "", entries = #entries m}
      | ["hol",h] =>
          {format_version = #format_version m, format_hash = #format_hash m,
           global_hash = #global_hash m, hol_hash = h, entries = #entries m}
      | ["thy",thy,data,src,anc,t] =>
          let
            val recorded_at = int_of_string t
            val entry = {thy = thy, data_sha256 = data, src_sha256 = src,
                         anc_version = int_of_string anc,
                         recorded_at = recorded_at,
                         failed = data = "failed" orelse recorded_at < 0,
                         format_hash = #format_hash m,
                         global_hash = #global_hash m,
                         hol_hash = #hol_hash m}
          in
            {format_version = #format_version m, format_hash = #format_hash m,
             global_hash = #global_hash m, hol_hash = #hol_hash m,
             entries = entry :: #entries m}
          end
      | ["thy",thy,data,src,anc,t,fmt,glob,hol] =>
          let
            val recorded_at = int_of_string t
            val entry = {thy = thy, data_sha256 = data, src_sha256 = src,
                         anc_version = int_of_string anc,
                         recorded_at = recorded_at,
                         failed = data = "failed" orelse recorded_at < 0,
                         format_hash = fmt, global_hash = glob, hol_hash = hol}
          in
            {format_version = #format_version m, format_hash = #format_hash m,
             global_hash = #global_hash m, hol_hash = #hol_hash m,
             entries = entry :: #entries m}
          end
      | _ => raise ERR "parse_manifest_line" line
  end

fun read_manifest_full () =
  if not (exists_file (manifest_file ())) then NONE else
  let
    val empty = {format_version = ~1, format_hash = "", global_hash = "",
                 hol_hash = "", entries = []}
    val m = foldl (fn (line,m) => parse_manifest_line line m)
      empty (readl (manifest_file ()))
  in
    if #format_version m < 0 then NONE
    else SOME {format_version = #format_version m, format_hash = #format_hash m,
               global_hash = #global_hash m, hol_hash = #hol_hash m,
               entries = rev (#entries m)}
  end
  handle _ => NONE

fun same_identity thy src anc (prov : provenance) (e : manifest_entry) =
  #thy e = thy andalso #src_sha256 e = src andalso #anc_version e = anc andalso
  #format_hash e = #format_hash prov andalso
  #global_hash e = #global_hash prov andalso
  #hol_hash e = #hol_hash prov

fun entry_file (e : manifest_entry) =
  let
    val prov = {format_hash = #format_hash e, global_hash = #global_hash e,
                hol_hash = #hol_hash e}
  in
    tacdata_file_of_identity (#thy e) (#src_sha256 e) (#anc_version e) prov
  end

fun tacdata_file_for_thy thy =
  let
    val src = source_hash thy
    val anc = length (ttt_ancestry thy)
    val prov = current_provenance ()
    val current_file = tacdata_file_of_identity thy src anc prov
  in
    case read_manifest_full () of
      NONE => if exists_file current_file then SOME current_file else NONE
    | SOME m =>
      case List.find (same_identity thy src anc prov) (#entries m) of
        NONE => if exists_file current_file then SOME current_file else NONE
      | SOME e =>
        let val file = entry_file e in
          if #failed e then NONE
          else if exists_file file andalso safe_sha256_file file = #data_sha256 e
          then SOME file
          else NONE
        end
  end handle _ => NONE

fun exists_tacdata_thy thy = isSome (tacdata_file_for_thy thy)

fun create_tacdata () =
  let
    val thyl = ancestry (current_theory ())
    val resolved = map (fn thy => (thy, tacdata_file_for_thy thy)) thyl
    val filel = List.mapPartial (fn (_,SOME file) => SOME file | _ => NONE)
      resolved
    val thyl2 = List.mapPartial (fn (thy,NONE) => SOME thy | _ => NONE)
      resolved
    val thyl3 = filter (fn x => not (mem x ["bool","min"])) thyl2
    val _ = if null thyl3 then () else
      (
      print_endline ("Missing tactic data: " ^  String.concatWith " " thyl3);
      print_endline "Run tttUnfold.ttt_record ()"
      )
    val (tacdata,t) = add_time import_tacdata filel
    val calln = dlength (#calld tacdata)
  in
    print_endline ("Loading " ^ its calln ^ " tactic calls in " ^
      rts_round 2 t ^ " seconds");
    tacdata
  end

fun ttt_update_tacdata ((loc,call),{calld,taccov,symfreq}) =
  {
  calld = dadd loc call calld,
  taccov = count_dict taccov [#stac call],
  symfreq = count_dict symfreq (#fea call)
  }

fun ttt_export_tacdata thy tacdata =
  let
    val dir = ttt_tacdata_data_dir_of ()
    val _ = mkDir_err dir
    val file = case !ttt_tacdata_file_override of
        SOME file => file
      | NONE => current_tacdata_file thy
  in
    export_tacdata thy file tacdata
  end


end (* struct *)
