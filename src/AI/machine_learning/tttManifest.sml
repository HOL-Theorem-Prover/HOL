(* ========================================================================= *)
(* FILE          : tttManifest.sml                                           *)
(* DESCRIPTION   : On-disk identity and manifest of TacticToe tactic data.   *)
(*                 Sole owner of the MANIFEST format: mlTacticData reads it  *)
(*                 to resolve a theory's data file, tttUnfold writes it when *)
(*                 recording.                                                *)
(* ========================================================================= *)

structure tttManifest :> tttManifest =
struct

open HolKernel boolLib Abbrev aiLib

val ERR = mk_HOL_ERR "tttManifest"

val format_version = 3
val tactictoe_version = 1
val manifest_format_version = 5

type provenance = {tacdata_version : int, tactictoe_version : int}

type entry =
  { thy : string, data_hash : string, src_hash : string,
    anc_version : int, anc_hash : string, recorded_at : int, failed : bool,
    tacdata_version : int, tactictoe_version : int }

type manifest =
  { tacdata_version : int, tactictoe_version : int, entries : entry list }

fun current_provenance () =
  {tacdata_version = format_version, tactictoe_version = tactictoe_version}

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

fun tacdata_dir () = !tactictoe_cache_dir ^ "/ttt_tacdata"
fun tacdata_data_dir () = tacdata_dir () ^ "/data"
fun manifest_file () = tacdata_dir () ^ "/MANIFEST"

(* -------------------------------------------------------------------------
   Theory identity
   ------------------------------------------------------------------------- *)

fun find_script thy =
  let val dir =
    Binarymap.find (fileDirMap (), thy ^ "Theory.sml")
    handle NotFound => raise ERR "find_script" ("please load " ^ thy ^ "Theory")
  in
    dir ^ "/" ^ thy ^ "Script.sml"
  end

(* A completed theory's ancestry cannot change, and sort_thyl topologically
   sorts it (calling ancestry once per ancestor), so memoize completed
   theories: the staleness scan asks for the same ancestries repeatedly.
   The current theory is a graph fringe whose ancestry can still grow. *)
val ancestry_cache = ref (dempty String.compare)

fun compute_ancestry thy =
  let val l = filter (fn x => not (mem x ["min","bool"]))
                (sort_thyl (ancestry thy))
  in l end

fun ttt_ancestry thy =
  if thy = current_theory () then compute_ancestry thy else
  dfind thy (!ancestry_cache) handle NotFound =>
  let val l = compute_ancestry thy
  in
    ancestry_cache := dadd thy l (!ancestry_cache); l
  end

fun ancestry_version thy = length (ttt_ancestry thy)

fun safe_sha1_file file = if exists_file file then sha1_file file else ""

fun source_hash thy = safe_sha1_file (find_script thy)

fun ancestry_hash thy =
  sha1_string (String.concatWith "\n"
    (map (fn anc => anc ^ "=" ^ source_hash anc) (ttt_ancestry thy)) ^ "\n")

fun identity_hash thy src anc anc_hash (prov : provenance) =
  sha1_string (String.concatWith "\n"
    ["thy=" ^ thy,
     "src_hash=" ^ src,
     "anc_version=" ^ its anc,
     "anc_hash=" ^ anc_hash,
     "tacdata_version=" ^ its (#tacdata_version prov),
     "tactictoe_version=" ^ its (#tactictoe_version prov)] ^ "\n")

fun tacdata_file_of_full_identity thy src anc anc_hash prov =
  tacdata_data_dir () ^ "/" ^ thy ^ "-" ^
    identity_hash thy src anc anc_hash prov

fun tacdata_file_of_identity thy src anc prov =
  tacdata_file_of_full_identity thy src anc (ancestry_hash thy) prov

fun current_tacdata_file thy =
  tacdata_file_of_identity thy (source_hash thy) (ancestry_version thy)
    (current_provenance ())

fun entry_file (e : entry) =
  tacdata_file_of_full_identity (#thy e) (#src_hash e) (#anc_version e)
    (#anc_hash e)
    {tacdata_version = #tacdata_version e,
     tactictoe_version = #tactictoe_version e}

(* -------------------------------------------------------------------------
   Reading and writing the manifest

   Line format (whitespace-separated, "#" introduces a comment):
     format    <manifest_format_version>
     tacdata   <tacdata_version>
     tactictoe <tactictoe_version>
     thy <thy> <data_hash> <src_hash> <anc> <anc_hash> <recorded_at>
         <tacdata_v> <ttt_v>
   ------------------------------------------------------------------------- *)

type partial =
  {manifest_version : int, tacdata_version : int, tactictoe_version : int,
   entries : entry list}

fun parse_line line (m : partial) : partial =
  case String.tokens Char.isSpace line of
    [] => m
  | a :: _ =>
    if String.isPrefix "#" a then m else
    case String.tokens Char.isSpace line of
      ["format",v] =>
        {manifest_version = string_to_int v,
         tacdata_version = #tacdata_version m,
         tactictoe_version = #tactictoe_version m, entries = #entries m}
    | ["tacdata",v] =>
        {manifest_version = #manifest_version m,
         tacdata_version = string_to_int v,
         tactictoe_version = #tactictoe_version m, entries = #entries m}
    | ["tactictoe",v] =>
        {manifest_version = #manifest_version m,
         tacdata_version = #tacdata_version m,
         tactictoe_version = string_to_int v, entries = #entries m}
    | ["thy",thy,data,src,anc,anc_hash,t,tacdata_v,tactictoe_v] =>
        let
          val recorded_at = string_to_int t
          val entry =
            {thy = thy, data_hash = data, src_hash = src,
             anc_version = string_to_int anc, anc_hash = anc_hash,
             recorded_at = recorded_at,
             failed = data = "failed" orelse recorded_at < 0,
             tacdata_version = string_to_int tacdata_v,
             tactictoe_version = string_to_int tactictoe_v}
        in
          {manifest_version = #manifest_version m,
           tacdata_version = #tacdata_version m,
           tactictoe_version = #tactictoe_version m,
           entries = entry :: #entries m}
        end
    | _ => raise ERR "parse_line" line

fun read_manifest () =
  if not (exists_file (manifest_file ())) then NONE else
  let
    val empty = {manifest_version = ~1, tacdata_version = ~1,
                 tactictoe_version = ~1, entries = []}
    val m = foldl (fn (line,m) => parse_line line m) empty
      (readl (manifest_file ()))
  in
    (* a manifest written by a different format version is not ours to
       interpret: report it as absent so everything re-records *)
    if #manifest_version m <> manifest_format_version then NONE
    else SOME {tacdata_version = #tacdata_version m,
               tactictoe_version = #tactictoe_version m,
               entries = rev (#entries m)}
  end
  handle Interrupt => raise Interrupt | _ => NONE

fun entry_compare (e1 : entry, e2 : entry) =
  list_compare String.compare
    ([#thy e1, #src_hash e1, its (#anc_version e1), #anc_hash e1,
      its (#tacdata_version e1), its (#tactictoe_version e1)],
     [#thy e2, #src_hash e2, its (#anc_version e2), #anc_hash e2,
      its (#tacdata_version e2), its (#tactictoe_version e2)])

fun manifest_lines (prov : provenance) entries =
  let
    fun line (e : entry) =
      String.concatWith " "
        ["thy", #thy e, #data_hash e, #src_hash e, its (#anc_version e),
         #anc_hash e, its (#recorded_at e), its (#tacdata_version e),
         its (#tactictoe_version e)]
  in
    ["# TacticToe tactic-data manifest. DO NOT EDIT by hand; managed by",
     "# ttt_record.",
     "format " ^ its manifest_format_version,
     "tacdata " ^ its (#tacdata_version prov),
     "tactictoe " ^ its (#tactictoe_version prov)] @
    map line (dict_sort entry_compare entries)
  end

fun write_manifest prov entries =
  (mkDir_err (tacdata_dir ());
   writel_atomic (manifest_file ()) (manifest_lines prov entries))

fun manifest_generation () = safe_sha1_file (manifest_file ())

(* -------------------------------------------------------------------------
   Entry lookup and construction
   ------------------------------------------------------------------------- *)

fun entry_matches (prov : provenance) src_hash thy (e : entry) =
  #thy e = thy andalso
  #src_hash e = src_hash andalso
  #anc_version e = ancestry_version thy andalso
  #anc_hash e = ancestry_hash thy andalso
  #tacdata_version e = #tacdata_version prov andalso
  #tactictoe_version e = #tactictoe_version prov

fun find_entry prov src_hash thy (m : manifest) =
  List.find (entry_matches prov src_hash thy) (#entries m)

fun same_slot (e1 : entry) (e2 : entry) =
  #thy e1 = #thy e2 andalso
  #src_hash e1 = #src_hash e2 andalso
  #anc_version e1 = #anc_version e2 andalso
  #anc_hash e1 = #anc_hash e2 andalso
  #tacdata_version e1 = #tacdata_version e2 andalso
  #tactictoe_version e1 = #tactictoe_version e2

fun update_entry entry entries =
  entry :: filter (fn e => not (same_slot e entry)) entries

fun now_unix () =
  IntInf.toInt (Time.toSeconds (Time.now ()))
  handle Interrupt => raise Interrupt | _ => 0

fun success_entry (prov : provenance) thy data_hash src_hash =
  {thy = thy, data_hash = data_hash, src_hash = src_hash,
   anc_version = ancestry_version thy, anc_hash = ancestry_hash thy,
   recorded_at = now_unix (),
   failed = false, tacdata_version = #tacdata_version prov,
   tactictoe_version = #tactictoe_version prov}

fun failed_entry (prov : provenance) thy src_hash =
  {thy = thy, data_hash = "failed", src_hash = src_hash,
   anc_version = ancestry_version thy, anc_hash = ancestry_hash thy,
   recorded_at = ~1, failed = true,
   tacdata_version = #tacdata_version prov,
   tactictoe_version = #tactictoe_version prov}

(* -------------------------------------------------------------------------
   Resolving a theory's tactic-data file
   ------------------------------------------------------------------------- *)

fun tacdata_file_for_thy_in man thy =
  let
    val src = source_hash thy
    val prov = current_provenance ()
    val current_file =
      tacdata_file_of_identity thy src (ancestry_version thy) prov
    fun unvalidated () =
      if exists_file current_file then SOME current_file else NONE
  in
    case man of
      NONE => unvalidated ()
    | SOME m =>
      case find_entry prov src thy m of
        NONE => unvalidated ()
      | SOME e =>
        let val file = entry_file e in
          if #failed e then NONE
          else if exists_file file andalso safe_sha1_file file = #data_hash e
          then SOME file
          else NONE
        end
  end
  handle Interrupt => raise Interrupt | _ => NONE

fun tacdata_file_for_thy thy = tacdata_file_for_thy_in (read_manifest ()) thy

end (* struct *)
