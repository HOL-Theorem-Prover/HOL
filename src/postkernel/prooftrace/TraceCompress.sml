(* TraceCompress: compression/decompression for .pft trace files.

   Encapsulates tool selection, compression after recording,
   transparent decompression on read, and file discovery.
*)

structure TraceCompress :> TraceCompress =
struct

val ERR = Feedback.mk_HOL_ERR "TraceCompress"

(* ------- Tool configuration ------- *)

datatype tool = Zstd | Gzip | Zip | NoCompression

fun extension Zstd = ".zst"
  | extension Gzip = ".gz"
  | extension Zip  = ".zip"
  | extension NoCompression = ""

fun compress_cmd Zstd path = "zstd --rm -q " ^ path
  | compress_cmd Gzip path = "gzip -q " ^ path
  | compress_cmd Zip  path = "zip -jmq " ^ path ^ ".zip " ^ path
  | compress_cmd NoCompression _ = ""

fun decompress_cmd Zstd src dst = "zstd -dcq " ^ src ^ " > " ^ dst
  | decompress_cmd Gzip src dst = "gzip -dcq " ^ src ^ " > " ^ dst
  | decompress_cmd Zip  src dst = "unzip -p " ^ src ^ " > " ^ dst
  | decompress_cmd NoCompression _ _ = ""

fun tool_binary Zstd = "zstd"
  | tool_binary Gzip = "gzip"
  | tool_binary Zip  = "zip"
  | tool_binary NoCompression = ""

(* All compression extensions to probe, in preference order *)
val all_extensions = [".zst", ".gz", ".zip"]

(* Parse HOL_PFT_COMPRESS env var *)
fun parse_tool_name s =
  case String.map Char.toLower s of
    "zstd" => SOME Zstd
  | "gzip" => SOME Gzip
  | "gz"   => SOME Gzip
  | "zip"  => SOME Zip
  | "none" => SOME NoCompression
  | ""     => NONE  (* use default *)
  | _      => (Feedback.HOL_WARNING "TraceCompress" "init"
                 ("Unknown compression tool: " ^ s ^ ", using zstd");
               NONE)

(* Selected tool, resolved at load time. Verified on first use. *)
val active_tool : tool ref = ref NoCompression
val tool_verified : bool ref = ref false

val _ =
  let
    val requested = case OS.Process.getEnv "HOL_PFT_COMPRESS" of
                      NONE => NONE
                    | SOME s => parse_tool_name s
  in active_tool := (case requested of
                       SOME t => t
                     | NONE => Zstd)
  end

(* On first compress call, verify the tool works by checking
   exit code. If it fails, disable compression. *)
fun get_tool () =
  let val tool = !active_tool
  in if tool = NoCompression then NoCompression
     else if !tool_verified then tool
     else
       let val bin = tool_binary tool
           val ok = OS.Process.isSuccess
                      (OS.Process.system
                         (bin ^ " --version >/dev/null 2>&1"))
                    handle _ => false
       in tool_verified := true;
          if ok then tool
          else (Feedback.HOL_WARNING "TraceCompress" "compress"
                  (bin ^ " not found, compression disabled");
                active_tool := NoCompression;
                NoCompression)
       end
  end

(* ------- Temp file tracking for cleanup ------- *)

(* Cache: base_path -> decompressed temp path.
   Avoids re-decompressing when the same file is opened
   multiple times (e.g., MergeTrace's two-pass reading). *)
val decomp_cache : (string, string) Redblackmap.dict ref =
  ref (Redblackmap.mkDict String.compare)

(* All active temp files, for atExit cleanup *)
val active_temps : string list ref = ref []

val _ = OS.Process.atExit (fn () =>
  List.app (fn p => OS.FileSys.remove p handle _ => ())
           (!active_temps))

(* ------- Compress ------- *)

fun compress path =
  let val tool = get_tool ()
  in if tool = NoCompression then path
     else
       let val cmd = compress_cmd tool path
           val result = OS.Process.system cmd
       in if OS.Process.isSuccess result then
            path ^ extension tool
          else
            (* Compression failed — leave original *)
            (Feedback.HOL_WARNING "TraceCompress" "compress"
               ("compression failed, keeping uncompressed: " ^ path);
             path)
       end
  end

(* ------- Find trace file ------- *)

fun find_trace base_path =
  if OS.FileSys.access(base_path, [OS.FileSys.A_READ])
  then SOME base_path
  else
    let fun try_ext [] = NONE
          | try_ext (ext :: rest) =
              let val p = base_path ^ ext
              in if OS.FileSys.access(p, [OS.FileSys.A_READ])
                 then SOME p else try_ext rest
              end
    in try_ext all_extensions end

(* ------- Decompress and open ------- *)

(* Determine which tool compressed a file based on extension *)
fun tool_of_path path =
  if String.isSuffix ".zst" path then SOME Zstd
  else if String.isSuffix ".gz" path then SOME Gzip
  else if String.isSuffix ".zip" path then SOME Zip
  else NONE

fun open_trace base_path =
  case find_trace base_path of
    NONE => raise ERR "open_trace"
              ("trace file not found: " ^ base_path)
  | SOME actual_path =>
    case tool_of_path actual_path of
      NONE =>
        (* Uncompressed — open directly *)
        let val s = TextIO.openIn actual_path
        in (s, fn () => TextIO.closeIn s) end
    | SOME tool =>
        let
          (* Check cache; decompress if not cached or stale *)
          fun do_decompress () =
            let val t = OS.FileSys.tmpName ()
                val cmd = decompress_cmd tool actual_path t
            in if OS.Process.isSuccess (OS.Process.system cmd)
               then (decomp_cache :=
                       Redblackmap.insert(!decomp_cache,
                                          base_path, t);
                     active_temps := t :: !active_temps;
                     t)
               else (OS.FileSys.remove t handle _ => ();
                     raise ERR "open_trace"
                       ("decompression failed: " ^ actual_path))
            end
          val tmp = case Redblackmap.peek(!decomp_cache, base_path) of
              SOME cached =>
                if OS.FileSys.access(cached, [OS.FileSys.A_READ])
                then cached
                else do_decompress ()
            | NONE => do_decompress ()
          val s = TextIO.openIn tmp
        in
          (* Cleanup just closes the stream — temp file stays
             cached for potential re-read (MergeTrace two-pass).
             atExit handler removes all temps. *)
          (s, fn () => TextIO.closeIn s handle _ => ())
        end

(* ------- Suffixes for directory scanning ------- *)

val trace_suffixes =
  "Theory.pft" ::
  map (fn ext => "Theory.pft" ^ ext) all_extensions

end
