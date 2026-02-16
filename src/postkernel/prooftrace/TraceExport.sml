(* TraceExport: serialize proof trace data to compressed .pftrace files.

   This module is NOT in the trust boundary. Its output is independently
   verified by replaying through the kernel (ReplayTrace.sml). Bugs here
   cause replay failure, not unsound theorems.

   Called by TraceRecord.export_hook when proof tracing is active.
   Reads temp files (steps + parents) written during kernel inference,
   performs backward reachability minimization, step dedup, type/term
   pruning, and writes a compressed .pftrace file.
*)

structure TraceExport :> TraceExport =
struct

open HolKernel

val ERR = mk_HOL_ERR "TraceExport"

val its = Int.toString

(* --- Configuration --- *)
val optimize = ref true   (* step dedup + type/term pruning *)
val bench_mode = ref false

(* --- Timing accumulators (only active when bench_mode = true) --- *)

val t_n_exports       = ref 0
val t_reachability_ms = ref 0
val t_raw_write_ms    = ref 0
val t_dedup_ms        = ref 0
val t_prune_ms        = ref 0
val t_opt_write_ms    = ref 0
val t_total_ms        = ref 0

fun timings () = {
  n_exports       = !t_n_exports,
  reachability_ms = !t_reachability_ms,
  raw_write_ms    = !t_raw_write_ms,
  dedup_ms        = !t_dedup_ms,
  prune_ms        = !t_prune_ms,
  opt_write_ms    = !t_opt_write_ms,
  total_ms        = !t_total_ms
}

fun reset_timings () = (
  t_n_exports := 0;
  t_reachability_ms := 0;
  t_raw_write_ms := 0;
  t_dedup_ms := 0;
  t_prune_ms := 0;
  t_opt_write_ms := 0;
  t_total_ms := 0)

(* Portable: Time.toMilliseconds returns LargeInt.int which Moscow ML
   lacks. Time.toReal is universally available. *)
fun time_to_ms t = Real.floor(Time.toReal t * 1000.0)

fun timed acc f =
  if !bench_mode then
    let val t0 = Timer.startRealTimer ()
        val result = f ()
        val elapsed = time_to_ms (Timer.checkRealTimer t0)
    in acc := !acc + elapsed; result end
  else f ()

fun checkpoint acc timer =
  if !bench_mode then
    acc := !acc + time_to_ms (Timer.checkRealTimer timer)
  else ()

type export_args = {
  thyname      : string,
  thy_parents  : string list,
  exports      : (string * thm) list,
  types        : hol_type list,
  terms        : term list,
  counter      : int,
  ext_cache    : (int, term list * term * string option) Redblackmap.dict,
  steps_path   : string,
  parents_path : string,
  thm_id       : thm -> int
}

(* -----------------------------------------------------------------------
   Helpers
   ----------------------------------------------------------------------- *)

fun count_lines path =
  let val instrm = TextIO.openIn path
      fun count n = case TextIO.inputLine instrm of
                      NONE => n | SOME _ => count (n + 1)
  in count 0 before TextIO.closeIn instrm end

fun read_parents path n =
  let val arr = Array.array (n, [] : int list)
      val instrm = TextIO.openIn path
      fun rd i = case TextIO.inputLine instrm of
          NONE => ()
        | SOME line =>
          let val ids = List.mapPartial Int.fromString
                          (String.tokens Char.isSpace line)
          in if i < n then Array.update(arr, i, ids) else ();
             rd (i + 1) end
  in rd 0; TextIO.closeIn instrm; arr end

fun mark_live parents base roots =
  let val n = Array.length parents
      val live = Array.array (n, false)
      fun mark gid =
        let val fp = gid - base in
          if fp < 0 orelse fp >= n then ()
          else if Array.sub(live, fp) then ()
          else (Array.update(live, fp, true);
                List.app mark (Array.sub(parents, fp)))
        end
  in List.app mark roots; live end

fun build_renumber live =
  let val n = Array.length live
      val remap = Array.array (n, ~1)
      val next = ref 0
  in Array.appi (fn (i, true) =>
       (Array.update(remap, i, !next); next := !next + 1)
     | _ => ()) live;
     (remap, !next)
  end

fun escape_string s =
  if CharVector.all (fn c => Char.isPrint c andalso c <> #" ") s
  then s
  else "\"" ^ String.translate
     (fn #"\"" => "\\\""
       | #"\\" => "\\\\"
       | #"\n" => "\\n"
       | c => if Char.ord c < 0x20
              then let val h = Int.fmt StringCvt.HEX (Char.ord c)
                   in "\\x" ^ (if size h = 1 then "0" ^ h else h) end
              else str c) s
       ^ "\""

(* Detect retired/old constant names: oldN->original_name<-old *)
fun decode_old_name name =
  if String.isPrefix "old" name andalso String.isSuffix "<-old" name then
    let val inner = String.substring(name, 3, size name - 3)
        val arrow_pos = Lib.index (fn c => c = #">") (String.explode inner)
        val orig = String.substring(inner, arrow_pos + 1,
                     size inner - arrow_pos - 1 - 5)
    in SOME orig end handle _ => NONE
  else NONE

fun build_type_map (types : hol_type list) =
  #1 (List.foldl (fn (ty, (m, i)) =>
    case Redblackmap.peek(m, ty) of
      SOME _ => (m, i + 1)
    | NONE => (Redblackmap.insert(m, ty, i), i + 1))
    (Redblackmap.mkDict Type.compare, 0) types)

fun build_term_map (terms : term list) =
  #1 (List.foldl (fn (tm, (m, i)) =>
    case Redblackmap.peek(m, tm) of
      SOME _ => (m, i + 1)
    | NONE => (Redblackmap.insert(m, tm, i), i + 1))
    (Redblackmap.mkDict Term.compare, 0) terms)

fun write_type_entry ty_lookup ostrm idx ty =
  if Type.is_vartype ty then
    TextIO.output(ostrm,
      "Y " ^ its idx ^ " V " ^ escape_string (Type.dest_vartype ty) ^ "\n")
  else
    let val {Thy, Tyop, Args} = Type.dest_thy_type ty
        val arg_ids = map ty_lookup Args
        val out_tyop = case decode_old_name Tyop of
                         SOME orig => orig | NONE => Tyop
    in TextIO.output(ostrm,
         "Y " ^ its idx ^ " O " ^ escape_string Thy ^ " " ^
         escape_string out_tyop ^
         (if null arg_ids then ""
          else " " ^ String.concatWith " " (map its arg_ids)) ^ "\n")
    end

fun write_term_entry ty_lookup tm_lookup ostrm idx tm =
  case Term.dest_term tm of
      Term.VAR (name, ty) =>
        TextIO.output(ostrm,
          "M " ^ its idx ^ " V " ^ escape_string name ^ " " ^
          its (ty_lookup ty) ^ "\n")
    | Term.CONST {Name, Thy, Ty} =>
        let val out_name = case decode_old_name Name of
                             SOME orig => orig | NONE => Name
        in TextIO.output(ostrm,
             "M " ^ its idx ^ " C " ^ escape_string Thy ^ " " ^
             escape_string out_name ^ " " ^ its (ty_lookup Ty) ^ "\n")
        end
    | Term.COMB (f, x) =>
        TextIO.output(ostrm,
          "M " ^ its idx ^ " A " ^
          its (tm_lookup f) ^ " " ^ its (tm_lookup x) ^ "\n")
    | Term.LAMB (v, b) =>
        TextIO.output(ostrm,
          "M " ^ its idx ^ " L " ^
          its (tm_lookup v) ^ " " ^ its (tm_lookup b) ^ "\n")

fun shell_quote s =
  "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"

(* -----------------------------------------------------------------------
   Compression: prefer zstd, fallback to gzip, then uncompressed.
   Compression is optional for portability (F2 review feedback).
   ----------------------------------------------------------------------- *)

datatype compress_mode = CM_ZSTD | CM_GZIP | CM_NONE

val compress_mode : compress_mode =
  let
    fun try_cmd cmd =
      let val p : (TextIO.instream, TextIO.outstream) Unix.proc =
            Unix.execute("/bin/sh", ["-c", cmd])
          val st = Unix.reap p
      in OS.Process.isSuccess st end
      handle _ => false
  in
    if try_cmd "echo x | zstd -c > /dev/null 2>/dev/null"
    then CM_ZSTD
    else if try_cmd "echo x | gzip > /dev/null 2>/dev/null"
    then CM_GZIP
    else CM_NONE
  end

fun compress_ext () = case compress_mode of
    CM_ZSTD => ".zst" | CM_GZIP => ".gz" | CM_NONE => ""

fun compress_cmd path = case compress_mode of
    CM_ZSTD => "zstd -c -q > " ^ path
  | CM_GZIP => "gzip > " ^ path
  | CM_NONE => raise ERR "compress_cmd" "no compressor"

(* -----------------------------------------------------------------------
   FNV-1a 64-bit hash for step deduplication
   ----------------------------------------------------------------------- *)

val fnv_offset = 0wxCBF29CE484222325 : Word64.word
val fnv_prime  = 0wx00000100000001B3 : Word64.word

fun fnv1a_byte (h, b) =
  Word64.*(Word64.xorb(h, Word64.fromInt b), fnv_prime)

fun fnv1a_string s =
  CharVector.foldl (fn (c,h) => fnv1a_byte(h, Char.ord c)) fnv_offset s

fun fnv1a_word64 (h, w) =
  let fun byte n =
        Word64.toInt(Word64.andb(Word64.>>(w, Word.fromInt(n*8)), 0wxFF))
  in fnv1a_byte(fnv1a_byte(fnv1a_byte(fnv1a_byte(
     fnv1a_byte(fnv1a_byte(fnv1a_byte(fnv1a_byte(h,
     byte 0), byte 1), byte 2), byte 3),
     byte 4), byte 5), byte 6), byte 7) end

(* -----------------------------------------------------------------------
   Main export function
   ----------------------------------------------------------------------- *)

fun export ({thyname, thy_parents, exports = all_thms,
             types, terms, counter, ext_cache,
             steps_path, parents_path, thm_id} : export_args) =
  let
    val n_file_lines = count_lines steps_path
    val _ = if n_file_lines = 0 then raise ERR "export" "no steps"
            else ()
    val n_parent_lines = count_lines parents_path
    val _ = if n_parent_lines <> n_file_lines then
              raise ERR "export"
                ("line count mismatch: steps=" ^ its n_file_lines ^
                 " parents=" ^ its n_parent_lines)
            else ()
    val base = counter - n_file_lines
    val t_export_start = Timer.startRealTimer ()
    val root_ids = map (fn (_, th) => thm_id th) all_thms
    val (parents, live, remap, n_live) = timed t_reachability_ms (fn () =>
      let val parents = read_parents parents_path n_file_lines
          val live = mark_live parents base root_ids
          val (remap, n_live) = build_renumber live
      in (parents, live, remap, n_live) end)

    (* Collect external IDs *)
    val ext_set = ref (Redblackset.empty Int.compare)
    val _ = Array.appi (fn (i, _) =>
      if Array.sub(live, i) then
        List.app (fn pid =>
          if pid < base then ext_set := Redblackset.add(!ext_set, pid)
          else ())
          (Array.sub(parents, i))
      else ()) live
    val _ = List.app (fn (_, th) =>
      let val tid = thm_id th
          val fp = tid - base
      in
        if fp < 0 orelse fp >= n_file_lines
        then ext_set := Redblackset.add(!ext_set, tid)
        else ()
      end) all_thms
    val ext_ids = Redblackset.listItems (!ext_set)
    val n_ext = length ext_ids

    val ty_map_local = build_type_map types
    val tm_map_local = build_term_map terms
    fun ty_lookup ty = case Redblackmap.peek(ty_map_local, ty) of
                         SOME id => id | NONE => ~1
    fun tm_lookup tm = case Redblackmap.peek(tm_map_local, tm) of
                         SOME id => id | NONE => ~1
    val n_types = length types
    val n_terms = length terms
    val objdir = ".hol/objs"
    val _ = (OS.FileSys.mkDir ".hol" handle OS.SysErr _ => ())
    val _ = (OS.FileSys.mkDir objdir handle OS.SysErr _ => ())
    val outname = objdir ^ "/" ^ thyname ^ "Theory.pftrace" ^ compress_ext ()

    (* Output abstraction: compressor pipe or direct file *)
    datatype out_handle =
        OH_PIPE of TextIO.outstream *
                   (TextIO.instream, TextIO.outstream) Unix.proc
      | OH_FILE of TextIO.outstream

    fun open_output path =
      case compress_mode of
        CM_NONE => OH_FILE (TextIO.openOut path)
      | _ =>
        let val p : (TextIO.instream, TextIO.outstream) Unix.proc =
              Unix.execute("/bin/sh",
                ["-c", compress_cmd (shell_quote path)])
        in OH_PIPE (Unix.textOutstreamOf p, p) end

    fun out_stream (OH_PIPE (s, _)) = s
      | out_stream (OH_FILE s) = s

    fun close_output (OH_PIPE (ostrm, p)) =
          let val _ = TextIO.closeOut ostrm
              val st = Unix.reap p
          in if not (OS.Process.isSuccess st)
             then raise ERR "export" "compressor failed"
             else ()
          end
      | close_output (OH_FILE s) = TextIO.closeOut s

    (* --- Parameterized trace writer --- *)
    fun write_body ostrm
        {step_count, step_offset,
         type_live_fn  : int -> bool,
         term_live_fn  : int -> bool,
         step_include  : int -> bool,
         step_outid    : int -> int,
         renumber      : int -> string,
         export_outid  : int -> int} =
      let
        val ext_rm =
          #1 (List.foldl (fn (eid, (m, next)) =>
                (Redblackmap.insert(m, eid, next), next + 1))
              (Redblackmap.mkDict Int.compare, step_offset) ext_ids)
        fun ren gid =
          let val fp = gid - base in
            if fp >= 0 andalso fp < n_file_lines then
              let val did = Array.sub(remap, fp) in
                if did >= 0 then renumber did else "?" ^ its gid
              end
            else case Redblackmap.peek(ext_rm, gid) of
                   SOME did => its did
                 | NONE => "?" ^ its gid
          end
      in
        TextIO.output(ostrm, "HOL4_PROOF_TRACE 1\n");
        TextIO.output(ostrm, "THEORY " ^ escape_string thyname ^ "\n");
        TextIO.output(ostrm, "PARENTS " ^
          String.concatWith " " (map escape_string thy_parents) ^ "\n");
        (* Best-effort ancestor digests (optional, skipped if no sha256sum) *)
        List.app (fn par =>
          let val pbase = objdir ^ "/" ^ par ^ "Theory.pftrace"
              val p = if OS.FileSys.access(pbase ^ ".zst", [])
                      then SOME (pbase ^ ".zst")
                      else if OS.FileSys.access(pbase ^ ".gz", [])
                      then SOME (pbase ^ ".gz")
                      else if OS.FileSys.access(pbase, [])
                      then SOME pbase
                      else NONE
          in
            case p of NONE => ()
            | SOME pf =>
              let
                val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
                  Unix.execute("/bin/sh",
                    ["-c", "sha256sum " ^ shell_quote pf])
                val line = TextIO.inputAll (Unix.textInstreamOf proc)
                val hash = hd (String.tokens Char.isSpace line)
                val _ = Unix.reap proc
              in
                TextIO.output(ostrm, "ANCESTOR " ^
                  escape_string par ^ " sha256:" ^ hash ^ "\n")
              end handle _ => ()
          end) thy_parents;
        TextIO.output(ostrm, "COUNTS " ^ its n_types ^ " " ^
          its n_terms ^ " " ^ its (step_count + n_ext) ^ "\n");
        TextIO.output(ostrm, "\n");

        (* Types *)
        ignore (List.foldl (fn (ty, i) =>
          (if type_live_fn i
           then write_type_entry ty_lookup ostrm i ty else ();
           i+1)) 0 types);
        TextIO.output(ostrm, "\n");

        (* Terms *)
        ignore (List.foldl (fn (tm, i) =>
          (if term_live_fn i
           then write_term_entry ty_lookup tm_lookup ostrm i tm else ();
           i+1)) 0 terms);
        TextIO.output(ostrm, "\n");

        (* Steps *)
        let val instrm = TextIO.openIn steps_path
            fun process fp =
              case TextIO.inputLine instrm of
                NONE => ()
              | SOME line =>
                (if fp < n_file_lines andalso Array.sub(live, fp) then
                   let val did = Array.sub(remap, fp) in
                     if step_include did then
                       let val sl = String.substring(line, 0, size line - 1)
                           val pids = Array.sub(parents, fp)
                           val rs = String.concatWith " " (map ren pids)
                       in TextIO.output(ostrm,
                            "P " ^ its (step_outid did) ^ " " ^ sl ^
                            (if null pids then "" else " | " ^ rs) ^
                            "\n")
                       end
                     else ()
                   end
                 else ();
                 process (fp + 1))
        in process 0; TextIO.closeIn instrm end;

        (* External (ancestor) theorem entries *)
        List.app (fn eid =>
          let val did = valOf (Redblackmap.peek(ext_rm, eid))
              val stmt =
                case Redblackmap.peek(ext_cache, eid) of
                  SOME (hyps, c, _) =>
                    let val c_id = tm_lookup c
                        val h_ids = map tm_lookup hyps
                    in " " ^ its c_id ^ " " ^
                       its (length h_ids) ^
                       (if null h_ids then ""
                        else " " ^ String.concatWith " "
                                     (map its h_ids))
                    end
                | NONE => ""
          in TextIO.output(ostrm,
               "P " ^ its did ^ " ORACLE DISK_THM" ^
               stmt ^ "\n")
          end) ext_ids;
        TextIO.output(ostrm, "\n");

        (* Exports *)
        List.app (fn (name, th) =>
          let val tid = thm_id th
              val fp = tid - base
              val oid =
                if fp >= 0 andalso fp < n_file_lines then
                  let val did = Array.sub(remap, fp) in
                    if did >= 0 then export_outid did
                    else raise ERR "export"
                           ("dead export: " ^ name ^ " (step not live)")
                  end
                else (case Redblackmap.peek(ext_rm, tid) of
                        SOME d => d
                      | NONE => raise ERR "export"
                           ("unmapped export: " ^ name))
          in TextIO.output(ostrm,
               "E " ^ escape_string name ^ " " ^ its oid ^ "\n")
          end) all_thms
      end

    (* === Phase 1: Write raw trace (always valid) === *)
    val _ = timed t_raw_write_ms (fn () =>
      let val oh1 = open_output outname
          val os1 = out_stream oh1
      in (write_body os1
               {step_count = n_live, step_offset = n_live,
                type_live_fn = fn _ => true,
                term_live_fn = fn _ => true,
                step_include = fn _ => true,
                step_outid = fn did => did,
                renumber = fn did => its did,
                export_outid = fn did => did};
             close_output oh1)
            handle e => (close_output oh1 handle _ => (); raise e)
      end)

    (* === Phase 2: Try optimized export (pruning + dedup) === *)
    val (n_final, n_deduped, n_live_types, n_live_terms) =
    if not (!optimize) then (n_live, 0, n_types, n_terms)
    else (let
       val t2_start = Timer.startRealTimer ()  (* bench_mode gated below *)
       val hash_arr = Array.array(n_live, fnv_offset)
       val dedup_to = Array.tabulate(n_live, fn i => i)
       val cmap = ref (Redblackmap.mkDict Word64.compare
                       : (Word64.word, (int * string * int list) list)
                         Redblackmap.dict)
       fun phash gid =
         let val fp = gid - base in
           if fp >= 0 andalso fp < n_file_lines then
             let val did = Array.sub(remap, fp) in
               if did >= 0 then Array.sub(hash_arr, did) else fnv_offset
             end
           else fnv1a_string (its gid)
         end

       fun find_equal _ _ [] = NONE
         | find_equal sl cpids ((did, csl, ccpids) :: rest) =
             if sl = csl andalso cpids = ccpids then SOME did
             else find_equal sl cpids rest

       val int_refs = let
         val refs = ref (Redblackset.empty Int.compare)
         val instrm = TextIO.openIn steps_path
         fun scan fp =
           case TextIO.inputLine instrm of
             NONE => ()
           | SOME line =>
             (if fp < n_file_lines andalso Array.sub(live, fp) then
                let val did = Array.sub(remap, fp)
                    val sl = String.substring(line, 0, size line - 1)
                    val toks = String.tokens Char.isSpace sl
                    fun collect [] = ()
                      | collect (t :: rest) =
                        (case Int.fromString t of
                           SOME n => refs := Redblackset.add(!refs, n)
                         | NONE => ();
                         collect rest)
                    val _ = collect
                              (case toks of _ :: rest => rest | _ => [])
                    val pids = Array.sub(parents, fp)
                    val cpids = map (fn gid =>
                      let val pfp = gid - base in
                        if pfp >= 0 andalso pfp < n_file_lines then
                          let val pdid = Array.sub(remap, pfp) in
                            if pdid >= 0
                            then Array.sub(dedup_to, pdid)
                            else gid
                          end
                        else gid
                      end) pids
                    val h = List.foldl (fn (gid, h) =>
                              fnv1a_word64(h, phash gid))
                              (fnv1a_string sl) pids
                    val bucket = case Redblackmap.peek(!cmap, h) of
                                   SOME bs => bs | NONE => []
                in
                  Array.update(hash_arr, did, h);
                  case find_equal sl cpids bucket of
                    SOME canon => Array.update(dedup_to, did, canon)
                  | NONE => cmap :=
                      Redblackmap.insert(!cmap, h,
                        (did, sl, cpids) :: bucket)
                end
              else ();
              scan (fp + 1))
       in scan 0; TextIO.closeIn instrm; !refs end

       val _ = checkpoint t_dedup_ms t2_start
       val t3_start = Timer.startRealTimer ()

       val output_id = Array.array(n_live, ~1)
       val n_unique = let val next = ref 0 in
         Array.appi (fn (i, _) =>
           if Array.sub(dedup_to, i) = i
           then (Array.update(output_id, i, !next); next := !next + 1)
           else ()) output_id;
         !next end
       val _ = Array.appi (fn (i, _) =>
         if Array.sub(dedup_to, i) <> i then
           Array.update(output_id, i,
             Array.sub(output_id, Array.sub(dedup_to, i)))
         else ()) output_id

       fun opt_outid did =
         Array.sub(output_id, Array.sub(dedup_to, did))

       (* Term/type pruning *)
       val all_refs = let
         val refs = ref int_refs
       in
         List.app (fn eid =>
           case Redblackmap.peek(ext_cache, eid) of
             SOME (hyps, c, _) =>
               (refs := Redblackset.add(!refs, tm_lookup c);
                List.app (fn h =>
                  refs := Redblackset.add(!refs, tm_lookup h)) hyps)
           | NONE => ()) ext_ids;
         !refs
       end

       val ty_arr = Array.fromList types
       val tm_arr = Array.fromList terms
       val live_ty = Array.array(n_types, false)
       val live_tm = Array.array(n_terms, false)
       fun mark_term i =
         if i < 0 orelse i >= n_terms orelse Array.sub(live_tm, i) then ()
         else (Array.update(live_tm, i, true);
               case Term.dest_term (Array.sub(tm_arr, i)) of
                 Term.COMB(f, x) =>
                   (mark_term (tm_lookup f); mark_term (tm_lookup x))
               | Term.LAMB(v, b) =>
                   (mark_term (tm_lookup v); mark_term (tm_lookup b))
               | Term.VAR(_, ty) => mark_type (ty_lookup ty)
               | Term.CONST{Ty,...} => mark_type (ty_lookup Ty))
       and mark_type i =
         if i < 0 orelse i >= n_types orelse Array.sub(live_ty, i) then ()
         else (Array.update(live_ty, i, true);
               let val ty = Array.sub(ty_arr, i) in
                 if Type.is_vartype ty then ()
                 else let val {Args,...} = Type.dest_thy_type ty
                      in List.app (fn a => mark_type (ty_lookup a)) Args
                      end
               end)
       val _ = Redblackset.app (fn i =>
         (if i >= 0 andalso i < n_terms then mark_term i else ();
          if i >= 0 andalso i < n_types then mark_type i else ())) all_refs

       val nlt = Array.foldl (fn (b,n) => if b then n+1 else n) 0 live_ty
       val nlm = Array.foldl (fn (b,n) => if b then n+1 else n) 0 live_tm

       val _ = checkpoint t_prune_ms t3_start

       (* Write optimized trace to temp file, then rename over raw *)
       val _ = timed t_opt_write_ms (fn () =>
         let val tmpgz = outname ^ ".tmp"
             val oh2 = open_output tmpgz
             val os2 = out_stream oh2
         in (write_body os2
                  {step_count = n_unique, step_offset = n_unique,
                   type_live_fn = fn i => Array.sub(live_ty, i),
                   term_live_fn = fn i => Array.sub(live_tm, i),
                   step_include = fn did =>
                     Array.sub(dedup_to, did) = did,
                   step_outid = fn did => Array.sub(output_id, did),
                   renumber = fn did => its (opt_outid did),
                   export_outid = opt_outid};
                close_output oh2)
               handle e =>
                 (close_output oh2 handle _ => (); raise e);
            OS.FileSys.rename {old = tmpgz, new = outname}
         end)
     in
       (n_unique, n_live - n_unique, nlt, nlm)
     end)
    handle e =>
      (Feedback.HOL_WARNING "TraceExport" "export"
         ("optimized export failed (" ^ General.exnMessage e ^
          "); keeping raw trace");
       (OS.FileSys.remove (outname ^ ".tmp") handle _ => ());
       (n_live, 0, n_types, n_terms))
  in
    (if !bench_mode then
       let val elapsed =
             time_to_ms (Timer.checkRealTimer t_export_start)
       in t_total_ms := !t_total_ms + elapsed;
          t_n_exports := !t_n_exports + 1;
          print ("TRACE_BENCH: " ^ thyname ^
                 " total=" ^ its elapsed ^
                 " reach=" ^ its (!t_reachability_ms) ^
                 " raw=" ^ its (!t_raw_write_ms) ^
                 " dedup=" ^ its (!t_dedup_ms) ^
                 " prune=" ^ its (!t_prune_ms) ^
                 " opt=" ^ its (!t_opt_write_ms) ^ "\n");
          reset_timings ()
       end
     else ());
    Feedback.HOL_MESG ("Proof trace: " ^ outname ^ " (" ^
      its n_final ^ " steps" ^
      (if n_deduped > 0 then " [" ^ its n_deduped ^ " deduped]"
       else "") ^
      " + " ^ its n_ext ^ " ancestor, " ^
      its n_live_terms ^ "/" ^ its n_terms ^ " terms, " ^
      its n_live_types ^ "/" ^ its n_types ^ " types)")
  end
  handle IO.Io e =>
    Feedback.HOL_WARNING "TraceExport" "export"
      ("I/O error: " ^ #function e ^ " " ^ #name e)
  | HOL_ERR _ => ()

end (* structure *)
