(* MergeTrace: merge per-theory and heap traces into a single
   self-contained trace.

   Two-pass algorithm:
   Pass 1: determine live entries per file via backward reachability,
           following NAME/LOAD and heap chain references across files
   Pass 2: re-read needed files in dependency order, dedup types/terms,
           remap all IDs, write merged output

   Key design points:
   - P entry IDs are kernel trace_ids (sparse, non-sequential)
   - Y and T entry IDs are sequential per-file (0-based)
   - Heap traces are discovered by following H lines
   - Types and terms are globally deduplicated across files
   - Each non-NAME/LOAD P entry gets a fresh sequential global ID
*)

structure MergeTrace :> MergeTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "MergeTrace"
fun its i = Int.toString i

(* ------- Memory instrumentation ------- *)

(* Read VmRSS from /proc/self/status, return in MB *)
fun get_rss_mb () : int =
  let val s = TextIO.openIn "/proc/self/status"
      fun scan () =
        case TextIO.inputLine s of
          NONE => (TextIO.closeIn s; 0)
        | SOME line =>
          if String.isPrefix "VmRSS:" line then
            let val toks = String.tokens Char.isSpace line
                val kb = case toks of
                           [_, n, _] => (case Int.fromString n of
                                           SOME v => v | NONE => 0)
                         | _ => 0
            in TextIO.closeIn s; kb div 1024 end
          else scan ()
  in scan () handle _ => 0 end

val mem_log : TextIO.outstream option ref = ref NONE

fun open_mem_log output_path =
  let val log_path = output_path ^ ".memlog"
      val s = TextIO.openOut log_path
  in mem_log := SOME s;
     TextIO.output(TextIO.stdErr,
       "  memory log: " ^ log_path ^ "\n");
     s
  end

fun mem (msg : string) =
  case !mem_log of
    NONE => ()
  | SOME s =>
    let val rss = get_rss_mb ()
    in TextIO.output(s, its rss ^ " MB\t" ^ msg ^ "\n");
       TextIO.flushOut s
    end

fun close_mem_log () =
  case !mem_log of
    NONE => ()
  | SOME s => (TextIO.closeOut s handle _ => ();
               mem_log := NONE)
(* Current file, line, and phase for error reporting.
   Set by each scan/process loop before parsing a line. *)
val parse_file = ref ""
val parse_line = ref 0
val parse_phase = ref ""

fun int_of s = case Int.fromString s of
    SOME n => n
  | NONE => raise ERR "int_of" ("not an int: " ^ s ^
      " [" ^ !parse_phase ^ "] " ^
      !parse_file ^ ":" ^ Int.toString (!parse_line))
val esc = TraceRecord.escape_string
val tokenize = ReplayTrace.tokenize
val unescape = ReplayTrace.unescape

(* ------- Stack ref resolution ------- *)

(* Read-side stacks for resolving ~k / ^k references.
   These are used during sequential scans (dep scan and Pass 2)
   to map stack-relative references back to explicit IDs. *)

val STACK_DEPTH = 16

fun mk_stack () = (Array.array(STACK_DEPTH, ~1), ref 0)

fun stack_push (arr, ptr) id =
  (Array.update(arr, !ptr, id);
   ptr := (!ptr + 1) mod STACK_DEPTH)

fun stack_resolve (arr, ptr) k =
  if k < 0 orelse k >= STACK_DEPTH then ~1
  else Array.sub(arr, (!ptr - 1 - k + STACK_DEPTH) mod STACK_DEPTH)

fun stack_reset (arr, ptr) =
  (Array.modify (fn _ => ~1) arr; ptr := 0)

(* Check if a token is a stack ref (~k or ^k) *)
fun is_tilde_ref s = size s >= 2 andalso String.sub(s, 0) = #"~"
                     andalso Char.isDigit(String.sub(s, 1))
fun is_caret_ref s = size s >= 2 andalso String.sub(s, 0) = #"^"
                     andalso Char.isDigit(String.sub(s, 1))

(* Parse a stack ref token: "~3" -> 3, "^0" -> 0 *)
fun stack_ref_k s = int_of (String.extract(s, 1, NONE))

(* Resolve a term ref token: if ~k, resolve via term stack;
   otherwise parse as int *)
fun resolve_tref tstack s =
  if is_tilde_ref s then stack_resolve tstack (stack_ref_k s)
  else int_of s

(* Resolve a theorem ref token: if ^k, resolve via thm stack;
   otherwise parse as int *)
fun resolve_pref pstack s =
  if is_caret_ref s then stack_resolve pstack (stack_ref_k s)
  else int_of s

(* Resolve all ~k/^k refs in a token list, given knowledge of
   which positions are t-refs, p-refs, or other.
   This is used in Pass 2 before remap_args. *)
fun resolve_args tstack pstack rule args =
  let
    fun rt s = if is_tilde_ref s
               then its (stack_resolve tstack (stack_ref_k s))
               else s
    fun rp s = if is_caret_ref s
               then its (stack_resolve pstack (stack_ref_k s))
               else s
    val nargs = length args
  in case rule of
      "REFL" => [rt (hd args)]
    | "ASSUME" => [rt (hd args)]
    | "BETA_CONV" => [rt (hd args)]
    | "ALPHA" => map rt args
    | "ABS" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "MK_COMB" => map rp args
    | "AP_TERM" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "AP_THM" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "SYM" => [rp (hd args)]
    | "TRANS" => map rp args
    | "EQ_MP" => map rp args
    | "EQ_IMP_RULE1" => [rp (hd args)]
    | "EQ_IMP_RULE2" => [rp (hd args)]
    | "MP" => map rp args
    | "DISCH" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "INST_TYPE" => rp (hd args) :: tl args  (* y refs are never ~k *)
    | "INST" => rp (hd args) :: map rt (tl args)
    | "SUBST" =>
        let val rest = List.drop(args, 2)
            fun pairs [] = []
              | pairs (v::r::t) = rt v :: rp r :: pairs t
              | pairs _ = []
        in rp (List.nth(args,0)) :: rt (List.nth(args,1)) :: pairs rest
        end
    | "SPEC" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "SPECL" => rp (hd args) :: map rt (tl args)
    | "Specialize" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "SPECIALIZEL" => rp (hd args) :: map rt (tl args)
    | "Specialize_thm" => [rp (List.nth(args,0)), rp (List.nth(args,1))]
    | "GEN" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "GENL" => rp (hd args) :: map rt (tl args)
    | "GEN_ABS" =>
        rp (List.nth(args,0)) ::
        (let val a1 = List.nth(args,1)
         in if a1 = "~" then "~" else rt a1 end) ::
        map rt (List.drop(args, 2))
    | "EXISTS" => [rp (List.nth(args,0)), rt (List.nth(args,1)),
                   rt (List.nth(args,2))]
    | "CHOOSE" => [rp (List.nth(args,0)), rp (List.nth(args,1)),
                   rt (List.nth(args,2))]
    | "CONJ" => map rp args
    | "CONJUNCT1" => [rp (hd args)]
    | "CONJUNCT2" => [rp (hd args)]
    | "DISJ1" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "DISJ2" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "DISJ_CASES" => map rp args
    | "NOT_INTRO" => [rp (hd args)]
    | "NOT_ELIM" => [rp (hd args)]
    | "CCONTR" => [rp (List.nth(args,0)), rt (List.nth(args,1))]
    | "Beta" => [rp (hd args)]
    | "REFL_RATOR" => [rp (hd args)]
    | "REFL_RAND" => [rp (hd args)]
    | "REFL_BODY" => [rp (hd args)]
    | "Mk_comb" => map rp args
    | "Mk_abs" => map rp args
    | "DEF_TYOP" => [rp (List.nth(args,0)),
                     List.nth(args,1), List.nth(args,2)]
    | "DEF_SPEC" => rp (hd args) :: tl args
    | "COMPUTE" => rt (hd args) :: map rp (tl args)
    | "AXIOM" => [List.nth(args,0), rt (List.nth(args,1))]
    | "ORACLE" =>
        List.nth(args,0) :: rt (List.nth(args,1)) ::
        map rt (List.drop(args, 2))
    | "NAME" => args  (* always explicit IDs *)
    | "LOAD" => args  (* always explicit IDs *)
    | _ => args
  end

(* ------- Per-rule argument parsing ------- *)

(* Extract parent (theorem) IDs from a P entry's args.
   Returns list of trace_ids that are parent theorem references. *)
fun extract_parent_ids rule args =
  let
    fun ai n = int_of (List.nth(args, n))
    val nargs = length args
  in case rule of
    (* No parents *)
      "REFL" => [] | "ASSUME" => [] | "BETA_CONV" => []
    | "ALPHA" => [] | "AXIOM" => [] | "NAME" => []
    | "LOAD" => [] | "ORACLE" => []
    (* Single parent at position 0 *)
    | "ABS" => [ai 0] | "AP_TERM" => [ai 0] | "AP_THM" => [ai 0]
    | "SYM" => [ai 0] | "DISCH" => [ai 0] | "SPEC" => [ai 0]
    | "SPECL" => [ai 0]
    | "Specialize" => [ai 0] | "SPECIALIZEL" => [ai 0]
    | "Specialize_thm" => [ai 0, ai 1]
    | "GEN" => [ai 0]
    | "EQ_IMP_RULE1" => [ai 0] | "EQ_IMP_RULE2" => [ai 0]
    | "CONJUNCT1" => [ai 0] | "CONJUNCT2" => [ai 0]
    | "DISJ1" => [ai 0] | "DISJ2" => [ai 0]
    | "NOT_INTRO" => [ai 0] | "NOT_ELIM" => [ai 0]
    | "CCONTR" => [ai 0] | "Beta" => [ai 0]
    | "REFL_RATOR" => [ai 0] | "REFL_RAND" => [ai 0]
    | "REFL_BODY" => [ai 0]
    | "EXISTS" => [ai 0]
    | "DEF_TYOP" => [ai 0]
    | "DEF_SPEC" => [ai 0]
    | "GENL" => [ai 0]
    | "GEN_ABS" => [ai 0]
    | "INST_TYPE" => [ai 0]
    | "INST" => [ai 0]
    (* Two parents *)
    | "MK_COMB" => [ai 0, ai 1] | "TRANS" => [ai 0, ai 1]
    | "EQ_MP" => [ai 0, ai 1] | "MP" => [ai 0, ai 1]
    | "CONJ" => [ai 0, ai 1] | "Mk_abs" => [ai 0, ai 1]
    | "CHOOSE" => [ai 0, ai 1]
    (* Three parents *)
    | "Mk_comb" => [ai 0, ai 1, ai 2]
    | "DISJ_CASES" => [ai 0, ai 1, ai 2]
    (* SUBST: p t (t p)* — parent at 0, then every 4th from pos 3 *)
    | "SUBST" =>
        ai 0 :: List.tabulate((nargs - 2) div 2, fn i => ai (3 + 2*i))
    (* COMPUTE: t p* — parents from pos 1 *)
    | "COMPUTE" =>
        List.tabulate(nargs - 1, fn i => ai (1 + i))
    | _ => []
  end

(* Extract term IDs referenced by a P entry *)
fun extract_term_ids rule args =
  let
    fun ai n = int_of (List.nth(args, n))
    val nargs = length args
  in case rule of
      "REFL" => [ai 0] | "ASSUME" => [ai 0] | "BETA_CONV" => [ai 0]
    | "ALPHA" => [ai 0, ai 1] | "AXIOM" => [ai 1]
    | "ABS" => [ai 1] | "AP_TERM" => [ai 1] | "AP_THM" => [ai 1]
    | "DISCH" => [ai 1] | "SPEC" => [ai 1] | "Specialize" => [ai 1]
    | "SPECL" => List.tabulate(nargs - 1, fn i => ai (1 + i))
    | "SPECIALIZEL" => List.tabulate(nargs - 1, fn i => ai (1 + i))
    | "GEN" => [ai 1] | "CCONTR" => [ai 1]
    | "DISJ1" => [ai 1] | "DISJ2" => [ai 1]
    | "EXISTS" => [ai 1, ai 2]
    | "CHOOSE" => [ai 2]
    | "GENL" => List.tabulate(nargs - 1, fn i => ai (1 + i))
    | "GEN_ABS" =>
        (if List.nth(args, 1) = "~" then []
         else [ai 1]) @
        List.tabulate(nargs - 2, fn i => ai (2 + i))
    | "INST" =>
        List.tabulate(nargs - 1, fn i => ai (1 + i))
    | "SUBST" =>
        ai 1 :: List.tabulate((nargs - 2) div 2, fn i => ai (2 + 2*i))
    | "COMPUTE" => [ai 0]
    | "ORACLE" =>
        ai 1 :: List.tabulate(nargs - 2, fn i => ai (2 + i))
    | _ => []
  end

(* Extract type IDs referenced by a P entry *)
fun extract_type_ids rule args =
  let
    fun ai n = int_of (List.nth(args, n))
    val nargs = length args
  in case rule of
      "INST_TYPE" =>
        List.tabulate(nargs - 1, fn i => ai (1 + i))
    | _ => []
  end

(* String pair comparison, used for (theory, name) keys *)
fun thyname_cmp ((t1,n1) : string*string, (t2,n2)) =
  case String.compare(t1,t2) of EQUAL => String.compare(n1,n2)
                               | ord => ord

(* ------- Pass 1: Read and analyze a trace file ------- *)

(* Per-file trace data for reachability analysis.

   Types (Y) and terms (T) have sequential IDs starting from 0,
   so we use growable arrays for them.

   Theorems (P) have kernel trace_ids which are sparse (e.g., a
   theory built on a heap with counter at 5M starts IDs from 5M+),
   so we use int-keyed maps for P entries. *)

(* Heavy dependency data needed only during Pass 1.
   Built lazily by read_file_deps, cleared by clear_deps. *)
type file_deps = {
  p_base_id : int,
  (* Resolved deps per P entry, indexed by (id - p_base_id).
     Each entry is (parent_ids, term_ids, type_ids) with all
     ~k/^k refs resolved to explicit IDs during the sequential
     dep scan. p_seen[i] is true iff the entry was present in
     the trace file. *)
  p_deps : (int list * int list * int list) Array.array,
  p_seen : bool Array.array,
  t_term_deps : int list Array.array,
  t_type_deps : int list Array.array,
  y_deps : int list Array.array,
  t_def : int Array.array,
  t_nc  : int Array.array,
  y_def : int Array.array,
  (* These are duplicated from file_data for convenience *)
  compute_ids : unit PIntMap.t,
  c_deps : (int list * int list * int list) option,
  t_unresolved_defs : (int * (string * string)) list,
  y_unresolved_defs : (int * (string * string)) list
}

type file_data = {
  path : string,
  heap_parent : string option,
  is_heap : bool,
  thy_name : string,
  n_terms : int,
  n_types : int,
  exports : (string, int) Redblackmap.dict,
  name_refs : (int * string * string) list,
  load_refs : (int * string * int) list,
  const_defs : (string * string, int) Redblackmap.dict,
  type_defs : (string * string, int) Redblackmap.dict,
  const_decls : (string * string, int) Redblackmap.dict,
  type_decls : (string * string, int) Redblackmap.dict,
  t_const_refs : (int * (string * string)) list,
  y_tyop_refs : (int * (string * string)) list,
  (* P ID range (from metadata scan, used by dep scan) *)
  p_min_id : int,
  p_max_id : int,
  (* COMPUTE and C deps (from metadata scan, copied into file_deps) *)
  compute_ids : unit PIntMap.t,
  c_deps : (int list * int list * int list) option,
  (* Heavy deps, built lazily by read_file_deps *)
  deps : file_deps option ref
}

(* Growable list accumulator, converted to array at the end *)
fun list_to_array n items default =
  let val arr = Array.array(n, default)
  in List.app (fn (id, v) =>
       if id < n then Array.update(arr, id, v) else ()) items;
     arr
  end

(* Shared scanning loop: read all lines, call process_line for each *)
fun scan_file path phase process_line =
  let
    val _ = (parse_file := path; parse_line := 0;
             parse_phase := phase)
    val (instrm, close_instrm) = TraceCompress.open_trace path
    val byte_pos = ref 0
    fun read_all () =
      case TextIO.inputLine instrm of
        NONE => ()
      | SOME line =>
          let val pos = !byte_pos
          in parse_line := !parse_line + 1;
             byte_pos := pos + size line;
             process_line pos
               (String.substring(line, 0, size line - 1)
                handle Subscript => line);
             read_all ()
          end
  in read_all ();
     close_instrm ();
     TraceCompress.release_temp path
  end

(* --- Convert TraceMetadata.metadata to file_data --- *)

fun metadata_to_file_data path (m : TraceMetadata.metadata) : file_data =
  let
    fun build_dict cmp items =
      List.foldl (fn ((k,v), d) => Redblackmap.insert(d, k, v))
        (Redblackmap.mkDict cmp) items
  in
    { path = path,
      heap_parent = #heap_parent m,
      is_heap = #thy_name m = "",
      thy_name = #thy_name m,
      n_terms = #n_terms m,
      n_types = #n_types m,
      exports = build_dict String.compare (#exports m),
      name_refs = #name_refs m,
      load_refs = #load_refs m,
      const_defs = List.foldl (fn ((id, thy, names), d) =>
          List.foldl (fn (c, d') =>
            Redblackmap.insert(d', (thy, c), id)) d names)
        (Redblackmap.mkDict thyname_cmp) (#const_defs m),
      type_defs = List.foldl (fn ((id, thy, tyop), d) =>
          Redblackmap.insert(d, (thy, tyop), id))
        (Redblackmap.mkDict thyname_cmp) (#type_defs m),
      const_decls = List.foldl (fn ((thy, name, tyid), d) =>
          Redblackmap.insert(d, (thy, name), tyid))
        (Redblackmap.mkDict thyname_cmp) (#const_decls m),
      type_decls = List.foldl (fn ((thy, name, arity), d) =>
          Redblackmap.insert(d, (thy, name), arity))
        (Redblackmap.mkDict thyname_cmp) (#type_decls m),
      t_const_refs = map (fn (id,thy,nm) => (id,(thy,nm)))
                       (#t_const_refs m),
      y_tyop_refs = map (fn (id,thy,nm) => (id,(thy,nm)))
                      (#y_tyop_refs m),
      p_min_id = #p_min_id m,
      p_max_id = #p_max_id m,
      compute_ids = List.foldl (fn (id, m) => PIntMap.add id () m)
                      PIntMap.empty (#compute_ids m),
      c_deps = #c_deps m,
      deps = ref NONE }
  end

(* --- Load file metadata: .pftm if available, else scan .pft --- *)

fun read_file_metadata path : file_data =
  let
    (* Try .pftm first *)
    val pftm = TraceMetadata.metadata_path path
  in
    case TraceMetadata.read pftm of
      SOME m => metadata_to_file_data path m
    | NONE =>
        (* Fallback: expensive full scan *)
        (* TODO: write .pftm after extract so future runs skip the scan *)
        metadata_to_file_data path (TraceMetadata.extract path)
  end

(* --- Dep scan: builds only the heavy dep structures --- *)

fun read_file_deps (data : file_data) : unit =
  let
    val path = #path data
    val nt = #n_terms data
    val ny = #n_types data

    (* Array for resolved P entry deps, indexed by (id - p_min_id).
       Sentinel ([], [], []) for entries not yet seen. *)
    val p_min_id = #p_min_id data
    val p_max_id = #p_max_id data
    val p_range = if p_min_id < 0 then 0
                  else p_max_id - p_min_id + 1
    val p_deps_arr : (int list * int list * int list) Array.array =
      Array.array(p_range, ([], [], []))
    (* Track which P entries have been seen (to distinguish
       empty deps from unseen entries). *)
    val p_seen = Array.array(p_range, false)

    (* Y and T deps accumulated as lists, arrays built at end *)
    val y_deps_rev = ref ([] : (int * int list) list)
    val t_term_deps_rev = ref ([] : (int * int list) list)
    val t_type_deps_rev = ref ([] : (int * int list) list)

    (* Read-side stacks for resolving ~k/^k during sequential scan *)
    val tstack = mk_stack ()
    val pstack = mk_stack ()

    fun process_line (_:int) line =
      if size line < 2 then ()
      else
      let val c0 = String.sub(line, 0)
      in
        if c0 = #"P" then
          let val toks = tokenize line in
          (case toks of
            ("P" :: id_s :: rule :: args) =>
              let val id = int_of id_s
                  val i = id - p_min_id
                  (* Resolve ~k/^k refs to explicit IDs *)
                  val resolved = resolve_args tstack pstack rule args
                  val parents = extract_parent_ids rule resolved
                  val terms = extract_term_ids rule resolved
                  val types = extract_type_ids rule resolved
              in if i >= 0 andalso i < p_range then
                   (Array.update(p_deps_arr, i,
                      (parents, terms, types));
                    Array.update(p_seen, i, true))
                 else ();
                 stack_push pstack id
              end
          | _ => ())
          end
        else if c0 = #"T" then
          let val toks = tokenize line in
          (case toks of
            ("T" :: id_s :: "V" :: _ :: ty_s :: _) =>
              let val id = int_of id_s
              in t_term_deps_rev := (id, []) :: !t_term_deps_rev;
                 t_type_deps_rev := (id, [int_of ty_s])
                                    :: !t_type_deps_rev;
                 stack_push tstack id
              end
          | ("T" :: id_s :: "C" :: _ :: _ :: ty_s :: _) =>
              let val id = int_of id_s
              in t_term_deps_rev := (id, []) :: !t_term_deps_rev;
                 t_type_deps_rev := (id, [int_of ty_s])
                                    :: !t_type_deps_rev;
                 stack_push tstack id
              end
          | ("T" :: id_s :: "A" :: f_s :: x_s :: _) =>
              let val id = int_of id_s
                  val fid = resolve_tref tstack f_s
                  val xid = resolve_tref tstack x_s
              in t_term_deps_rev := (id, [fid, xid])
                                    :: !t_term_deps_rev;
                 t_type_deps_rev := (id, []) :: !t_type_deps_rev;
                 stack_push tstack id
              end
          | ("T" :: id_s :: "L" :: v_s :: b_s :: _) =>
              let val id = int_of id_s
                  val vid = resolve_tref tstack v_s
                  val bid = resolve_tref tstack b_s
              in t_term_deps_rev := (id, [vid, bid])
                                    :: !t_term_deps_rev;
                 t_type_deps_rev := (id, []) :: !t_type_deps_rev;
                 stack_push tstack id
              end
          | _ => ())
          end
        else if c0 = #"Y" then
          let val toks = tokenize line in
          (case toks of
            ("Y" :: id_s :: "V" :: _) =>
              y_deps_rev := (int_of id_s, []) :: !y_deps_rev
          | ("Y" :: id_s :: "O" :: _ :: _ :: arg_ids) =>
              let val id = int_of id_s
                  val deps = List.mapPartial Int.fromString arg_ids
              in y_deps_rev := (id, deps) :: !y_deps_rev end
          | _ => ())
          end
        else ()
      end

    val _ = scan_file path "dep-scan" process_line

    (* Build cascading arrays *)
    val t_def_arr = Array.array(nt, ~1)
    val t_nc_arr = Array.array(nt, ~1)
    val t_unresolved_defs_ref = ref ([] : (int * (string * string)) list)
    val _ = List.app (fn (tid, (thy, name)) =>
      case Redblackmap.peek(#const_defs data, (thy, name)) of
        SOME pid => Array.update(t_def_arr, tid, pid)
      | NONE =>
          (case Redblackmap.peek(#const_decls data, (thy, name)) of
             SOME tyid => Array.update(t_nc_arr, tid, tyid)
           | NONE => t_unresolved_defs_ref := (tid, (thy, name))
                                              :: !t_unresolved_defs_ref))
      (#t_const_refs data)
    val y_def_arr = Array.array(ny, ~1)
    val y_unresolved_defs_ref = ref ([] : (int * (string * string)) list)
    val _ = List.app (fn (yid, (thy, tyop)) =>
      case Redblackmap.peek(#type_defs data, (thy, tyop)) of
        SOME pid => Array.update(y_def_arr, yid, pid)
      | NONE =>
          (case Redblackmap.peek(#type_decls data, (thy, tyop)) of
             SOME _ => ()
           | NONE => y_unresolved_defs_ref := (yid, (thy, tyop))
                                              :: !y_unresolved_defs_ref))
      (#y_tyop_refs data)
  in
    #deps data := SOME {
      p_base_id = p_min_id,
      p_deps = p_deps_arr,
      p_seen = p_seen,
      t_term_deps = list_to_array nt (!t_term_deps_rev) [],
      t_type_deps = list_to_array nt (!t_type_deps_rev) [],
      y_deps = list_to_array ny (!y_deps_rev) [],
      compute_ids = #compute_ids data,
      c_deps = #c_deps data,
      t_def = t_def_arr,
      t_nc = t_nc_arr,
      y_def = y_def_arr,
      t_unresolved_defs = !t_unresolved_defs_ref,
      y_unresolved_defs = !y_unresolved_defs_ref
    }
  end

fun get_deps (data : file_data) : file_deps =
  case !(#deps data) of
    SOME d => d
  | NONE =>
    (* Deps not yet built, or were cleared. Build via dep scan. *)
    (mem ("get_deps building " ^ OS.Path.file (#path data));
     read_file_deps data;
     mem ("get_deps built " ^ OS.Path.file (#path data));
     case !(#deps data) of
       SOME d => d
     | NONE => raise ERR "get_deps"
                 ("failed to build deps for " ^ #path data))

fun clear_deps (data : file_data) =
  case !(#deps data) of
    NONE => ()
  | SOME _ =>
      (#deps data := NONE;
       TraceCompress.release_temp (#path data))

(* Check whether a trace_id has a P entry in this file *)
fun p_has_id (dp : file_deps) (id : int) =
  let val i = id - #p_base_id dp
  in i >= 0 andalso i < Array.length (#p_seen dp) andalso
     Array.sub(#p_seen dp, i)
  end

(* Read and parse a single P line's deps by seeking to its
   byte offset. Returns (parent_ids, term_ids, type_ids). *)
(* Look up resolved deps for a P entry by ID *)
fun read_p_deps (dp : file_deps) (id : int) =
  let val i = id - #p_base_id dp
  in Array.sub(#p_deps dp, i) end

(* ------- Heap trace file discovery ------- *)

(* Given a heap path from an H line (e.g. "/home/user/HOL/bin/hol.state0"),
   find the corresponding trace file at <heap_path>.pft. *)
fun find_heap_trace_file heap_path =
  TraceCompress.find_trace (heap_path ^ ".pft")

(* ------- Pass 1: Backward reachability ------- *)

(* Liveness sets for a file. Y and T use arrays (sequential IDs),
   P uses a bool array indexed by (trace_id - p_min_id). *)
type liveness = {
  live_y : bool Array.array,
  live_t : bool Array.array,
  live_p : bool Array.array,
  live_p_min : int,  (* p_min_id for this file *)
  live_p_count : int ref  (* count of live P entries *)
}

fun mark_live (data : file_data) (prev : liveness)
              (needed_thm_ids : int list)
  : liveness * int list (* unresolved parent trace_ids *)
    * bool (* true if any COMPUTE entry was newly marked live *)
    * (string * string) list (* unresolved type defs: (thy, tyop) *)
    * (string * string) list (* unresolved const defs: (thy, name) *) =
  let
    val live_y = #live_y prev
    val live_t = #live_t prev
    val live_p = #live_p prev
    val p_min = #live_p_min prev
    val live_p_count = #live_p_count prev
    val unresolved = ref ([] : int list)
    val found_compute = ref false

    val dp = get_deps data

    (* Use precomputed cascading arrays from file_deps *)
    val t_def = #t_def dp
    val t_nc = #t_nc dp
    val y_def = #y_def dp

    fun p_is_live id =
      let val idx = id - p_min
      in idx >= 0 andalso idx < Array.length live_p
         andalso Array.sub(live_p, idx)
      end

    fun mark_thm id =
      if p_is_live id then ()
      else if not (p_has_id dp id) then
        unresolved := id :: !unresolved
      else
        let val (parents, term_deps, type_deps) =
              read_p_deps dp id
            val idx = id - p_min
            val _ = Array.update(live_p, idx, true)
            val _ = live_p_count := !live_p_count + 1
            val _ = if PIntMap.mem id (#compute_ids dp)
                    then found_compute := true else ()
        in List.app mark_thm parents;
           List.app mark_term term_deps;
           List.app mark_type type_deps
        end
    and mark_term id =
      if id < 0 orelse id >= #n_terms data orelse
         Array.sub(live_t, id) then ()
      else (Array.update(live_t, id, true);
            List.app mark_term
              (Array.sub(#t_term_deps dp, id));
            List.app mark_type
              (Array.sub(#t_type_deps dp, id));
            let val def = Array.sub(t_def, id)
            in if def >= 0 then mark_thm def
               else (* No DEF_SPEC; check for C decl — mark its type live *)
                 let val nc = Array.sub(t_nc, id)
                 in if nc >= 0 then mark_type nc else () end
            end)
    and mark_type id =
      if id < 0 orelse id >= #n_types data orelse
         Array.sub(live_y, id) then ()
      else (Array.update(live_y, id, true);
            List.app mark_type (Array.sub(#y_deps dp, id));
            let val def = Array.sub(y_def, id)
            in if def >= 0 then mark_thm def else () end)
  in
    List.app mark_thm needed_thm_ids;

    (* If this file has a C line and we're processing it (i.e.,
       some thm IDs were requested), mark the C line's term and
       type refs as live. The C file is only ever processed when
       a COMPUTE entry is live, so this is safe. *)
    if isSome (#c_deps dp) andalso not (null needed_thm_ids) then
      let val (_, terms, types) = valOf (#c_deps dp)
      in List.app mark_term terms;
         List.app mark_type types
      end
    else ();

    (* Collect unresolved type/const defs for live entries.
       Must be after mark_thm so live_y/live_t are populated. *)
    let
      val unresolved_tyops =
        List.mapPartial (fn (yid, key) =>
          if Array.sub(live_y, yid) then SOME key else NONE)
          (#y_unresolved_defs dp)
      val unresolved_consts =
        List.mapPartial (fn (tid, key) =>
          if Array.sub(live_t, tid) then SOME key else NONE)
          (#t_unresolved_defs dp)
    in
      ({live_y = live_y, live_t = live_t, live_p = live_p,
        live_p_min = p_min, live_p_count = live_p_count},
       !unresolved,
       !found_compute,
       unresolved_tyops,
       unresolved_consts)
    end
  end

(* ------- Dedup map key types ------- *)

datatype ty_desc = TyV of string | TyO of string * string * int list
datatype tm_desc = TmV of string * int | TmC of string * string * int
                 | TmA of int * int | TmL of int * int

fun ty_desc_compare (TyV a, TyV b) = String.compare(a, b)
  | ty_desc_compare (TyV _, _) = LESS
  | ty_desc_compare (_, TyV _) = GREATER
  | ty_desc_compare (TyO(t1,n1,a1), TyO(t2,n2,a2)) =
      (case String.compare(t1,t2) of EQUAL =>
        (case String.compare(n1,n2) of EQUAL =>
          List.collate Int.compare (a1,a2)
        | ord => ord)
      | ord => ord)

fun tm_desc_compare (TmV(n1,t1), TmV(n2,t2)) =
      (case String.compare(n1,n2) of EQUAL => Int.compare(t1,t2)
       | ord => ord)
  | tm_desc_compare (TmV _, _) = LESS
  | tm_desc_compare (_, TmV _) = GREATER
  | tm_desc_compare (TmC(t1,n1,y1), TmC(t2,n2,y2)) =
      (case String.compare(t1,t2) of EQUAL =>
        (case String.compare(n1,n2) of EQUAL => Int.compare(y1,y2)
         | ord => ord)
      | ord => ord)
  | tm_desc_compare (TmC _, _) = LESS
  | tm_desc_compare (_, TmC _) = GREATER
  | tm_desc_compare (TmA(f1,x1), TmA(f2,x2)) =
      (case Int.compare(f1,f2) of EQUAL => Int.compare(x1,x2)
       | ord => ord)
  | tm_desc_compare (TmA _, _) = LESS
  | tm_desc_compare (_, TmA _) = GREATER
  | tm_desc_compare (TmL(v1,b1), TmL(v2,b2)) =
      (case Int.compare(v1,v2) of EQUAL => Int.compare(b1,b2)
       | ord => ord)

(* ------- Remap a P line's args ------- *)

(* remap_args: remap and render P entry arguments.
   ory: type ID -> string (always explicit)
   ort: term ID -> string (may produce ~k)
   orp: thm ID -> string (may produce ^k)
   All input args have been resolved to explicit IDs already. *)
fun remap_args (ory : int -> string) (ort : int -> string)
               (orp : int -> string) rule args =
  case rule of
    "REFL" => [ort (int_of (hd args))]
  | "ASSUME" => [ort (int_of (hd args))]
  | "BETA_CONV" => [ort (int_of (hd args))]
  | "ALPHA" => map (ort o int_of) args
  | "ABS" => [orp (int_of (List.nth(args,0))),
              ort (int_of (List.nth(args,1)))]
  | "MK_COMB" => map (orp o int_of) args
  | "AP_TERM" => [orp (int_of (List.nth(args,0))),
                  ort (int_of (List.nth(args,1)))]
  | "AP_THM" => [orp (int_of (List.nth(args,0))),
                 ort (int_of (List.nth(args,1)))]
  | "SYM" => [orp (int_of (hd args))]
  | "TRANS" => map (orp o int_of) args
  | "EQ_MP" => map (orp o int_of) args
  | "EQ_IMP_RULE1" => [orp (int_of (hd args))]
  | "EQ_IMP_RULE2" => [orp (int_of (hd args))]
  | "MP" => map (orp o int_of) args
  | "DISCH" => [orp (int_of (List.nth(args,0))),
                ort (int_of (List.nth(args,1)))]
  | "INST_TYPE" =>
      orp (int_of (hd args)) ::
      map (ory o int_of) (tl args)
  | "INST" =>
      orp (int_of (hd args)) ::
      map (ort o int_of) (tl args)
  | "SUBST" =>
      let val orig = orp (int_of (List.nth(args,0)))
          val tmpl = ort (int_of (List.nth(args,1)))
          val rest = List.drop(args, 2)
          fun pairs [] = []
            | pairs (v::r::t) =
                ort (int_of v) :: orp (int_of r) :: pairs t
            | pairs _ = []
      in orig :: tmpl :: pairs rest end
  | "SPEC" => [orp (int_of (List.nth(args,0))),
               ort (int_of (List.nth(args,1)))]
  | "SPECL" =>
      orp (int_of (hd args)) ::
      map (ort o int_of) (tl args)
  | "Specialize" => [orp (int_of (List.nth(args,0))),
                     ort (int_of (List.nth(args,1)))]
  | "SPECIALIZEL" =>
      orp (int_of (hd args)) ::
      map (ort o int_of) (tl args)
  | "Specialize_thm" => [orp (int_of (List.nth(args,0))),
                          orp (int_of (List.nth(args,1)))]
  | "GEN" => [orp (int_of (List.nth(args,0))),
              ort (int_of (List.nth(args,1)))]
  | "GENL" =>
      orp (int_of (hd args)) ::
      map (ort o int_of) (tl args)
  | "GEN_ABS" =>
      orp (int_of (List.nth(args,0))) ::
      (if List.nth(args,1) = "~" then "~"
       else ort (int_of (List.nth(args,1)))) ::
      map (ort o int_of) (List.drop(args, 2))
  | "EXISTS" => [orp (int_of (List.nth(args,0))),
                 ort (int_of (List.nth(args,1))),
                 ort (int_of (List.nth(args,2)))]
  | "CHOOSE" => [orp (int_of (List.nth(args,0))),
                 orp (int_of (List.nth(args,1))),
                 ort (int_of (List.nth(args,2)))]
  | "CONJ" => map (orp o int_of) args
  | "CONJUNCT1" => [orp (int_of (hd args))]
  | "CONJUNCT2" => [orp (int_of (hd args))]
  | "DISJ1" => [orp (int_of (List.nth(args,0))),
                ort (int_of (List.nth(args,1)))]
  | "DISJ2" => [orp (int_of (List.nth(args,0))),
                ort (int_of (List.nth(args,1)))]
  | "DISJ_CASES" => map (orp o int_of) args
  | "NOT_INTRO" => [orp (int_of (hd args))]
  | "NOT_ELIM" => [orp (int_of (hd args))]
  | "CCONTR" => [orp (int_of (List.nth(args,0))),
                 ort (int_of (List.nth(args,1)))]
  | "Beta" => [orp (int_of (hd args))]
  | "REFL_RATOR" => [orp (int_of (hd args))]
  | "REFL_RAND" => [orp (int_of (hd args))]
  | "REFL_BODY" => [orp (int_of (hd args))]
  | "Mk_comb" => map (orp o int_of) args
  | "Mk_abs" => map (orp o int_of) args
  | "DEF_TYOP" => [orp (int_of (List.nth(args,0))),
                   List.nth(args,1), List.nth(args,2)]
  | "DEF_SPEC" =>
      orp (int_of (hd args)) :: tl args
  | "COMPUTE" =>
      ort (int_of (hd args)) ::
      map (orp o int_of) (tl args)
  | "AXIOM" => [List.nth(args,0), ort (int_of (List.nth(args,1)))]
  | "ORACLE" =>
      List.nth(args,0) ::
      ort (int_of (List.nth(args,1))) ::
      map (ort o int_of) (List.drop(args, 2))
  | _ => args

(* ------- Main merge ------- *)

(* Compare file paths for use as map keys *)
fun merge {trace_paths : (string * string) list,
           desired_exports : (string * string) list,
           output_path : string,
           quiet : bool} =
  let
    val err = if quiet then fn _ => ()
             else fn s => TextIO.output(TextIO.stdErr, s)

    (* Build theory name -> file path map *)
    val thy_path_map = List.foldl (fn ((thy, path), m) =>
      Redblackmap.insert(m, thy, path))
      (Redblackmap.mkDict String.compare) trace_paths

    (* ============================================================
       Pass 1: Determine live entries across all needed files
       ============================================================ *)
    val _ = open_mem_log output_path
    val _ = mem "start"
    val _ = err "Pass 1: determining live entries...\n"

    (* Cache of loaded file data, keyed by canonical path *)
    val file_cache : (string, file_data) Redblackmap.dict ref =
      ref (Redblackmap.mkDict String.compare)

    fun load_file path =
      case Redblackmap.peek(!file_cache, path) of
        SOME data => data
      | NONE =>
        let val _ = if not quiet then
                      let val base = OS.Path.file path
                          val msg = "  loading " ^ base ^ "..."
                          val padded = StringCvt.padRight #" " 72 msg
                      in TextIO.output(TextIO.stdErr, "\r" ^ padded);
                         TextIO.flushOut TextIO.stdErr
                      end
                    else ()
            val data = read_file_metadata path
            val p_range = if #p_min_id data < 0 then 0
                          else #p_max_id data - #p_min_id data + 1
        in file_cache := Redblackmap.insert(!file_cache, path, data);
           mem ("load_file " ^ OS.Path.file path ^
                " p_range=" ^ its p_range);
           data
        end

    fun lv_p_mem (lv : liveness) id =
      let val idx = id - #live_p_min lv
      in idx >= 0 andalso idx < Array.length (#live_p lv)
         andalso Array.sub(#live_p lv, idx)
      end

    fun lv_p_size (lv : liveness) = !(#live_p_count lv)

    (* Per-file liveness results, keyed by path *)
    val file_liveness : (string, liveness) Redblackmap.dict ref =
      ref (Redblackmap.mkDict String.compare)

    (* Get or create liveness for a file *)
    fun get_liveness path =
      case Redblackmap.peek(!file_liveness, path) of
        SOME lv => lv
      | NONE =>
        let val data = load_file path
            val p_min = #p_min_id data
            val p_max = #p_max_id data
            val p_rng = if p_min < 0 then 0 else p_max - p_min + 1
            val lv = {live_y = Array.array(#n_types data, false),
                      live_t = Array.array(#n_terms data, false),
                      live_p = Array.array(p_rng, false),
                      live_p_min = p_min,
                      live_p_count = ref 0}
        in file_liveness :=
             Redblackmap.insert(!file_liveness, path, lv);
           lv
        end

    (* Update liveness for a file by merging in new live P ids *)
    fun update_liveness path lv =
      file_liveness := Redblackmap.insert(!file_liveness, path, lv)

    (* Track which files have been processed *)
    val processed_files = ref (Redblackset.empty String.compare)

    (* Given a trace_id not found in file at `path`, search up
       the heap ancestry chain for a file containing it. *)
    fun find_in_heap_chain path trace_id =
      let val data = load_file path
      in case #heap_parent data of
           NONE => NONE
         | SOME hp =>
           case find_heap_trace_file hp of
             NONE => NONE
           | SOME heap_pft =>
             let val hdata = load_file heap_pft
                 val hdp = get_deps hdata
             in if p_has_id hdp trace_id
                then SOME heap_pft
                else find_in_heap_chain heap_pft trace_id
             end
      end

    (* Global: any COMPUTE entry is live across all files *)
    val live_c = ref false

    (* Worklist: (file_path, thm_ids_needed) pairs to process *)
    val worklist = ref ([] : (string * int list) list)
    fun enqueue item = worklist := item :: !worklist

    (* Process one file: mark needed entries, enqueue discoveries.
       Only the new thm_ids need to be passed to mark_live since
       it short-circuits on already-live entries. *)
    val total_trace_files = length trace_paths
    val pass1_live_thms = ref 0
    val pass1_theories = ref 0
    val pass1_heaps = ref 0
    val pass1_last_report = ref (Time.now ())
    val spinner_chars = Vector.fromList ["|", "/", "-", "\\"]
    val spinner_idx = ref 0

    fun pass1_progress () =
      if quiet then ()
      else
        let val now = Time.now ()
            val elapsed = Time.-(now, !pass1_last_report)
        in if Time.>(elapsed, Time.fromMilliseconds 250) then
             let val si = !spinner_idx
                 val sc = Vector.sub(spinner_chars, si mod 4)
                 val msg = "  " ^ sc ^ " " ^
                   its (!pass1_theories) ^ "/" ^
                   its total_trace_files ^ " theories" ^
                   (if !pass1_heaps > 0
                    then " incl. " ^ its (!pass1_heaps) ^ " heaps"
                    else "") ^
                   ", " ^ its (!pass1_live_thms) ^ " live thms"
                 (* Pad to 72 chars to overwrite previous line *)
                 val padded = StringCvt.padRight #" " 72 msg
             in TextIO.output(TextIO.stdErr, "\r" ^ padded);
                TextIO.flushOut TextIO.stdErr;
                spinner_idx := si + 1;
                pass1_last_report := now
             end
           else ()
        end

    fun process_file path needed_thm_ids =
      let
        val _ = mem ("process_file " ^ OS.Path.file path ^
                     " ids=" ^ its (length needed_thm_ids))
        val data = load_file path
        val _ = if not (Redblackset.member(!processed_files, path))
                then (if #is_heap data
                      then pass1_heaps := !pass1_heaps + 1
                      else pass1_theories := !pass1_theories + 1)
                else ()
        val _ = pass1_progress ()
        val prev_lv = get_liveness path
        (* Skip if all requested IDs are already live *)
        val dominated = List.all
          (fn id => lv_p_mem prev_lv id) needed_thm_ids
      in if dominated then () else
      let
        val (lv, unresolved, found_compute,
             unresolved_tyops, unresolved_consts) =
          mark_live data prev_lv needed_thm_ids
        val prev_live_count = lv_p_size prev_lv
        val new_live_count = lv_p_size lv
      in
        pass1_live_thms :=
          !pass1_live_thms + (new_live_count - prev_live_count);
        update_liveness path lv;
        processed_files :=
          Redblackset.add(!processed_files, path);

        (* Enqueue ancestor DEF_TYOP for unresolved type ops.
           Silently skip if not found (C/O handled separately). *)
        List.app (fn (anc_thy, anc_tyop) =>
          case Redblackmap.peek(thy_path_map, anc_thy) of
            SOME anc_path =>
              let val anc_data = load_file anc_path
              in case Redblackmap.peek(#type_defs anc_data,
                                       (anc_thy, anc_tyop)) of
                   SOME thm_id => enqueue (anc_path, [thm_id])
                 | NONE => ()
              end
          | NONE => ())
          unresolved_tyops;

        (* Enqueue ancestor DEF_SPEC for unresolved constants.
           Silently skip if not found (C/O handled separately). *)
        List.app (fn (anc_thy, anc_name) =>
          case Redblackmap.peek(thy_path_map, anc_thy) of
            SOME anc_path =>
              let val anc_data = load_file anc_path
              in case Redblackmap.peek(#const_defs anc_data,
                                       (anc_thy, anc_name)) of
                   SOME thm_id => enqueue (anc_path, [thm_id])
                 | NONE => ()
              end
          | NONE => ())
          unresolved_consts;

        (* Only enqueue NAME/LOAD for NEWLY live entries
           (not in prev_lv but in lv) to avoid redundant re-processing *)
        let val _ = ()
        in
        (* Enqueue NAME ancestor exports *)
        List.app (fn (id, anc_thy, anc_name) =>
          if lv_p_mem lv id andalso
             not (lv_p_mem prev_lv id) then
            case Redblackmap.peek(thy_path_map, anc_thy) of
              SOME anc_path =>
                let val anc_data = load_file anc_path
                in case Redblackmap.peek(#exports anc_data, anc_name) of
                     SOME thm_id => enqueue (anc_path, [thm_id])
                   | NONE =>
                     err ("WARNING: export " ^ anc_thy ^ "." ^
                          anc_name ^ " not found\n")
                end
            | NONE =>
                err ("WARNING: no trace for theory " ^
                     anc_thy ^ "\n")
          else ()) (#name_refs data);

        (* Enqueue LOAD ancestor theorems by trace_id *)
        List.app (fn (id, anc_thy, anc_trace_id) =>
          if lv_p_mem lv id andalso
             not (lv_p_mem prev_lv id) then
            case Redblackmap.peek(thy_path_map, anc_thy) of
              SOME anc_path =>
                enqueue (anc_path, [anc_trace_id])
            | NONE =>
                err ("WARNING: no trace for theory " ^
                     anc_thy ^ "\n")
          else ()) (#load_refs data)
        end;

        (* Enqueue unresolved heap parent trace_ids *)
        List.app (fn trace_id =>
          case find_in_heap_chain path trace_id of
            NONE =>
              raise ERR "process_file"
                ("unresolved parent trace_id " ^ its trace_id ^
                 " in " ^ path ^
                 " (not found in any ancestor heap trace)")
          | SOME heap_pft =>
              enqueue (heap_pft, [trace_id]))
          unresolved;

        (* If a COMPUTE entry was newly marked live and we haven't
           already handled the C line, find it and enqueue its
           char_eqn parent thm IDs. *)
        if found_compute andalso not (!live_c) then
          let
            val _ = live_c := true
            fun find_c_file p =
              let val d = load_file p
                  val dd = get_deps d
              in case #c_deps dd of
                   SOME _ => SOME p
                 | NONE =>
                   case #heap_parent d of
                     NONE => NONE
                   | SOME hp =>
                     case find_heap_trace_file hp of
                       NONE => NONE
                     | SOME hpft => find_c_file hpft
              end
          in
            case find_c_file path of
              NONE => raise ERR "process_file"
                "COMPUTE entry live but no C line found"
            | SOME c_path =>
              let val (parents, _, _) =
                    valOf (#c_deps (get_deps (load_file c_path)))
              in enqueue (c_path, parents) end
          end
        else ()
      end end

    (* Seed worklist from desired exports *)
    val _ = List.app (fn (thy, name) =>
      case Redblackmap.peek(thy_path_map, thy) of
        NONE => err ("WARNING: no trace for theory " ^ thy ^ "\n")
      | SOME path =>
        let val data = load_file path
        in case Redblackmap.peek(#exports data, name) of
             SOME thm_id => enqueue (path, [thm_id])
           | NONE =>
             err ("WARNING: export " ^ thy ^ "." ^ name ^
                  " not found\n")
        end) desired_exports

    (* Release seeking resources for a file (fd + temp).
       No-op if already cleared. *)
    fun release_file path =
      case Redblackmap.peek(!file_cache, path) of
        SOME data => (clear_deps data;
                      mem ("release " ^ OS.Path.file path))
      | NONE => ()

    (* Is this a heap file? Heap deps are kept alive during drain
       because heap files are accessed repeatedly (every theory's
       unresolved parent IDs bounce through the heap chain). *)
    fun is_heap_file path =
      case Redblackmap.peek(!file_cache, path) of
        SOME data => #is_heap data
      | NONE => false

    (* Batch worklist items by file path, merging ID lists.
       Deduplicates IDs within each file to avoid redundant
       mark_live calls (mark_live short-circuits on already-live
       entries, but dedup avoids the overhead entirely). *)
    fun batch_worklist items =
      let val m = List.foldl (fn ((path, ids), acc) =>
            let val prev = case Redblackmap.peek(acc, path) of
                             SOME s => s | NONE => PIntMap.empty
                val merged = List.foldl
                  (fn (id, s) => PIntMap.add id () s) prev ids
            in Redblackmap.insert(acc, path, merged) end)
            (Redblackmap.mkDict String.compare) items
      in map (fn (path, idmap) =>
           (path, PIntMap.fold (fn (k,_,acc) => k::acc) [] idmap))
         (Redblackmap.listItems m)
      end

    (* Drain worklist *)
    val last_seek_path = ref (NONE : string option)

    fun drain () =
      case !worklist of
        [] => (case !last_seek_path of
                 SOME p => (if is_heap_file p then ()
                            else release_file p;
                            last_seek_path := NONE)
               | NONE => ())
      | items =>
        let
          (* Batch: merge all pending IDs for the same file *)
          val _ = worklist := []
          val batched = batch_worklist items
        in
          List.app (fn (path, ids) =>
            (* Release previous non-heap file's seeking temp.
               Keep heap file deps alive — they're accessed
               repeatedly and rebuilding is expensive. *)
            ((case !last_seek_path of
                SOME p => if p = path then ()
                          else if is_heap_file p then ()
                          else (release_file p;
                                last_seek_path := SOME path)
              | NONE => last_seek_path := SOME path);
             process_file path ids)) batched;
          drain ()
        end
    val _ = drain ()
    val _ = mem "drain complete"

    (* --- Resolve C/O for live constants/types ---

       After the main worklist drains, scan all processed files for
       live T/Y entries whose constants/types have no DEF_SPEC/DEF_TYOP
       anywhere. For those, find the C/O in an ancestor file and
       ensure that file is included. For C, also mark its type live
       in the ancestor file (which may cascade, requiring another
       drain). *)

    (* Check if a constant (thy, name) has a DEF_SPEC or C in its
       defining theory's trace file. Only loads that one file. *)
    fun has_const_resolution (thy, name) =
      case Redblackmap.peek(thy_path_map, thy) of
        NONE => false
      | SOME path =>
          let val d = load_file path
          in isSome (Redblackmap.peek(#const_defs d, (thy, name)))
             orelse
             isSome (Redblackmap.peek(#const_decls d, (thy, name)))
          end

    fun has_type_resolution (thy, tyop) =
      case Redblackmap.peek(thy_path_map, thy) of
        NONE => false
      | SOME path =>
          let val d = load_file path
          in isSome (Redblackmap.peek(#type_defs d, (thy, tyop)))
             orelse
             isSome (Redblackmap.peek(#type_decls d, (thy, tyop)))
          end

    (* For each processed file, find live constants/types needing C/O *)
    val needed_ncs = ref (Redblackset.empty thyname_cmp)
    val needed_nys = ref (Redblackset.empty thyname_cmp)
    val _ = List.app (fn path =>
      let val data = load_file path
          val lv = case Redblackmap.peek(!file_liveness, path) of
                     SOME lv => lv | NONE => raise ERR "merge" "no liveness"
      in
        (* Check live T entries for constants with no local DEF_SPEC *)
        List.app (fn (tid, (thy, name)) =>
          if Array.sub(#live_t lv, tid) then
            case Redblackmap.peek(#const_defs data, (thy, name)) of
              SOME _ => () (* local DEF_SPEC — already handled *)
            | NONE =>
                case Redblackmap.peek(#const_decls data, (thy, name)) of
                  SOME _ => () (* local C — already in this file *)
                | NONE =>
                    if has_const_resolution (thy, name)
                    then needed_ncs :=
                           Redblackset.add(!needed_ncs, (thy, name))
                    else () (* truly primitive — min or missing *)
          else ())
          (#t_const_refs data);

        (* Check live Y entries for types with no local DEF_TYOP *)
        List.app (fn (yid, (thy, tyop)) =>
          if Array.sub(#live_y lv, yid) then
            case Redblackmap.peek(#type_defs data, (thy, tyop)) of
              SOME _ => ()
            | NONE =>
                case Redblackmap.peek(#type_decls data, (thy, tyop)) of
                  SOME _ => ()
                | NONE =>
                    if has_type_resolution (thy, tyop)
                    then needed_nys :=
                           Redblackset.add(!needed_nys, (thy, tyop))
                    else ()
          else ())
          (#y_tyop_refs data)
      end) (Redblackset.listItems (!processed_files))

    (* For each needed NC, find the file that has it, ensure it's
       processed, and mark the NC's type live there. We use
       mark_live_types to properly cascade type dependencies. *)
    val _ = Redblackset.app (fn (thy, name) =>
      case Redblackmap.peek(thy_path_map, thy) of
        SOME anc_path =>
          let val anc_data = load_file anc_path
          in case Redblackmap.peek(#const_decls anc_data, (thy, name)) of
               SOME tyid =>
                 let val anc_lv = get_liveness anc_path
                     val live_y = #live_y anc_lv
                     (* Recursively mark type and sub-types live *)
                     fun mark_ty id =
                       if id < 0 orelse id >= Array.length live_y
                          orelse Array.sub(live_y, id) then ()
                       else (Array.update(live_y, id, true);
                             List.app mark_ty
                               (Array.sub(#y_deps (get_deps anc_data), id)))
                 in processed_files :=
                      Redblackset.add(!processed_files, anc_path);
                    mark_ty tyid;
                    update_liveness anc_path anc_lv
                 end
             | NONE => ()
          end
      | NONE => ()) (!needed_ncs)

    (* For each needed NY, find the file and ensure it's processed *)
    val _ = Redblackset.app (fn (thy, tyop) =>
      case Redblackmap.peek(thy_path_map, thy) of
        SOME anc_path =>
          (processed_files :=
             Redblackset.add(!processed_files, anc_path);
           ignore (get_liveness anc_path))
      | NONE => ()) (!needed_nys)

    (* Build output order via unified topological sort across all
       files (both heap and theory traces).

       Dependencies:
       - NAME/LOAD in any file -> the theory file for thy
       - Live type/const refs with non-local DEF_TYOP/DEF_SPEC ->
         the theory file containing the definition
       - Heap ancestry: a file with H line depends on its parent heap
         (parent heap must be written first so its P entries are in
         heap_thm_map when the child is written)

       Theory files that a heap's NAME/LOAD entries reference must be
       written before the heap, not after. *)

    val all_files = Redblackset.listItems (!processed_files)

    (* Map theory name -> file path for theory traces *)
    val thy_to_path =
      let fun is_thy path =
            case Redblackmap.peek(!file_cache, path) of
              SOME d => not (#is_heap d) | NONE => false
      in List.foldl (fn (path, m) =>
           if is_thy path then
             let val data = load_file path
             in Redblackmap.insert(m, #thy_name data, path) end
           else m)
         (Redblackmap.mkDict String.compare) all_files
      end

    (* Dependencies for any file (heap or theory) *)
    fun file_deps path =
      let
        val data = load_file path
        val lv = case Redblackmap.peek(!file_liveness, path) of
            SOME lv => lv | NONE => raise ERR "merge" "no liveness"
        (* NAME deps -> theory file paths *)
        val thm_file_deps = List.mapPartial (fn (id, anc_thy, _) =>
          if lv_p_mem lv id then
            Redblackmap.peek(thy_to_path, anc_thy)
          else NONE)
          (#name_refs data)
        (* LOAD deps -> theory file paths *)
        val dep_file_deps = List.mapPartial (fn (id, anc_thy, _) =>
          if lv_p_mem lv id then
            Redblackmap.peek(thy_to_path, anc_thy)
          else NONE)
          (#load_refs data)
        (* Type/const def deps -> theory file paths.
           If a live type/const references a non-local DEF_TYOP/DEF_SPEC,
           the ancestor theory must be written first. *)
        val tyop_def_deps = List.mapPartial (fn (yid, (thy, _)) =>
          if Array.sub(#live_y lv, yid) then
            Redblackmap.peek(thy_to_path, thy)
          else NONE)
          (#y_tyop_refs data)
        val const_def_deps = List.mapPartial (fn (tid, (thy, _)) =>
          if Array.sub(#live_t lv, tid) then
            Redblackmap.peek(thy_to_path, thy)
          else NONE)
          (#t_const_refs data)
        (* Heap ancestry dep -> parent heap file path *)
        val heap_dep = case #heap_parent data of
            NONE => []
          | SOME hp =>
            case find_heap_trace_file hp of
              NONE => []
            | SOME hpft =>
              if Redblackset.member(!processed_files, hpft)
              then [hpft] else []
      in
        thm_file_deps @ dep_file_deps @ tyop_def_deps @
        const_def_deps @ heap_dep
      end

    (* Unified topo sort via DFS *)
    val topo =
      let
        val visited = ref (Redblackset.empty String.compare)
        val result = ref ([] : string list)
        fun visit path =
          if Redblackset.member(!visited, path) then ()
          else
            (visited := Redblackset.add(!visited, path);
             List.app visit (file_deps path);
             result := path :: !result)
      in
        List.app visit all_files;
        rev (!result)
      end

    val n_live_total =
      List.foldl (fn (path, acc) =>
        case Redblackmap.peek(!file_liveness, path) of
          SOME lv => acc + lv_p_size lv
        | NONE => acc) 0 topo

    val _ = if not quiet then
              (TextIO.output(TextIO.stdErr,
                 "\r" ^ StringCvt.padRight #" " 72 "" ^ "\r");
               TextIO.flushOut TextIO.stdErr)
            else ()
    val _ = err ("Pass 1 done: " ^ its (length topo) ^ " files, " ^
                 its n_live_total ^ " live theorems\n")

    (* Free heavy dependency data no longer needed after Pass 1 *)
    val _ = mem "before clear_deps (pass 1 done)"
    val _ = Redblackmap.app (fn (_, data) => clear_deps data)
              (!file_cache)
    (* Remove decompressed temp files — seeking is done *)
    val _ = TraceCompress.cleanup_temps ()
    val _ = mem "after clear_deps + cleanup_temps"

    (* ============================================================
       Pass 2: Write merged trace with global dedup and remapping
       ============================================================ *)
    val _ = err "Pass 2: writing merged trace...\n"

    val global_ty_map = ref (Redblackmap.mkDict ty_desc_compare)
    val global_tm_map = ref (Redblackmap.mkDict tm_desc_compare)
    val global_ty_id = ref 0
    val global_tm_id = ref 0
    val global_thm_id = ref 0

    (* (theory, name) -> global thm id, for resolving NAME *)
    val ancestor_exports : (string * string, int) Redblackmap.dict ref =
      ref (Redblackmap.mkDict thyname_cmp)

    (* Provenance accumulators for F/G lines *)
    val prov_f = ref ([] : (string * string * int) list)  (* thy, name, gid *)
    val prov_g = ref ([] : (string * int * int) list)     (* thy, trace_id, gid *)

    (* (theory, trace_id) -> global thm id, for resolving LOAD *)
    fun thyint_cmp ((t1,i1) : string*int, (t2,i2)) =
      case String.compare(t1,t2) of EQUAL => Int.compare(i1,i2)
                                   | ord => ord
    val ancestor_thm_map : (string * int, int) Redblackmap.dict ref =
      ref (Redblackmap.mkDict thyint_cmp)

    (* (file_path, trace_id) -> global thm id, for resolving
       heap parent references *)
    (* Nested map: heap_path -> (trace_id -> global_id) *)
    val heap_thm_map : (string, int PIntMap.t) Redblackmap.dict ref =
      ref (Redblackmap.mkDict String.compare)

    fun heap_thm_lookup (path, trace_id) =
      case Redblackmap.peek(!heap_thm_map, path) of
        NONE => NONE
      | SOME m => SOME (PIntMap.find trace_id m)
                  handle PIntMap.NotFound => NONE

    fun heap_thm_insert (path, trace_id, gid) =
      let val m = case Redblackmap.peek(!heap_thm_map, path) of
                    SOME m => m | NONE => PIntMap.empty
      in heap_thm_map :=
           Redblackmap.insert(!heap_thm_map, path,
                              PIntMap.add trace_id gid m)
      end

    val ostrm = TextIO.openOut output_path
    val _ = TextIO.output(ostrm, "V 1\n")

    fun write_file path =
      let
        val data = load_file path
        val lv = case Redblackmap.peek(!file_liveness, path) of
            SOME lv => lv
          | NONE => raise ERR "write_file"
                      ("no liveness for " ^ path)
        val live_y = #live_y lv
        val live_t = #live_t lv
        val live_p = #live_p lv
        val live_p_min = #live_p_min lv
        fun p_is_live id =
          let val idx = id - live_p_min
          in idx >= 0 andalso idx < Array.length live_p
             andalso Array.sub(live_p, idx)
          end

        val (instrm, close_instrm) = TraceCompress.open_trace path
        val _ = (parse_file := path; parse_line := 0;
                 parse_phase := "write")

        (* Read-side stacks for resolving ~k/^k during Pass 2 *)
        val r_tstack = mk_stack ()
        val r_pstack = mk_stack ()

        (* Local -> global remap: arrays for Y/T (sequential),
           map for P (sparse trace_ids) *)
        val y_remap = Array.array(#n_types data, ~1)
        val t_remap = Array.array(#n_terms data, ~1)
        (* P remap: array indexed by (trace_id - p_min_id) *)
        val p_min = #p_min_id data
        val p_max = #p_max_id data
        val p_rng = if p_min < 0 then 0 else p_max - p_min + 1
        val p_remap = Array.array(p_rng, ~1)

        fun rp_peek i =
          if i >= p_min andalso i <= p_max then
            let val g = Array.sub(p_remap, i - p_min)
            in if g >= 0 then SOME g else NONE end
          else NONE
        fun ry i = Array.sub(y_remap, i)
        fun rt i = Array.sub(t_remap, i)
        fun rp i =
          case rp_peek i of
            SOME gid => gid
          | NONE =>
            (* Not in this file — search up heap ancestry chain
               for a heap trace that defined this trace_id *)
            let fun search p =
                  let val d = load_file p
                  in case #heap_parent d of
                       NONE => raise ERR "write_file"
                         ("unresolved parent trace_id " ^ its i ^
                          " while writing " ^ path)
                     | SOME hp =>
                       case find_heap_trace_file hp of
                         NONE => raise ERR "write_file"
                           ("heap trace not found for " ^ hp)
                       | SOME hpft =>
                         case heap_thm_lookup (hpft, i) of
                           SOME gid => gid
                         | NONE => search hpft
                  end
            in search path end

        (* Write-side stacks for outputting ~k/^k in merged trace *)
        val w_tstack = mk_stack ()
        val w_pstack = mk_stack ()

        fun w_push_t gid = stack_push w_tstack gid
        fun w_push_p gid = stack_push w_pstack gid

        (* Output renderers: produce ~k/^k when on stack *)
        fun ory i = its (ry i)
        fun ort i =
          let val gid = rt i
              fun find k =
                if k >= STACK_DEPTH then its gid
                else if stack_resolve w_tstack k = gid
                then "~" ^ its k
                else find (k + 1)
          in find 0 end
        fun orp i =
          let val gid = rp i
              fun find k =
                if k >= STACK_DEPTH then its gid
                else if stack_resolve w_pstack k = gid
                then "^" ^ its k
                else find (k + 1)
          in find 0 end

        fun process_line line =
          let val toks = tokenize line in
          case toks of
            [] => ()
          | ("Y" :: id_s :: rest) =>
              let val id = int_of id_s
              in if id < Array.length live_y andalso
                    Array.sub(live_y, id) then
                let val desc = case rest of
                      ["V", name] => TyV (unescape name)
                    | ("O" :: thy_s :: name_s :: arg_ids) =>
                        TyO (unescape thy_s, unescape name_s,
                             map (ry o int_of) arg_ids)
                    | _ => raise ERR "write_file" "bad Y entry"
                in case Redblackmap.peek(!global_ty_map, desc) of
                     SOME gid => Array.update(y_remap, id, gid)
                   | NONE =>
                     let val gid = !global_ty_id
                     in global_ty_id := gid + 1;
                        global_ty_map :=
                          Redblackmap.insert(!global_ty_map, desc, gid);
                        Array.update(y_remap, id, gid);
                        TextIO.output(ostrm, case desc of
                          TyV name =>
                            "Y " ^ its gid ^ " V " ^ esc name ^ "\n"
                        | TyO (t,n,args) =>
                            "Y " ^ its gid ^ " O " ^ esc t ^ " " ^
                            esc n ^
                            (if null args then ""
                             else " " ^ String.concatWith " "
                                          (map its args)) ^ "\n")
                     end
                end
              else ()
              end
          | ("T" :: id_s :: rest) =>
              let val id = int_of id_s
              in (if id < Array.length live_t andalso
                    Array.sub(live_t, id) then
                let val desc = case rest of
                      ["V", name, ty_s] =>
                        TmV (unescape name, ry (int_of ty_s))
                    | ["C", thy_s, name_s, ty_s] =>
                        TmC (unescape thy_s, unescape name_s,
                             ry (int_of ty_s))
                    | ["A", f_s, x_s] =>
                        TmA (rt (resolve_tref r_tstack f_s),
                             rt (resolve_tref r_tstack x_s))
                    | ["L", v_s, b_s] =>
                        TmL (rt (resolve_tref r_tstack v_s),
                             rt (resolve_tref r_tstack b_s))
                    | _ => raise ERR "write_file" "bad T entry"
                in case Redblackmap.peek(!global_tm_map, desc) of
                     SOME gid => Array.update(t_remap, id, gid)
                   | NONE =>
                     let val gid = !global_tm_id
                         (* Render global term ID, using ~k if on
                            write-side stack *)
                         fun wt gid2 =
                           let fun find k =
                                 if k >= STACK_DEPTH then its gid2
                                 else if stack_resolve w_tstack k = gid2
                                 then "~" ^ its k
                                 else find (k + 1)
                           in find 0 end
                     in global_tm_id := gid + 1;
                        global_tm_map :=
                          Redblackmap.insert(!global_tm_map, desc, gid);
                        Array.update(t_remap, id, gid);
                        TextIO.output(ostrm, case desc of
                          TmV (name, tyid) =>
                            "T " ^ its gid ^ " V " ^ esc name ^
                            " " ^ its tyid ^ "\n"
                        | TmC (t,n,tyid) =>
                            "T " ^ its gid ^ " C " ^ esc t ^ " " ^
                            esc n ^ " " ^ its tyid ^ "\n"
                        | TmA (f,x) =>
                            "T " ^ its gid ^ " A " ^ wt f ^
                            " " ^ wt x ^ "\n"
                        | TmL (v,b) =>
                            "T " ^ its gid ^ " L " ^ wt v ^
                            " " ^ wt b ^ "\n");
                        w_push_t gid
                     end
                end
              else ());
              stack_push r_tstack id
              end
          | ("C" :: thy_s :: name_s :: ty_s :: _) =>
              let val thy = unescape thy_s
                  val name = unescape name_s
                  val tyid = int_of ty_s
              in (* Emit C if this constant is needed and has no
                    DEF_SPEC (locally or globally) *)
                if Redblackset.member(!needed_ncs, (thy, name)) orelse
                   (case Redblackmap.peek(#const_decls data, (thy, name)) of
                      SOME _ =>
                        (* Local C — emit if any live T refs this const *)
                        List.exists (fn (tid, k) =>
                          k = (thy, name) andalso
                          tid < Array.length live_t andalso
                          Array.sub(live_t, tid))
                          (#t_const_refs data)
                    | NONE => false)
                then TextIO.output(ostrm,
                       "C " ^ esc thy ^ " " ^ esc name ^
                       " " ^ its (ry tyid) ^ "\n")
                else ()
              end
          | ("O" :: thy_s :: name_s :: arity_s :: _) =>
              let val thy = unescape thy_s
                  val name = unescape name_s
                  val arity = int_of arity_s
              in if Redblackset.member(!needed_nys, (thy, name)) orelse
                   (case Redblackmap.peek(#type_decls data, (thy, name)) of
                      SOME _ =>
                        List.exists (fn (yid, k) =>
                          k = (thy, name) andalso
                          yid < Array.length live_y andalso
                          Array.sub(live_y, yid))
                          (#y_tyop_refs data)
                    | NONE => false)
                then TextIO.output(ostrm,
                       "O " ^ esc thy ^ " " ^ esc name ^
                       " " ^ arity_s ^ "\n")
                else ()
              end
          | ("P" :: id_s :: "NAME" :: args) =>
              let val id = int_of id_s
              in (if p_is_live id then
                let val anc_thy = unescape (List.nth(args, 0))
                    val anc_name = unescape (List.nth(args, 1))
                in case Redblackmap.peek(!ancestor_exports,
                                         (anc_thy, anc_name)) of
                     SOME gid =>
                       Array.update(p_remap, id - p_min, gid)
                   | NONE =>
                     err ("WARNING: unresolved NAME " ^
                          anc_thy ^ "." ^ anc_name ^ "\n")
                end
              else ());
              stack_push r_pstack id
              end
          | ("P" :: id_s :: "LOAD" :: args) =>
              let val id = int_of id_s
              in (if p_is_live id then
                let val anc_thy = unescape (List.nth(args, 0))
                    val anc_trace_id = int_of (List.nth(args, 1))
                    (* First try the ancestor theory's own trace *)
                    val gid_opt =
                      case Redblackmap.peek(!ancestor_thm_map,
                                             (anc_thy, anc_trace_id)) of
                        SOME gid => SOME gid
                      | NONE =>
                        (* trace_id might be from the theory's heap
                           chain (theorem survived heap restore into
                           the theory script without being re-loaded
                           from disk). Search up the heap chain. *)
                        case Redblackmap.peek(thy_path_map, anc_thy) of
                          NONE => NONE
                        | SOME anc_path =>
                          let fun search p =
                                let val d = load_file p
                                in case #heap_parent d of
                                     NONE => NONE
                                   | SOME hp =>
                                     case find_heap_trace_file hp of
                                       NONE => NONE
                                     | SOME hpft =>
                                       case heap_thm_lookup
                                              (hpft, anc_trace_id) of
                                         SOME gid => SOME gid
                                       | NONE => search hpft
                                end
                          in search anc_path end
                in case gid_opt of
                     SOME gid =>
                       (Array.update(p_remap, id - p_min, gid);
                        prov_g := (anc_thy, anc_trace_id, gid)
                                  :: !prov_g)
                   | NONE =>
                     err ("WARNING: unresolved LOAD " ^
                          anc_thy ^ ".#" ^ its anc_trace_id ^ "\n")
                end
              else ());
              stack_push r_pstack id
              end
          | ("P" :: id_s :: rule :: args) =>
              let val id = int_of id_s
              in (if p_is_live id then
                let val gid = !global_thm_id
                    val resolved =
                      resolve_args r_tstack r_pstack rule args
                    val remapped = remap_args ory ort orp rule resolved
                in global_thm_id := gid + 1;
                   Array.update(p_remap, id - p_min, gid);
                   TextIO.output(ostrm, "P " ^ its gid ^ " " ^
                     rule ^
                     (if null remapped then ""
                      else " " ^ String.concatWith " " remapped) ^
                     "\n");
                   w_push_p gid
                end
              else ());
              stack_push r_pstack id
              end
          | ("I" :: args) =>
              if !live_c then
              let
                fun ai n = int_of (List.nth(args, n))
                val cy = its (ry (ai 0))
                val ny' = its (ry (ai 1))
                val rest = List.drop(args, 2)
                val cvals = List.tabulate(29, fn i =>
                  List.nth(rest, 2*i) ^ " " ^
                  ort (resolve_tref r_tstack
                         (List.nth(rest, 2*i + 1))))
                val rest2 = List.drop(rest, 58)
                val char_pairs =
                  let fun go [] = []
                        | go (n::p::r) =
                            (n ^ " " ^ orp (resolve_pref r_pstack p))
                            :: go r
                        | go _ = []
                  in go rest2 end
              in TextIO.output(ostrm, "I " ^ cy ^ " " ^ ny' ^ " " ^
                   String.concatWith " " cvals ^
                   (if null char_pairs then ""
                    else " " ^ String.concatWith " " char_pairs) ^
                   "\n")
              end
              else ()
          | _ => ()  (* skip V, H, N, E, blank lines *)
          end

        fun read_all () =
          case TextIO.inputLine instrm of
            NONE => ()
          | SOME line =>
              (parse_line := !parse_line + 1;
               process_line (String.substring(line, 0, size line - 1)
                             handle Subscript => line);
               read_all ())
      in
        read_all ();
        close_instrm ();

        (* Register this file's exports in ancestor_exports *)
        Redblackmap.app (fn (name, local_id) =>
          case rp_peek local_id of
            SOME gid =>
              (ancestor_exports :=
                Redblackmap.insert(!ancestor_exports,
                                   (#thy_name data, name), gid);
               if not (#is_heap data) then
                 prov_f := (#thy_name data, name, gid) :: !prov_f
               else ())
          | NONE => ())
          (#exports data);

        (* Register this file's P entries for cross-file resolution.
           Theory traces: register in ancestor_thm_map (for LOAD resolution).
           Heap traces: register in heap_thm_map (for parent trace_id resolution). *)
        let fun for_live_p f =
              let val len = Array.length live_p
                  fun loop i =
                    if i >= len then ()
                    else (if Array.sub(live_p, i)
                          then f (i + live_p_min)
                          else ();
                          loop (i + 1))
              in loop 0 end
        in
        if #is_heap data then
          for_live_p (fn trace_id =>
            case rp_peek trace_id of
              SOME gid => heap_thm_insert (path, trace_id, gid)
            | NONE => ())
        else
          for_live_p (fn trace_id =>
            case rp_peek trace_id of
              SOME gid =>
                ancestor_thm_map :=
                  Redblackmap.insert(!ancestor_thm_map,
                                     (#thy_name data, trace_id), gid)
            | NONE => ())
        end
      end

    val _ = List.app (fn path =>
      let val data = load_file path
          val lv = case Redblackmap.peek(!file_liveness, path) of
              SOME lv => lv | NONE => raise ERR "merge" "no liveness"
          val n_live = lv_p_size lv
          val label = if #is_heap data
                      then OS.Path.file path
                      else #thy_name data
      in err ("  " ^ label ^ " (" ^ its n_live ^ " live thms)...\n");
         write_file path
      end) topo

    (* Write provenance lines *)
    val _ = List.app (fn (thy, name, gid) =>
      TextIO.output(ostrm, "F " ^ esc thy ^ " " ^ esc name ^
                    " " ^ its gid ^ "\n"))
      (rev (!prov_f))
    val _ = List.app (fn (thy, trace_id, gid) =>
      TextIO.output(ostrm, "G " ^ esc thy ^ " " ^ its trace_id ^
                    " " ^ its gid ^ "\n"))
      (rev (!prov_g))

    (* Write exports *)
    val _ = List.app (fn (thy, name) =>
      case Redblackmap.peek(!ancestor_exports, (thy, name)) of
        SOME gid =>
          TextIO.output(ostrm, "E " ^ esc name ^ " " ^
                        its gid ^ "\n")
      | NONE =>
          err ("WARNING: desired export " ^ thy ^ "." ^ name ^
               " not found in merged output\n")) desired_exports

    val _ = TextIO.closeOut ostrm
    val _ = mem "done"
    val _ = close_mem_log ()
  in
    err ("Merged trace: " ^ its (!global_ty_id) ^ " types, " ^
         its (!global_tm_id) ^ " terms, " ^
         its (!global_thm_id) ^ " thms -> " ^
         output_path ^ "\n")
  end

end
