(* MergeTrace: merge per-theory and heap traces into a single
   self-contained trace.

   Two-pass algorithm:
   Pass 1: determine live entries per file via backward reachability,
           following DISK_THM and heap chain references across files
   Pass 2: re-read needed files in dependency order, dedup types/terms,
           remap all IDs, write merged output

   Key design points:
   - P entry IDs are kernel trace_ids (sparse, non-sequential)
   - Y and T entry IDs are sequential per-file (0-based)
   - Heap traces are discovered by following H lines
   - Types and terms are globally deduplicated across files
   - Each non-DISK_THM P entry gets a fresh sequential global ID
*)

structure MergeTrace :> MergeTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "MergeTrace"
fun its i = Int.toString i
fun int_of s = case Int.fromString s of
    SOME n => n
  | NONE => raise ERR "int_of" ("not an int: " ^ s)
val esc = TraceRecord.escape_string
val tokenize = ReplayTrace.tokenize
val unescape = ReplayTrace.unescape

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
    | "ALPHA" => [] | "AXIOM" => [] | "DISK_THM" => []
    | "ORACLE" => []
    (* Single parent at position 0 *)
    | "ABS" => [ai 0] | "AP_TERM" => [ai 0] | "AP_THM" => [ai 0]
    | "SYM" => [ai 0] | "DISCH" => [ai 0] | "SPEC" => [ai 0]
    | "Specialize" => [ai 0] | "GEN" => [ai 0]
    | "EQ_IMP_RULE1" => [ai 0] | "EQ_IMP_RULE2" => [ai 0]
    | "CONJUNCT1" => [ai 0] | "CONJUNCT2" => [ai 0]
    | "DISJ1" => [ai 0] | "DISJ2" => [ai 0]
    | "NOT_INTRO" => [ai 0] | "NOT_ELIM" => [ai 0]
    | "CCONTR" => [ai 0] | "Beta" => [ai 0]
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
    | "ALPHA" => [ai 0, ai 1] | "AXIOM" => [ai 0]
    | "ABS" => [ai 1] | "AP_TERM" => [ai 1] | "AP_THM" => [ai 1]
    | "DISCH" => [ai 1] | "SPEC" => [ai 1] | "Specialize" => [ai 1]
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

(* ------- Pass 1: Read and analyze a trace file ------- *)

(* Per-file trace data for reachability analysis.

   Types (Y) and terms (T) have sequential IDs starting from 0,
   so we use growable arrays for them.

   Theorems (P) have kernel trace_ids which are sparse (e.g., a
   theory built on a heap with counter at 5M starts IDs from 5M+),
   so we use int-keyed maps for P entries. *)

type file_data = {
  path : string,
  heap_parent : string option,     (* H line: parent heap path *)
  is_heap : bool,                  (* true if no N line = heap trace *)
  thy_name : string,               (* N line value, "" for heaps *)
  (* P entry deps: trace_id -> (parent_ids, term_ids, type_ids) *)
  p_deps : (int, int list * int list * int list) Redblackmap.dict,
  (* Set of all P trace_ids defined in this file *)
  p_ids : int Redblackset.set,
  (* T entry deps: sequential id -> (sub_term_ids, sub_type_ids) *)
  t_term_deps : int list Array.array,
  t_type_deps : int list Array.array,
  n_terms : int,
  (* Y entry deps: sequential id -> sub_type_ids *)
  y_deps : int list Array.array,
  n_types : int,
  (* Exports: (name, trace_id) *)
  exports : (string * int) list,
  (* DISK_THM entries: (trace_id, theory, name) *)
  disk_thms : (int * string * string) list,
  (* Whether file has a C (compute init) entry *)
  has_compute_init : bool
}

(* Growable list accumulator, converted to array at the end *)
fun list_to_array n items default =
  let val arr = Array.array(n, default)
  in List.app (fn (id, v) =>
       if id < n then Array.update(arr, id, v) else ()) items;
     arr
  end

fun read_file_data path : file_data =
  let
    val (instrm, proc) = ReplayTrace.open_trace path
    val ty_count = ref 0
    val tm_count = ref 0
    val heap_parent = ref (NONE : string option)
    val thy_name = ref ""
    val has_name = ref false
    val exports_rev = ref ([] : (string * int) list)
    val disk_thms_rev = ref ([] : (int * string * string) list)
    val has_ci = ref false

    (* P deps stored in a map (sparse trace_ids) *)
    val p_deps_ref = ref (Redblackmap.mkDict Int.compare
      : (int, int list * int list * int list) Redblackmap.dict)
    val p_ids_ref = ref (Redblackset.empty Int.compare)

    (* Y and T deps accumulated as lists, arrays built at end *)
    val y_deps_rev = ref ([] : (int * int list) list)
    val t_term_deps_rev = ref ([] : (int * int list) list)
    val t_type_deps_rev = ref ([] : (int * int list) list)

    fun process_line line =
      let val toks = tokenize line in
      case toks of
        [] => ()
      | ["V", _] => ()  (* version *)
      | ("H" :: hp :: _) =>
          heap_parent := SOME (unescape hp)
      | ("Y" :: id_s :: "V" :: _) =>
          let val id = int_of id_s
          in ty_count := Int.max(!ty_count, id + 1);
             y_deps_rev := (id, []) :: !y_deps_rev
          end
      | ("Y" :: id_s :: "O" :: _ :: _ :: arg_ids) =>
          let val id = int_of id_s
              val deps = List.mapPartial Int.fromString arg_ids
          in ty_count := Int.max(!ty_count, id + 1);
             y_deps_rev := (id, deps) :: !y_deps_rev
          end
      | ("T" :: id_s :: "V" :: _ :: ty_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_term_deps_rev := (id, []) :: !t_term_deps_rev;
             t_type_deps_rev := (id, [int_of ty_s]) :: !t_type_deps_rev
          end
      | ("T" :: id_s :: "C" :: _ :: _ :: ty_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_term_deps_rev := (id, []) :: !t_term_deps_rev;
             t_type_deps_rev := (id, [int_of ty_s]) :: !t_type_deps_rev
          end
      | ("T" :: id_s :: "A" :: f_s :: x_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_term_deps_rev := (id, [int_of f_s, int_of x_s])
                                :: !t_term_deps_rev;
             t_type_deps_rev := (id, []) :: !t_type_deps_rev
          end
      | ("T" :: id_s :: "L" :: v_s :: b_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_term_deps_rev := (id, [int_of v_s, int_of b_s])
                                :: !t_term_deps_rev;
             t_type_deps_rev := (id, []) :: !t_type_deps_rev
          end
      | ("P" :: id_s :: rule :: args) =>
          let val id = int_of id_s
              val parents = extract_parent_ids rule args
              val term_deps = extract_term_ids rule args
              val type_deps = extract_type_ids rule args
          in p_ids_ref := Redblackset.add(!p_ids_ref, id);
             p_deps_ref := Redblackmap.insert(!p_deps_ref, id,
                             (parents, term_deps, type_deps));
             (case rule of
                "DISK_THM" =>
                  disk_thms_rev := (id, unescape (List.nth(args, 0)),
                                    unescape (List.nth(args, 1)))
                                   :: !disk_thms_rev
              | _ => ())
          end
      | ("C" :: _) => has_ci := true
      | ("N" :: name :: _) =>
          (thy_name := unescape name; has_name := true)
      | ("E" :: name :: id_s :: _) =>
          exports_rev := (unescape name, int_of id_s) :: !exports_rev
      | _ => ()
      end

    fun read_all () =
      case TextIO.inputLine instrm of
        NONE => ()
      | SOME line =>
          (process_line (String.substring(line, 0, size line - 1)
                         handle Subscript => line);
           read_all ())
    val _ = read_all ()
    val _ = ReplayTrace.close_trace (instrm, proc)

    val ny = !ty_count
    val nt = !tm_count
  in
    { path = path,
      heap_parent = !heap_parent,
      is_heap = not (!has_name),
      thy_name = !thy_name,
      p_deps = !p_deps_ref,
      p_ids = !p_ids_ref,
      t_term_deps = list_to_array nt (!t_term_deps_rev) [],
      t_type_deps = list_to_array nt (!t_type_deps_rev) [],
      n_terms = nt,
      y_deps = list_to_array ny (!y_deps_rev) [],
      n_types = ny,
      exports = rev (!exports_rev),
      disk_thms = rev (!disk_thms_rev),
      has_compute_init = !has_ci }
  end

(* ------- Heap trace file discovery ------- *)

(* Given a heap path from an H line (e.g. "/home/user/HOL/bin/hol.state0"),
   find the corresponding trace file. Tries .pft.zst, .pft.gz, .pft
   in that order (matching compression preference). *)
fun find_heap_trace_file heap_path =
  let
    val candidates = [heap_path ^ ".pft.zst",
                      heap_path ^ ".pft.gz",
                      heap_path ^ ".pft"]
  in
    case List.find (fn p =>
           OS.FileSys.access(p, [OS.FileSys.A_READ])) candidates of
      SOME p => SOME p
    | NONE => NONE
  end

(* ------- Pass 1: Backward reachability ------- *)

(* Liveness sets for a file. Y and T use arrays (sequential IDs),
   P uses a set (sparse trace_ids). *)
type liveness = {
  live_y : bool Array.array,
  live_t : bool Array.array,
  live_p : int Redblackset.set
}

fun mark_live (data : file_data) (needed_thm_ids : int list)
  : liveness * int list (* unresolved parent trace_ids *) =
  let
    val live_y = Array.array(#n_types data, false)
    val live_t = Array.array(#n_terms data, false)
    val live_p = ref (Redblackset.empty Int.compare)
    val unresolved = ref (Redblackset.empty Int.compare)

    fun mark_thm id =
      if Redblackset.member(!live_p, id) then ()
      else if not (Redblackset.member(#p_ids data, id)) then
        (* This trace_id isn't defined in this file —
           it's a reference to a parent heap *)
        unresolved := Redblackset.add(!unresolved, id)
      else
        let val _ = live_p := Redblackset.add(!live_p, id)
            val (parents, term_deps, type_deps) =
              Redblackmap.find(#p_deps data, id)
        in List.app mark_thm parents;
           List.app mark_term term_deps;
           List.app mark_type type_deps
        end
    and mark_term id =
      if id < 0 orelse id >= #n_terms data orelse
         Array.sub(live_t, id) then ()
      else (Array.update(live_t, id, true);
            List.app mark_term
              (Array.sub(#t_term_deps data, id));
            List.app mark_type
              (Array.sub(#t_type_deps data, id)))
    and mark_type id =
      if id < 0 orelse id >= #n_types data orelse
         Array.sub(live_y, id) then ()
      else (Array.update(live_y, id, true);
            List.app mark_type (Array.sub(#y_deps data, id)))
  in
    List.app mark_thm needed_thm_ids;
    ({live_y = live_y, live_t = live_t, live_p = !live_p},
     Redblackset.listItems (!unresolved))
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

fun remap_args (ry : int -> int) (rt : int -> int) (rp : int -> int)
               rule args =
  case rule of
    "REFL" => [its (rt (int_of (hd args)))]
  | "ASSUME" => [its (rt (int_of (hd args)))]
  | "BETA_CONV" => [its (rt (int_of (hd args)))]
  | "ALPHA" => map (its o rt o int_of) args
  | "ABS" => [its (rp (int_of (List.nth(args,0)))),
              its (rt (int_of (List.nth(args,1))))]
  | "MK_COMB" => map (its o rp o int_of) args
  | "AP_TERM" => [its (rp (int_of (List.nth(args,0)))),
                  its (rt (int_of (List.nth(args,1))))]
  | "AP_THM" => [its (rp (int_of (List.nth(args,0)))),
                 its (rt (int_of (List.nth(args,1))))]
  | "SYM" => [its (rp (int_of (hd args)))]
  | "TRANS" => map (its o rp o int_of) args
  | "EQ_MP" => map (its o rp o int_of) args
  | "EQ_IMP_RULE1" => [its (rp (int_of (hd args)))]
  | "EQ_IMP_RULE2" => [its (rp (int_of (hd args)))]
  | "MP" => map (its o rp o int_of) args
  | "DISCH" => [its (rp (int_of (List.nth(args,0)))),
                its (rt (int_of (List.nth(args,1))))]
  | "INST_TYPE" =>
      its (rp (int_of (hd args))) ::
      map (its o ry o int_of) (tl args)
  | "INST" =>
      its (rp (int_of (hd args))) ::
      map (its o rt o int_of) (tl args)
  | "SUBST" =>
      let val orig = its (rp (int_of (List.nth(args,0))))
          val tmpl = its (rt (int_of (List.nth(args,1))))
          val rest = List.drop(args, 2)
          fun pairs [] = []
            | pairs (v::r::t) =
                its (rt (int_of v)) :: its (rp (int_of r)) :: pairs t
            | pairs _ = []
      in orig :: tmpl :: pairs rest end
  | "SPEC" => [its (rp (int_of (List.nth(args,0)))),
               its (rt (int_of (List.nth(args,1))))]
  | "Specialize" => [its (rp (int_of (List.nth(args,0)))),
                     its (rt (int_of (List.nth(args,1))))]
  | "GEN" => [its (rp (int_of (List.nth(args,0)))),
              its (rt (int_of (List.nth(args,1))))]
  | "GENL" =>
      its (rp (int_of (hd args))) ::
      map (its o rt o int_of) (tl args)
  | "GEN_ABS" =>
      its (rp (int_of (List.nth(args,0)))) ::
      (if List.nth(args,1) = "~" then "~"
       else its (rt (int_of (List.nth(args,1))))) ::
      map (its o rt o int_of) (List.drop(args, 2))
  | "EXISTS" => [its (rp (int_of (List.nth(args,0)))),
                 its (rt (int_of (List.nth(args,1)))),
                 its (rt (int_of (List.nth(args,2))))]
  | "CHOOSE" => [its (rp (int_of (List.nth(args,0)))),
                 its (rp (int_of (List.nth(args,1)))),
                 its (rt (int_of (List.nth(args,2))))]
  | "CONJ" => map (its o rp o int_of) args
  | "CONJUNCT1" => [its (rp (int_of (hd args)))]
  | "CONJUNCT2" => [its (rp (int_of (hd args)))]
  | "DISJ1" => [its (rp (int_of (List.nth(args,0)))),
                its (rt (int_of (List.nth(args,1))))]
  | "DISJ2" => [its (rp (int_of (List.nth(args,0)))),
                its (rt (int_of (List.nth(args,1))))]
  | "DISJ_CASES" => map (its o rp o int_of) args
  | "NOT_INTRO" => [its (rp (int_of (hd args)))]
  | "NOT_ELIM" => [its (rp (int_of (hd args)))]
  | "CCONTR" => [its (rp (int_of (List.nth(args,0)))),
                 its (rt (int_of (List.nth(args,1))))]
  | "Beta" => [its (rp (int_of (hd args)))]
  | "Mk_comb" => map (its o rp o int_of) args
  | "Mk_abs" => map (its o rp o int_of) args
  | "DEF_TYOP" => [its (rp (int_of (List.nth(args,0)))),
                   List.nth(args,1), List.nth(args,2)]
  | "DEF_SPEC" =>
      its (rp (int_of (hd args))) :: tl args
  | "COMPUTE" =>
      its (rt (int_of (hd args))) ::
      map (its o rp o int_of) (tl args)
  | "AXIOM" => [its (rt (int_of (hd args)))]
  | "ORACLE" =>
      List.nth(args,0) ::
      its (rt (int_of (List.nth(args,1)))) ::
      map (its o rt o int_of) (List.drop(args, 2))
  | _ => args

(* ------- Main merge ------- *)

fun thyname_cmp ((t1,n1) : string*string, (t2,n2)) =
  case String.compare(t1,t2) of EQUAL => String.compare(n1,n2)
                               | ord => ord

(* Compare file paths for use as map keys *)
fun path_int_cmp ((p1,i1) : string*int, (p2,i2)) =
  case String.compare(p1,p2) of EQUAL => Int.compare(i1,i2)
                               | ord => ord

fun merge {trace_paths : (string * string) list,
           desired_exports : (string * string) list,
           output_path : string} =
  let
    val err = fn s => TextIO.output(TextIO.stdErr, s)

    (* Build theory name -> file path map *)
    val thy_path_map = List.foldl (fn ((thy, path), m) =>
      Redblackmap.insert(m, thy, path))
      (Redblackmap.mkDict String.compare) trace_paths

    (* ============================================================
       Pass 1: Determine live entries across all needed files
       ============================================================ *)
    val _ = err "Pass 1: determining live entries...\n"

    (* Cache of loaded file data, keyed by canonical path *)
    val file_cache : (string, file_data) Redblackmap.dict ref =
      ref (Redblackmap.mkDict String.compare)

    fun load_file path =
      case Redblackmap.peek(!file_cache, path) of
        SOME data => data
      | NONE =>
        let val data = read_file_data path
        in file_cache := Redblackmap.insert(!file_cache, path, data);
           data
        end

    (* Per-file liveness results, keyed by path *)
    val file_liveness : (string, liveness) Redblackmap.dict ref =
      ref (Redblackmap.mkDict String.compare)

    (* Get or create liveness for a file *)
    fun get_liveness path =
      case Redblackmap.peek(!file_liveness, path) of
        SOME lv => lv
      | NONE =>
        let val data = load_file path
            val lv = {live_y = Array.array(#n_types data, false),
                      live_t = Array.array(#n_terms data, false),
                      live_p = Redblackset.empty Int.compare}
        in file_liveness :=
             Redblackmap.insert(!file_liveness, path, lv);
           lv
        end

    (* Update liveness for a file by merging in new live P ids *)
    fun update_liveness path lv =
      file_liveness := Redblackmap.insert(!file_liveness, path, lv)

    (* Needed ancestor exports: (thy, name) set *)
    val needed_exports = ref (Redblackset.empty thyname_cmp)
    val _ = List.app (fn e =>
      needed_exports := Redblackset.add(!needed_exports, e))
      desired_exports

    (* Track which files have been fully processed *)
    val processed_files = ref (Redblackset.empty String.compare)
    (* Output order for Pass 2 *)
    val output_order = ref ([] : string list)

    (* Given a trace_id not found in file at `path`, search up
       the heap ancestry chain for a file containing it. *)
    fun find_in_heap_chain path trace_id =
      let val data = load_file path
      in case #heap_parent data of
           NONE => NONE
         | SOME hp =>
           case find_heap_trace_file hp of
             NONE =>
               (err ("WARNING: heap trace not found for " ^
                     hp ^ " (referenced from " ^ path ^ ")\n");
                NONE)
           | SOME heap_pft =>
             let val hdata = load_file heap_pft
             in if Redblackset.member(#p_ids hdata, trace_id)
                then SOME heap_pft
                else find_in_heap_chain heap_pft trace_id
             end
      end

    (* Process a file: mark needed entries, recursively process
       ancestors for DISK_THM and unresolved heap references. *)
    fun process_file path needed_thm_ids =
      let
        val data = load_file path

        (* Merge with any previously needed IDs for this file *)
        val prev_lv = get_liveness path
        val all_needed =
          Redblackset.listItems (#live_p prev_lv) @ needed_thm_ids

        val (lv, unresolved) = mark_live data all_needed
      in
        update_liveness path lv;

        (* Handle DISK_THM references: for each live DISK_THM,
           add it to needed ancestor exports *)
        List.app (fn (id, anc_thy, anc_name) =>
          if Redblackset.member(#live_p lv, id) then
            needed_exports :=
              Redblackset.add(!needed_exports, (anc_thy, anc_name))
          else ()) (#disk_thms data);

        (* Handle unresolved parent trace_ids: find them in the
           heap ancestry chain *)
        List.app (fn trace_id =>
          case find_in_heap_chain path trace_id of
            NONE =>
              raise ERR "process_file"
                ("unresolved parent trace_id " ^ its trace_id ^
                 " in " ^ path ^
                 " (not found in any ancestor heap trace)")
          | SOME heap_pft =>
              process_file heap_pft [trace_id])
          unresolved;

        (* Register for output if not already done *)
        if Redblackset.member(!processed_files, path) then ()
        else (processed_files :=
                Redblackset.add(!processed_files, path);
              output_order := path :: !output_order)
      end

    (* Iteratively process until all needed exports are covered.
       New ancestor exports may be discovered during processing. *)
    fun iterate_until_stable () =
      let
        val to_process = ref ([] : (string * int list) list)

        (* Check each needed export *)
        val _ = Redblackset.app (fn (thy, name) =>
          case Redblackmap.peek(thy_path_map, thy) of
            NONE => err ("WARNING: no trace for theory " ^ thy ^ "\n")
          | SOME path =>
            let val data = load_file path
                val lv = get_liveness path
            in case List.find (fn (n, _) => n = name)
                              (#exports data) of
                 NONE =>
                   err ("WARNING: export " ^ thy ^ "." ^ name ^
                        " not found in " ^ path ^ "\n")
               | SOME (_, thm_id) =>
                   if Redblackset.member(#live_p lv, thm_id) then ()
                   else to_process :=
                     (path, [thm_id]) :: !to_process
            end) (!needed_exports)
      in
        if null (!to_process) then ()
        else
          (List.app (fn (path, ids) => process_file path ids)
                    (!to_process);
           (* Recurse: processing may have discovered new
              ancestor exports *)
           iterate_until_stable ())
      end

    val _ = iterate_until_stable ()

    (* Build output order via unified topological sort across all
       files (both heap and theory traces).

       Dependencies:
       - DISK_THM (thy, name) in any file -> the theory file for thy
       - Heap ancestry: a file with H line depends on its parent heap
         (parent heap must be written first so its P entries are in
         heap_thm_map when the child is written)

       Theory files that a heap's DISK_THMs reference must be written
       before the heap, not after. *)

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
        (* DISK_THM deps -> theory file paths *)
        val disk_deps = List.mapPartial (fn (id, anc_thy, _) =>
          if Redblackset.member(#live_p lv, id) then
            Redblackmap.peek(thy_to_path, anc_thy)
          else NONE)
          (#disk_thms data)
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
        disk_deps @ heap_dep
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
          SOME lv => acc + Redblackset.numItems (#live_p lv)
        | NONE => acc) 0 topo

    val _ = err ("Pass 1 done: " ^ its (length topo) ^ " files, " ^
                 its n_live_total ^ " live theorems\n")

    (* ============================================================
       Pass 2: Write merged trace with global dedup and remapping
       ============================================================ *)
    val _ = err "Pass 2: writing merged trace...\n"

    val global_ty_map = ref (Redblackmap.mkDict ty_desc_compare)
    val global_tm_map = ref (Redblackmap.mkDict tm_desc_compare)
    val global_ty_id = ref 0
    val global_tm_id = ref 0
    val global_thm_id = ref 0

    (* (theory, name) -> global thm id, for resolving DISK_THM *)
    val ancestor_exports : (string * string, int) Redblackmap.dict ref =
      ref (Redblackmap.mkDict thyname_cmp)

    (* (file_path, trace_id) -> global thm id, for resolving
       heap parent references *)
    val heap_thm_map : (string * int, int) Redblackmap.dict ref =
      ref (Redblackmap.mkDict path_int_cmp)

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

        val (instrm, proc) = ReplayTrace.open_trace path

        (* Local -> global remap: arrays for Y/T (sequential),
           map for P (sparse trace_ids) *)
        val y_remap = Array.array(#n_types data, ~1)
        val t_remap = Array.array(#n_terms data, ~1)
        val p_remap = ref (Redblackmap.mkDict Int.compare : (int, int) Redblackmap.dict)

        fun ry i = Array.sub(y_remap, i)
        fun rt i = Array.sub(t_remap, i)
        fun rp i =
          case Redblackmap.peek(!p_remap, i) of
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
                         case Redblackmap.peek(!heap_thm_map,
                                               (hpft, i)) of
                           SOME gid => gid
                         | NONE => search hpft
                  end
            in search path end

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
              in if id < Array.length live_t andalso
                    Array.sub(live_t, id) then
                let val desc = case rest of
                      ["V", name, ty_s] =>
                        TmV (unescape name, ry (int_of ty_s))
                    | ["C", thy_s, name_s, ty_s] =>
                        TmC (unescape thy_s, unescape name_s,
                             ry (int_of ty_s))
                    | ["A", f_s, x_s] =>
                        TmA (rt (int_of f_s), rt (int_of x_s))
                    | ["L", v_s, b_s] =>
                        TmL (rt (int_of v_s), rt (int_of b_s))
                    | _ => raise ERR "write_file" "bad T entry"
                in case Redblackmap.peek(!global_tm_map, desc) of
                     SOME gid => Array.update(t_remap, id, gid)
                   | NONE =>
                     let val gid = !global_tm_id
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
                            "T " ^ its gid ^ " A " ^ its f ^
                            " " ^ its x ^ "\n"
                        | TmL (v,b) =>
                            "T " ^ its gid ^ " L " ^ its v ^
                            " " ^ its b ^ "\n")
                     end
                end
              else ()
              end
          | ("P" :: id_s :: "DISK_THM" :: args) =>
              let val id = int_of id_s
              in if Redblackset.member(live_p, id) then
                let val anc_thy = unescape (List.nth(args, 0))
                    val anc_name = unescape (List.nth(args, 1))
                in case Redblackmap.peek(!ancestor_exports,
                                         (anc_thy, anc_name)) of
                     SOME gid =>
                       p_remap :=
                         Redblackmap.insert(!p_remap, id, gid)
                   | NONE =>
                     err ("WARNING: unresolved DISK_THM " ^
                          anc_thy ^ "." ^ anc_name ^ "\n")
                end
              else ()
              end
          | ("P" :: id_s :: rule :: args) =>
              let val id = int_of id_s
              in if Redblackset.member(live_p, id) then
                let val gid = !global_thm_id
                    val remapped = remap_args ry rt rp rule args
                in global_thm_id := gid + 1;
                   p_remap :=
                     Redblackmap.insert(!p_remap, id, gid);
                   TextIO.output(ostrm, "P " ^ its gid ^ " " ^
                     rule ^
                     (if null remapped then ""
                      else " " ^ String.concatWith " " remapped) ^
                     "\n")
                end
              else ()
              end
          | ("C" :: args) =>
              (* Remap C entry — only write if this file has
                 live COMPUTE entries *)
              let
                fun ai n = int_of (List.nth(args, n))
                val cy = its (ry (ai 0))
                val ny' = its (ry (ai 1))
                val rest = List.drop(args, 2)
                val cvals = List.tabulate(29, fn i =>
                  List.nth(rest, 2*i) ^ " " ^
                  its (rt (int_of (List.nth(rest, 2*i + 1)))))
                val rest2 = List.drop(rest, 58)
                val char_pairs =
                  let fun go [] = []
                        | go (n::p::r) =
                            (n ^ " " ^ its (rp (int_of p))) :: go r
                        | go _ = []
                  in go rest2 end
              in TextIO.output(ostrm, "C " ^ cy ^ " " ^ ny' ^ " " ^
                   String.concatWith " " cvals ^
                   (if null char_pairs then ""
                    else " " ^ String.concatWith " " char_pairs) ^
                   "\n")
              end
          | _ => ()  (* skip V, H, N, E, blank lines *)
          end

        fun read_all () =
          case TextIO.inputLine instrm of
            NONE => ()
          | SOME line =>
              (process_line (String.substring(line, 0, size line - 1)
                             handle Subscript => line);
               read_all ())
      in
        read_all ();
        ReplayTrace.close_trace (instrm, proc);

        (* Register this file's exports in ancestor_exports *)
        List.app (fn (name, local_id) =>
          case Redblackmap.peek(!p_remap, local_id) of
            SOME gid =>
              ancestor_exports :=
                Redblackmap.insert(!ancestor_exports,
                                   (#thy_name data, name), gid)
          | NONE => ())
          (#exports data);

        (* If this is a heap trace, register all its live P entries
           in heap_thm_map so theory scripts (and later heaps)
           can resolve parent references into this heap *)
        if #is_heap data then
          Redblackset.app (fn trace_id =>
            case Redblackmap.peek(!p_remap, trace_id) of
              SOME gid =>
                heap_thm_map :=
                  Redblackmap.insert(!heap_thm_map,
                                     (path, trace_id), gid)
            | NONE => ())
            live_p
        else ()
      end

    val _ = List.app (fn path =>
      let val data = load_file path
          val lv = case Redblackmap.peek(!file_liveness, path) of
              SOME lv => lv | NONE => raise ERR "merge" "no liveness"
          val n_live = Redblackset.numItems (#live_p lv)
          val label = if #is_heap data
                      then OS.Path.file path
                      else #thy_name data
      in err ("  " ^ label ^ " (" ^ its n_live ^ " live thms)...\n");
         write_file path
      end) topo

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
  in
    err ("Merged trace: " ^ its (!global_ty_id) ^ " types, " ^
         its (!global_tm_id) ^ " terms, " ^
         its (!global_thm_id) ^ " thms -> " ^
         output_path ^ "\n")
  end

end
