(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step, streaming
   Y/T/P/I entries to the output file. P entries use kernel
   trace_ids for both their own ID and parent references.

   Two kinds of output:
   - Heap builds: write directly to <heapname>.pft
   - Theory scripts: write to .hol/objs/.trace_<pid>.tmp,
     renamed to .hol/objs/<thy>Theory.pft at export time

   Stack encoding: T and P entries maintain implicit stacks.
   Recent entries are referenced by stack position (~k for terms,
   ^k for theorems) instead of explicit IDs, reducing trace size.
   Peephole: consecutive SPEC/Specialize chains are collapsed
   into SPECL/SPECIALIZEL compound entries.

   NOT in the trust boundary: output is verified by ReplayTrace.
*)

structure TraceRecord :> TraceRecord =
struct

open HolKernel

val ERR = mk_HOL_ERR "TraceRecord"
val its = Int.toString

(* ------- String escaping ------- *)

fun escape_string s =
  if CharVector.all (fn c => Char.isPrint c andalso c <> #" ") s
  then s
  else "\"" ^ String.translate
     (fn #"\"" => "\\\""
       | #"\\" => "\\\\"
       | #"\n" => "\\n"
       | c => if Char.ord c < 0x20
              then "\\x" ^ StringCvt.padLeft #"0" 2
                     (Int.fmt StringCvt.HEX (Char.ord c))
              else str c) s ^ "\""

val esc = escape_string

(* ------- Command line parsing ------- *)

fun find_arg flag args =
  let fun find [] = NONE
        | find (s :: rest) =
            if s = flag then
              (case rest of p :: _ => SOME p | [] => NONE)
            else if String.isPrefix (flag ^ "=") s then
              SOME (String.extract(s, size flag + 1, NONE))
            else find rest
  in find args end

fun find_heap_output () = find_arg "-o" (CommandLine.arguments())

(* Parent heap path derived from stale output path during heap restore.
   Set by recover_stale when detecting a new process via PID change. *)
val stale_parent_heap = ref (NONE : string option)

fun find_heap_input () =
  case !stale_parent_heap of
    SOME p => SOME p
  | NONE =>
    let val args = CommandLine.arguments ()
        fun mkabs p = OS.Path.mkAbsolute {
              path = p, relativeTo = OS.FileSys.getDir ()}
    in case find_arg "--holstate" args of
         SOME p => SOME (mkabs p)
       | NONE => Option.map mkabs (find_arg "-b" args)
    end

(* ------- Output stream ------- *)

val output_strm : TextIO.outstream option ref = ref NONE
val output_path_ref : string option ref = ref NONE
val keep_on_exit : bool ref = ref false

(* Cached output stream for fast path in ensure_stream.
   Reset to NONE by close_output and reset_for_new_session. *)
val cached_strm : TextIO.outstream option ref = ref NONE

(* Reset function ref — set after intern tables are defined *)
val reset_for_new_session = ref (fn () => ())

fun write_header s heap_input =
  (TextIO.output(s, "V 1\n");
   case heap_input of
     SOME hp => TextIO.output(s, "H " ^ esc hp ^ "\n")
   | NONE => ())

val objdir = ".hol/objs"

fun open_temp_file () =
  let
    val _ = if OS.FileSys.access(objdir, []) andalso
               OS.FileSys.isDir objdir
            then ()
            else raise ERR "open_temp_file"
                   (objdir ^ " does not exist")
    val pid = SysWord.toString
                (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
    val path = OS.Path.concat(objdir,
                 ".trace_" ^ pid ^ ".tmp")
    val _ = output_path_ref := SOME path
    val _ = keep_on_exit := false
    val s = TextIO.openOut path
  in
    output_strm := SOME s;
    write_header s (find_heap_input ());
    s
  end

fun open_heap_file path =
  let
    val pft = OS.Path.mkAbsolute {
                path = path ^ ".pft",
                relativeTo = OS.FileSys.getDir ()}
    val s = TextIO.openOut pft
  in
    output_strm := SOME s;
    output_path_ref := SOME pft;
    keep_on_exit := true;
    write_header s (find_heap_input ());
    s
  end

val cleanup_ref : (unit -> unit) ref = ref (fn () => ())

(* Detect new process after heap restore by comparing PIDs.
   After heap restore, the output stream from the heap build is
   stale (closed fd). The old approach (zero-byte TextIO.output
   probe) was unreliable: buffered I/O may never touch the fd
   for an empty write, so it silently succeeds on a stale stream.
   PID comparison is robust — after heap restore, getpid() returns
   the new process's PID, which differs from the saved one.

   recover_stale closes the stale stream, resets all intern state,
   remembers the parent heap path for the H line, re-registers the
   atExit handler (which doesn't survive heap save/restore), and
   opens a new output file. Called from ensure_stream on PID
   mismatch, which is the entry point for all output paths
   (record_hook and the C/O TheoryDelta hook). *)
val session_pid =
  ref (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))

fun recover_stale () =
  let val stale = !output_path_ref
      fun is_tmp p = String.isSuffix ".tmp" p
      fun strip_pft p =
        if String.isSuffix ".pft" p then
          SOME (String.substring(p, 0, size p - 4))
        else NONE
  in
    (case !output_strm of
       SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
     | NONE => ());
    output_strm := NONE; output_path_ref := NONE;
    (!reset_for_new_session) ();
    (* Remember the parent heap for the H line *)
    stale_parent_heap :=
      (case stale of
         SOME p => if is_tmp p then NONE else strip_pft p
       | NONE => NONE);
    (case stale of
       SOME p => if is_tmp p then
                   (OS.FileSys.remove p handle _ => ())
                 else ()
     | NONE => ());
    (case find_heap_output () of
       SOME path => ignore (open_heap_file path)
     | NONE => ignore (open_temp_file ()));
    OS.Process.atExit (fn () => (!cleanup_ref) ())
  end



fun out_strm () =
  case !output_strm of
    NONE => open_temp_file ()
  | SOME s => s

fun close_output () =
  (case !output_strm of
     SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
   | NONE => ();
   output_strm := NONE;
   cached_strm := NONE)

(* ------- Output primitives ------- *)

(* Write directly to the buffered stream, avoiding intermediate
   string allocation from ^ concatenation. Each TextIO.output
   call copies bytes into the internal buffer with no heap
   allocation (except for Int.toString results). *)

fun outs s str = TextIO.output(s, str)
fun outi s n = TextIO.output(s, Int.toString n)

(* ------- Intern map key types ------- *)

(* Descriptor-based keys: contain only ints and strings, not
   term/type values. This avoids pinning large terms alive in
   the intern maps, allowing GC to collect intermediate proof
   terms that are no longer referenced elsewhere. Type and term
   comparisons on descriptors are O(1) (int/string comparisons),
   eliminating the O(spine_depth) structural comparisons that
   made Term.compare quadratic on deep application spines. *)

datatype ty_desc = TyV of string | TyO of string * string * int list

fun ty_desc_compare (TyV a, TyV b) = String.compare(a, b)
  | ty_desc_compare (TyV _, _) = LESS
  | ty_desc_compare (_, TyV _) = GREATER
  | ty_desc_compare (TyO(t1,n1,a1), TyO(t2,n2,a2)) =
      (case String.compare(t1,t2) of EQUAL =>
        (case String.compare(n1,n2) of EQUAL =>
          List.collate Int.compare (a1,a2)
        | ord => ord)
      | ord => ord)

(* Term map: keyed by (hash, term). Comparisons resolve by hash
   first (O(1) int compare), falling back to Term.compare only on
   hash collision.  This avoids the O(spine_depth) comparisons
   that made the old pure Term.compare approach quadratic on deep
   application spines, without needing to decompose terms into
   descriptors (which required O(body_size) dest_abs for lambdas). *)
fun tm_keyed_compare ((h1, t1 : Term.term), (h2, t2)) =
  case Int.compare(h1, h2) of
    EQUAL => Term.compare(t1, t2)
  | ord => ord

(* ------- Hash-indexed pointer-equality cache ------- *)

(* Direct-mapped cache checked via pointer equality, used as a
   fast front-end for the descriptor-based term intern map.
   Indexed by Term.hash, which is a bounded-depth O(1) structural
   hash computed inside the kernel (with access to internal term
   constructors, including Abs binder names without substitution).
   Avoids the O(term_size) recursive descent for terms that are
   pointer-identical to recently interned values. Pins at most
   CACHE_SIZE terms, bounding its memory footprint. *)

val CACHE_SIZE = 65536

val tm_cache : (Term.term * int) option Array.array ref =
  ref (Array.array(CACHE_SIZE, NONE))

fun cache_lookup tm =
  let val i = Term.hash tm mod CACHE_SIZE
  in case Array.sub(!tm_cache, i) of
       SOME(t, id) => if Portable.pointer_eq(t, tm) then SOME id else NONE
     | NONE => NONE
  end

fun cache_insert tm id =
  let val i = Term.hash tm mod CACHE_SIZE
  in Array.update(!tm_cache, i, SOME(tm, id)) end

(* ------- Write-side stacks for stack encoding ------- *)

(* Term and theorem stacks maintain the last STACK_DEPTH IDs
   written, enabling ~k (term) and ^k (theorem) references.
   Each T entry pushes onto the term stack; each P entry pushes
   onto the theorem stack. References within STACK_DEPTH of the
   top use the compact ~k/^k notation instead of explicit IDs. *)

val STACK_DEPTH = 16

val w_tstack = Array.array(STACK_DEPTH, ~1)
val w_tstack_ptr = ref 0

fun push_tstack id =
  (Array.update(w_tstack, !w_tstack_ptr, id);
   w_tstack_ptr := (!w_tstack_ptr + 1) mod STACK_DEPTH)

fun find_tstack id =
  let val p = !w_tstack_ptr
      fun search k =
        if k >= STACK_DEPTH then NONE
        else if Array.sub(w_tstack,
                  (p - 1 - k + STACK_DEPTH) mod STACK_DEPTH) = id
             then SOME k
             else search (k + 1)
  in search 0 end

val w_pstack = Array.array(STACK_DEPTH, ~1)
val w_pstack_ptr = ref 0

fun push_pstack id =
  (Array.update(w_pstack, !w_pstack_ptr, id);
   w_pstack_ptr := (!w_pstack_ptr + 1) mod STACK_DEPTH)

fun find_pstack id =
  let val p = !w_pstack_ptr
      fun search k =
        if k >= STACK_DEPTH then NONE
        else if Array.sub(w_pstack,
                  (p - 1 - k + STACK_DEPTH) mod STACK_DEPTH) = id
             then SOME k
             else search (k + 1)
  in search 0 end

fun reset_stacks () =
  (Array.modify (fn _ => ~1) w_tstack; w_tstack_ptr := 0;
   Array.modify (fn _ => ~1) w_pstack; w_pstack_ptr := 0)

(* Output a term reference: ~k if in stack, else explicit ID *)
fun out_tref s id =
  case find_tstack id of
    SOME k => (outs s "~"; outi s k)
  | NONE => outi s id

(* Output a theorem reference: ^k if in stack, else explicit ID *)
fun out_pref s id =
  case find_pstack id of
    SOME k => (outs s "^"; outi s k)
  | NONE => outi s id

(* ------- Type interning (writes Y entries inline) ------- *)

(* Types are small and few — descriptor maps without caching.
   No stack encoding for types (Y entries are ~1% of lines). *)

val ty_map = ref (Redblackmap.mkDict ty_desc_compare)
val ty_counter = ref 0

fun intern_type ty =
  let
    val desc =
      if Type.is_vartype ty then TyV (Type.dest_vartype ty)
      else let val {Thy, Tyop, Args} = Type.dest_thy_type ty
           in TyO (Thy, Tyop, map intern_type Args) end
  in
    case Redblackmap.peek(!ty_map, desc) of
      SOME id => id
    | NONE =>
      let val id = !ty_counter
          val _ = ty_counter := id + 1
          val _ = ty_map := Redblackmap.insert(!ty_map, desc, id)
          val s = out_strm ()
      in (case desc of
            TyV name =>
              (outs s "Y "; outi s id; outs s " V ";
               outs s (esc name); outs s "\n")
          | TyO (thy, tyop, arg_ids) =>
              (outs s "Y "; outi s id; outs s " O ";
               outs s (esc thy); outs s " "; outs s (esc tyop);
               List.app (fn a => (outs s " "; outi s a)) arg_ids;
               outs s "\n"));
         id
      end
  end

val iY = intern_type

(* ------- Term interning (writes T entries, pushes term stack) ------- *)

(* Hash-keyed term map fronted by a pointer-eq cache.
   Fast path: cache hit via pointer equality → O(1).
   Slow path: map lookup via (hash, term) key → O(log N) int
   comparisons, with rare Term.compare fallback on hash collision.
   Each newly written T entry pushes onto the term stack. *)

val tm_map = ref (Redblackmap.mkDict tm_keyed_compare)
val tm_counter = ref 0

fun intern_term tm =
  case cache_lookup tm of
    SOME id => id
  | NONE =>
    let val key = (Term.hash tm, tm)
    in
      case Redblackmap.peek(!tm_map, key) of
        SOME id => (cache_insert tm id; id)
      | NONE =>
        let val id = !tm_counter
            val _ = tm_counter := id + 1
            val _ = tm_map := Redblackmap.insert(!tm_map, key, id)
            val _ = cache_insert tm id
            val s = out_strm ()
        in (case Term.dest_term tm of
              Term.VAR (name, ty) =>
                let val tyid = intern_type ty
                in outs s "T "; outi s id; outs s " V ";
                   outs s (esc name); outs s " "; outi s tyid;
                   outs s "\n"
                end
            | Term.CONST {Thy, Name, Ty} =>
                let val tyid = intern_type Ty
                in outs s "T "; outi s id; outs s " C ";
                   outs s (esc Thy); outs s " "; outs s (esc Name);
                   outs s " "; outi s tyid; outs s "\n"
                end
            | Term.COMB (f, x) =>
                let val fid = intern_term f
                    val xid = intern_term x
                in outs s "T "; outi s id; outs s " A ";
                   out_tref s fid; outs s " "; out_tref s xid;
                   outs s "\n"
                end
            | Term.LAMB (v, b) =>
                let val vid = intern_term v
                    val bid = intern_term b
                in outs s "T "; outi s id; outs s " L ";
                   out_tref s vid; outs s " "; out_tref s bid;
                   outs s "\n"
                end);
           push_tstack id;
           id
        end
    end

val iT = intern_term

(* ------- DEF_SPEC/DEF_TYOP tracking for C/O filtering ------- *)

(* Constants introduced by DEF_SPEC — keyed by (thy, name) *)
val defined_consts : (string * string) Redblackset.set ref =
  ref (Redblackset.empty
         (fn ((t1,n1),(t2,n2)) =>
           case String.compare(t1,t2) of
             EQUAL => String.compare(n1,n2)
           | ord => ord))

(* Type operators introduced by DEF_TYOP — keyed by (thy, tyop) *)
val defined_types : (string * string) Redblackset.set ref =
  ref (Redblackset.empty
         (fn ((t1,n1),(t2,n2)) =>
           case String.compare(t1,t2) of
             EQUAL => String.compare(n1,n2)
           | ord => ord))

val _ = reset_for_new_session := (fn () => (
  ty_map := Redblackmap.mkDict ty_desc_compare;
  tm_map := Redblackmap.mkDict tm_keyed_compare;
  ty_counter := 0;
  tm_counter := 0;
  tm_cache := Array.array(CACHE_SIZE, NONE);
  cached_strm := NONE;
  reset_stacks ();
  defined_consts := Redblackset.empty
    (fn ((t1,n1),(t2,n2)) =>
      case String.compare(t1,t2) of
        EQUAL => String.compare(n1,n2)
      | ord => ord);
  defined_types := Redblackset.empty
    (fn ((t1,n1),(t2,n2)) =>
      case String.compare(t1,t2) of
        EQUAL => String.compare(n1,n2)
      | ord => ord)
))

(* ------- Output helpers ------- *)

fun ensure_stream () =
  let val cur_pid = Posix.Process.pidToWord (Posix.ProcEnv.getpid ())
  in if cur_pid = !session_pid then
       (case !cached_strm of
          SOME s => s
        | NONE => let val s = out_strm ()
                  in cached_strm := SOME s; s end)
     else
       (session_pid := cur_pid; recover_stale ();
        let val s = out_strm ()
        in cached_strm := SOME s; s end)
  end

(* Write the "P <id>" prefix that starts most entries *)
fun outp s r = (outs s "P "; outi s (Thm.trace_id r))

(* Write a theorem parent reference: " <^k or trace_id>" *)
fun outth s th = (outs s " "; out_pref s (Thm.trace_id th))

(* Record a line for C/O entries and other non-hot-path uses *)
fun record_line line =
  let val s = ensure_stream ()
  in outs s line; outs s "\n" end

(* ------- Peephole: SPEC/Specialize chain accumulator ------- *)

(* Consecutive SPEC (or Specialize) entries where each uses the
   previous result as its parent are collapsed into a single
   SPECL (or SPECIALIZEL) compound entry. This reduces the
   number of P entries in the trace. The replayer executes the
   compound by applying SPEC (or Specialize) repeatedly.

   The chain accumulator holds the state of the current chain
   being built. It is flushed when a non-matching entry arrives,
   or at close/export time. *)

datatype spec_kind = SK_SPEC | SK_Specialize

type spec_chain_state = {
  first_parent_id: int,    (* trace_id of the first SPEC's parent *)
  term_ids_rev: int list,  (* term IDs in reverse order *)
  result_id: int,          (* trace_id of the most recent result *)
  kind: spec_kind
}

val spec_chain : spec_chain_state option ref = ref NONE

(* Add spec_chain reset to session reset (spec_chain defined after
   the initial reset_for_new_session assignment, so patch it here) *)
val prev_reset = !reset_for_new_session
val _ = reset_for_new_session :=
  (fn () => (prev_reset (); spec_chain := NONE))

(* Flush the accumulated SPEC chain to the output stream.
   For a single entry, writes a normal SPEC/Specialize line.
   For multiple entries, writes SPECL/SPECIALIZEL. *)
fun flush_spec_chain s =
  case !spec_chain of
    NONE => ()
  | SOME {first_parent_id, term_ids_rev, result_id, kind} =>
    let val terms = rev term_ids_rev
    in
      spec_chain := NONE;
      outs s "P "; outi s result_id;
      (case (kind, terms) of
        (SK_SPEC, [t]) =>
          (outs s " SPEC "; out_pref s first_parent_id;
           outs s " "; out_tref s t)
      | (SK_Specialize, [t]) =>
          (outs s " Specialize "; out_pref s first_parent_id;
           outs s " "; out_tref s t)
      | (SK_SPEC, _) =>
          (outs s " SPECL "; out_pref s first_parent_id;
           List.app (fn t => (outs s " "; out_tref s t)) terms)
      | (SK_Specialize, _) =>
          (outs s " SPECIALIZEL "; out_pref s first_parent_id;
           List.app (fn t => (outs s " "; out_tref s t)) terms));
      outs s "\n";
      push_pstack result_id
    end

(* Try to extend the current SPEC chain with a new SPEC/Specialize
   entry. If the new entry's parent matches the chain's result and
   the kind matches, extend. Otherwise flush and start new chain. *)
fun push_spec_chain s (rid, parent_id, term_id, kind) =
  case !spec_chain of
    NONE =>
      spec_chain := SOME {
        first_parent_id = parent_id,
        term_ids_rev = [term_id],
        result_id = rid,
        kind = kind
      }
  | SOME chain =>
      if #kind chain = kind andalso #result_id chain = parent_id
      then
        spec_chain := SOME {
          first_parent_id = #first_parent_id chain,
          term_ids_rev = term_id :: #term_ids_rev chain,
          result_id = rid,
          kind = kind
        }
      else
        (flush_spec_chain s;
         spec_chain := SOME {
           first_parent_id = parent_id,
           term_ids_rev = [term_id],
           result_id = rid,
           kind = kind
         })

(* ------- Trace hook ------- *)

fun record_hook (step : (thm, term, hol_type) Thm.trace_step) =
  let val s = ensure_stream () in
  case step of
    Thm.TR_ASSUME (r, tm) =>
      let val t = iT tm val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " ASSUME "; out_tref s t; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_REFL (r, tm) =>
      let val t = iT tm val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " REFL "; out_tref s t; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_BETA_CONV (r, tm) =>
      let val t = iT tm val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " BETA_CONV "; out_tref s t; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_ALPHA (r, t1, t2) =>
      let val i1 = iT t1 val i2 = iT t2 val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " ALPHA "; out_tref s i1;
         outs s " "; out_tref s i2; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_ABS (r, th, v) =>
      let val vid = iT v val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " ABS"; outth s th;
         outs s " "; out_tref s vid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_MK_COMB (r, f, x) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " MK_COMB"; outth s f; outth s x; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_AP_TERM (r, th, f) =>
      let val fid = iT f val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " AP_TERM"; outth s th;
         outs s " "; out_tref s fid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_AP_THM (r, th, tm) =>
      let val t = iT tm val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " AP_THM"; outth s th;
         outs s " "; out_tref s t; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_SYM (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " SYM"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_TRANS (r, a, b) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " TRANS"; outth s a; outth s b; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_EQ_MP (r, a, b) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " EQ_MP"; outth s a; outth s b; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_EQ_IMP_RULE1 (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " EQ_IMP_RULE1"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_EQ_IMP_RULE2 (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " EQ_IMP_RULE2"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_MP (r, a, b) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " MP"; outth s a; outth s b; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_DISCH (r, th, w) =>
      let val wid = iT w val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " DISCH"; outth s th;
         outs s " "; out_tref s wid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_INST_TYPE (r, th, theta) =>
      let val pairs = map (fn {redex,residue} =>
            (iY redex, iY residue)) theta
          val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " INST_TYPE"; outth s th;
         List.app (fn (a,b) =>
           (outs s " "; outi s a; outs s " "; outi s b)) pairs;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_INST (r, th, theta) =>
      let val pairs = map (fn {redex,residue} =>
            (iT redex, iT residue)) theta
          val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " INST"; outth s th;
         List.app (fn (a,b) =>
           (outs s " "; out_tref s a;
            outs s " "; out_tref s b)) pairs;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_SUBST (r, repls, template, th) =>
      let val tid = iT template
          val rpairs = map (fn {redex, residue} =>
            (iT redex, Thm.trace_id residue)) repls
          val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " SUBST"; outth s th;
         outs s " "; out_tref s tid;
         List.app (fn (a,b) =>
           (outs s " "; out_tref s a;
            outs s " "; out_pref s b)) rpairs;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_SPEC (r, th, t) =>
      let val tid = iT t
      in push_spec_chain s
           (Thm.trace_id r, Thm.trace_id th, tid, SK_SPEC)
      end
  | Thm.TR_Specialize (r, th, t) =>
      let val tid = iT t
      in push_spec_chain s
           (Thm.trace_id r, Thm.trace_id th, tid, SK_Specialize)
      end
  | Thm.TR_Specialize_thm (r, th_arg, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " Specialize_thm"; outth s th_arg; outth s th;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_GEN (r, th, x) =>
      let val xid = iT x val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " GEN"; outth s th;
         outs s " "; out_tref s xid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_GENL (r, th, vs) =>
      let val vids = map iT vs val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " GENL"; outth s th;
         List.app (fn v => (outs s " "; out_tref s v)) vids;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_GEN_ABS (r, th, opt, vs) =>
      let val oid = Option.map iT opt
          val vids = map iT vs
          val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " GEN_ABS"; outth s th;
         outs s " ";
         (case oid of SOME t => out_tref s t | NONE => outs s "~");
         List.app (fn v => (outs s " "; out_tref s v)) vids;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_EXISTS (r, th, w, t) =>
      let val wid = iT w val tid = iT t val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " EXISTS"; outth s th;
         outs s " "; out_tref s wid;
         outs s " "; out_tref s tid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_CHOOSE (r, xth, bth, v) =>
      let val vid = iT v val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " CHOOSE"; outth s xth; outth s bth;
         outs s " "; out_tref s vid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_CONJ (r, a, b) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " CONJ"; outth s a; outth s b; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_CONJUNCT1 (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " CONJUNCT1"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_CONJUNCT2 (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " CONJUNCT2"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_DISJ1 (r, th, w) =>
      let val wid = iT w val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " DISJ1"; outth s th;
         outs s " "; out_tref s wid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_DISJ2 (r, th, w) =>
      let val wid = iT w val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " DISJ2"; outth s th;
         outs s " "; out_tref s wid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_DISJ_CASES (r, d, a, b) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " DISJ_CASES"; outth s d; outth s a; outth s b;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_NOT_INTRO (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " NOT_INTRO"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_NOT_ELIM (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " NOT_ELIM"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_CCONTR (r, fth, w) =>
      let val wid = iT w val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " CCONTR"; outth s fth;
         outs s " "; out_tref s wid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_Beta (r, th) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " Beta"; outth s th; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_Mk_comb (r, orig, f, x) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " Mk_comb"; outth s orig; outth s f; outth s x;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_Mk_abs (r, orig, body, _) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " Mk_abs"; outth s orig; outth s body;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_REFL_RATOR (r, parent) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " REFL_RATOR"; outth s parent; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_REFL_RAND (r, parent) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " REFL_RAND"; outth s parent; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_REFL_BODY (r, parent) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " REFL_BODY"; outth s parent; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_DEF_TYOP (r, wit, thy, tyop) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         defined_types :=
           Redblackset.add(!defined_types, (thy, tyop));
         outp s r; outs s " DEF_TYOP"; outth s wit;
         outs s " "; outs s (esc thy);
         outs s " "; outs s (esc tyop); outs s "\n";
         push_pstack rid
      end
  | Thm.TR_DEF_SPEC (r, wit, thyname, cnames) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         List.app (fn c =>
           defined_consts :=
             Redblackset.add(!defined_consts, (thyname, c))) cnames;
         outp s r; outs s " DEF_SPEC"; outth s wit;
         outs s " "; outs s (esc thyname);
         List.app (fn c => (outs s " "; outs s (esc c))) cnames;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_COMPUTE (r, code_eqs, tm) =>
      let val tid = iT tm val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " COMPUTE "; out_tref s tid;
         List.app (fn eq => outth s eq) code_eqs;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_COMPUTE_INIT (cval_terms, cval_type, num_type, char_eqns) =>
      let val cyid = iY cval_type
          val nyid = iY num_type
          val cv_pairs = map (fn (name, tm) => (name, iT tm)) cval_terms
      in flush_spec_chain s;
         outs s "I "; outi s cyid; outs s " "; outi s nyid;
         List.app (fn (name, tid) =>
           (outs s " "; outs s (esc name); outs s " "; out_tref s tid))
           cv_pairs;
         List.app (fn (name, th) =>
           (outs s " "; outs s (esc name); outth s th)) char_eqns;
         outs s "\n"
      end
  | Thm.TR_ORACLE (r, tg) =>
      let val (hyps, c) = Thm.dest_thm r
          val cid = iT c
          val hids = map iT hyps
          val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " ORACLE "; outs s (esc tg);
         outs s " "; out_tref s cid;
         List.app (fn h => (outs s " "; out_tref s h)) hids;
         outs s "\n";
         push_pstack rid
      end
  | Thm.TR_AXIOM (r, c) =>
      let val name = case Tag.axioms_of (Thm.tag r) of
                       [n] => Nonce.dest n
                     | _ => raise ERR "record_hook"
                              "AXIOM: expected exactly one axiom nonce"
          val cid = iT c
          val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " AXIOM "; outs s (esc name);
         outs s " "; out_tref s cid; outs s "\n";
         push_pstack rid
      end
  | Thm.TR_NAME (r, src_thy, name) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " NAME ";
         outs s (esc src_thy); outs s " "; outs s (esc name); outs s "\n";
         push_pstack rid
      end
  | Thm.TR_LOAD (r, src_thy, src_trace_id) =>
      let val rid = Thm.trace_id r
      in flush_spec_chain s;
         outp s r; outs s " LOAD ";
         outs s (esc src_thy); outs s " "; outi s src_trace_id;
         outs s "\n";
         push_pstack rid
      end
  end

(* ------- Cleanup and reset ------- *)

fun flush_before_close () =
  case !output_strm of
    SOME s => (flush_spec_chain s handle _ => ())
  | NONE => ()

fun cleanup () =
  (flush_before_close ();
   close_output () handle _ => ();
   if not (!keep_on_exit) then
     case !output_path_ref of
       SOME p => (OS.FileSys.remove p handle _ => ())
     | NONE => ()
   else
     (* Heap trace: compress the completed .pft file *)
     case !output_path_ref of
       SOME p => (ignore (TraceCompress.compress p) handle _ => ())
     | NONE => ())

val _ = cleanup_ref := cleanup

fun trace_reset () =
  (flush_before_close ();
   close_output ();
   output_path_ref := NONE;
   keep_on_exit := false;
   (!reset_for_new_session) ())

(* ------- Export hook (theory export) ------- *)

fun export_hook thyname (_:string list) all_thms =
  let
    val () = flush_before_close ()
    val () = close_output ()
    val temp = case !output_path_ref of
                 SOME p => p
               | NONE => ""
  in
    if temp = "" then () else
    let
      val final_name = thyname ^ "Theory.pft"

      (* Write N and E lines to the temp file *)
      val s = TextIO.openAppend temp
      val _ = TextIO.output(s, "N " ^ esc thyname ^ "\n")
      val _ = List.app (fn (name, th) =>
        TextIO.output(s, "E " ^ esc name ^ " " ^
          its (Thm.trace_id th) ^ "\n")) all_thms
      val _ = TextIO.closeOut s

      (* Put theory trace files in .hol/objs/ if it exists *)
      val actual_path =
        let val objdir = ".hol/objs"
        in if OS.FileSys.access(objdir, []) andalso OS.FileSys.isDir objdir
           then OS.Path.concat(objdir, final_name)
           else final_name
        end

      val _ = OS.FileSys.rename {old = temp, new = actual_path}
      val final = TraceCompress.compress actual_path
      val _ = Feedback.HOL_MESG ("Proof trace: " ^ final)
    in () end;
    trace_reset ()
  end
  handle e =>
    (Feedback.HOL_WARNING "TraceRecord" "export_hook"
       ("export failed: " ^ General.exnMessage e);
     trace_reset ())

(* ------- Public API ------- *)

fun is_active () = isSome (!Thm.trace_hook)
fun trace_step_count () = !Thm.trace_counter

(* ------- Activation ------- *)

fun activate () = (
  Thm.trace_hook := SOME record_hook;
  Thm.trace_export_hook := SOME export_hook;
  (* Emit C/O for constants/types not already defined by
     DEF_SPEC/DEF_TYOP *)
  Theory.register_hook (
    "TraceRecord.new_const_type",
    fn TheoryDelta.NewConstant {Thy, Name} =>
         (ignore (ensure_stream ());
          if Redblackset.member(!defined_consts, (Thy, Name))
          then ()
          else
            let val s = out_strm ()
                val tyid = iY (Term.type_of
                           (Term.prim_mk_const {Thy=Thy, Name=Name}))
            in outs s "C "; outs s (esc Thy); outs s " ";
               outs s (esc Name); outs s " "; outi s tyid;
               outs s "\n"
            end)
     | TheoryDelta.NewTypeOp {Thy, Name} =>
         (ignore (ensure_stream ());
          if Redblackset.member(!defined_types, (Thy, Name))
          then ()
          else
            (case Type.op_arity {Thy=Thy, Tyop=Name} of
               SOME a =>
                 let val s = out_strm ()
                 in outs s "O "; outs s (esc Thy); outs s " ";
                    outs s (esc Name); outs s " "; outi s a;
                    outs s "\n"
                 end
             | NONE => ()))
     | _ => ()
  );
  OS.Process.atExit cleanup
)

val _ = case OS.Process.getEnv "HOL_TRACE_PROOFS" of
          SOME _ =>
          let val _ = activate ()
          in case find_heap_output () of
               SOME path => ignore (open_heap_file path)
             | NONE => ()
          end
        | NONE => ()

end
