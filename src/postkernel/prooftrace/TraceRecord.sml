(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step, streaming
   Y/T/P/I entries to the output file. P entries use kernel
   trace_ids for both their own ID and parent references.

   Two kinds of output:
   - Heap builds: write directly to <heapname>.pft
   - Theory scripts: write to .hol/objs/.trace_<pid>.tmp,
     renamed to .hol/objs/<thy>Theory.pft at export time

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

(* ------- Intern map key types ------- *)

(* Descriptor-based keys: contain only ints and strings, not
   term/type values. This avoids pinning large terms alive in
   the intern maps, allowing GC to collect intermediate proof
   terms that are no longer referenced elsewhere. Type and term
   comparisons on descriptors are O(1) (int/string comparisons),
   eliminating the O(spine_depth) structural comparisons that
   made Term.compare quadratic on deep application spines. *)

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

(* ------- Type interning (writes Y entries inline) ------- *)

(* Types are small and few — descriptor maps without caching. *)

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
              TextIO.output(s, "Y " ^ its id ^ " V " ^
                esc name ^ "\n")
          | TyO (thy, tyop, arg_ids) =>
              TextIO.output(s, "Y " ^ its id ^ " O " ^
                esc thy ^ " " ^ esc tyop ^
                (if null arg_ids then ""
                 else " " ^ String.concatWith " "
                               (map its arg_ids)) ^ "\n"));
         id
      end
  end

val iY = intern_type

(* ------- Term interning (writes T entries inline) ------- *)

(* Descriptor-keyed map for structural dedup, fronted by a
   hash-indexed pointer-eq cache for O(1) re-lookup of the
   same ML value. *)

val tm_map = ref (Redblackmap.mkDict tm_desc_compare)
val tm_counter = ref 0

fun intern_term tm =
  case cache_lookup tm of
    SOME id => id
  | NONE =>
    let
      val desc = case Term.dest_term tm of
          Term.VAR (name, ty) => TmV (name, intern_type ty)
        | Term.CONST {Thy, Name, Ty} => TmC (Thy, Name, intern_type Ty)
        | Term.COMB (f, x) => TmA (intern_term f, intern_term x)
        | Term.LAMB (v, b) => TmL (intern_term v, intern_term b)
    in
      case Redblackmap.peek(!tm_map, desc) of
        SOME id => (cache_insert tm id; id)
      | NONE =>
        let val id = !tm_counter
            val _ = tm_counter := id + 1
            val _ = tm_map := Redblackmap.insert(!tm_map, desc, id)
            val _ = cache_insert tm id
            val s = out_strm ()
        in (case desc of
              TmV (name, tyid) =>
                TextIO.output(s, "T " ^ its id ^ " V " ^
                  esc name ^ " " ^ its tyid ^ "\n")
            | TmC (thy, name, tyid) =>
                TextIO.output(s, "T " ^ its id ^ " C " ^
                  esc thy ^ " " ^ esc name ^ " " ^
                  its tyid ^ "\n")
            | TmA (fid, xid) =>
                TextIO.output(s, "T " ^ its id ^ " A " ^
                  its fid ^ " " ^ its xid ^ "\n")
            | TmL (vid, bid) =>
                TextIO.output(s, "T " ^ its id ^ " L " ^
                  its vid ^ " " ^ its bid ^ "\n"));
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
  tm_map := Redblackmap.mkDict tm_desc_compare;
  ty_counter := 0;
  tm_counter := 0;
  tm_cache := Array.array(CACHE_SIZE, NONE);
  cached_strm := NONE;
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

(* Write directly to the buffered stream, avoiding intermediate
   string allocation from ^ concatenation. Each TextIO.output
   call copies bytes into the internal buffer with no heap
   allocation (except for Int.toString results). *)

fun outs s str = TextIO.output(s, str)
fun outi s n = TextIO.output(s, Int.toString n)

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

(* Write the "P <id> " prefix that starts most entries *)
fun outp s r = (outs s "P "; outi s (Thm.trace_id r))

(* Write a theorem parent reference: " <trace_id>" *)
fun outth s th = (outs s " "; outi s (Thm.trace_id th))

(* Write a term intern reference: " <term_id>" *)
fun outtm s tm = (outs s " "; outi s (iT tm))

(* Write a type intern reference: " <type_id>" *)
fun outty s ty = (outs s " "; outi s (iY ty))

(* Record a line for C/O entries and other non-hot-path uses *)
fun record_line line =
  let val s = ensure_stream ()
  in outs s line; outs s "\n" end

(* ------- Trace hook ------- *)

fun record_hook (step : (thm, term, hol_type) Thm.trace_step) =
  let val s = ensure_stream () in
  case step of
    Thm.TR_ASSUME (r, tm) =>
      (outp s r; outs s " ASSUME"; outtm s tm; outs s "\n")
  | Thm.TR_REFL (r, tm) =>
      (outp s r; outs s " REFL"; outtm s tm; outs s "\n")
  | Thm.TR_BETA_CONV (r, tm) =>
      (outp s r; outs s " BETA_CONV"; outtm s tm; outs s "\n")
  | Thm.TR_ALPHA (r, t1, t2) =>
      (outp s r; outs s " ALPHA"; outtm s t1; outtm s t2; outs s "\n")
  | Thm.TR_ABS (r, th, v) =>
      (outp s r; outs s " ABS"; outth s th; outtm s v; outs s "\n")
  | Thm.TR_MK_COMB (r, f, x) =>
      (outp s r; outs s " MK_COMB"; outth s f; outth s x; outs s "\n")
  | Thm.TR_AP_TERM (r, th, f) =>
      (outp s r; outs s " AP_TERM"; outth s th; outtm s f; outs s "\n")
  | Thm.TR_AP_THM (r, th, tm) =>
      (outp s r; outs s " AP_THM"; outth s th; outtm s tm; outs s "\n")
  | Thm.TR_SYM (r, th) =>
      (outp s r; outs s " SYM"; outth s th; outs s "\n")
  | Thm.TR_TRANS (r, a, b) =>
      (outp s r; outs s " TRANS"; outth s a; outth s b; outs s "\n")
  | Thm.TR_EQ_MP (r, a, b) =>
      (outp s r; outs s " EQ_MP"; outth s a; outth s b; outs s "\n")
  | Thm.TR_EQ_IMP_RULE1 (r, th) =>
      (outp s r; outs s " EQ_IMP_RULE1"; outth s th; outs s "\n")
  | Thm.TR_EQ_IMP_RULE2 (r, th) =>
      (outp s r; outs s " EQ_IMP_RULE2"; outth s th; outs s "\n")
  | Thm.TR_MP (r, a, b) =>
      (outp s r; outs s " MP"; outth s a; outth s b; outs s "\n")
  | Thm.TR_DISCH (r, th, w) =>
      (outp s r; outs s " DISCH"; outth s th; outtm s w; outs s "\n")
  | Thm.TR_INST_TYPE (r, th, theta) =>
      (outp s r; outs s " INST_TYPE"; outth s th;
       List.app (fn {redex,residue} =>
         (outty s redex; outty s residue)) theta;
       outs s "\n")
  | Thm.TR_INST (r, th, theta) =>
      (outp s r; outs s " INST"; outth s th;
       List.app (fn {redex,residue} =>
         (outtm s redex; outtm s residue)) theta;
       outs s "\n")
  | Thm.TR_SUBST (r, repls, template, th) =>
      (outp s r; outs s " SUBST"; outth s th; outtm s template;
       List.app (fn {redex, residue} =>
         (outtm s redex; outth s residue)) repls;
       outs s "\n")
  | Thm.TR_SPEC (r, th, t) =>
      (outp s r; outs s " SPEC"; outth s th; outtm s t; outs s "\n")
  | Thm.TR_Specialize (r, th, t) =>
      (outp s r; outs s " Specialize"; outth s th; outtm s t; outs s "\n")
  | Thm.TR_Specialize_thm (r, th_arg, th) =>
      (outp s r; outs s " Specialize_thm"; outth s th_arg; outth s th;
       outs s "\n")
  | Thm.TR_GEN (r, th, x) =>
      (outp s r; outs s " GEN"; outth s th; outtm s x; outs s "\n")
  | Thm.TR_GENL (r, th, vs) =>
      (outp s r; outs s " GENL"; outth s th;
       List.app (fn v => outtm s v) vs;
       outs s "\n")
  | Thm.TR_GEN_ABS (r, th, opt, vs) =>
      (outp s r; outs s " GEN_ABS"; outth s th;
       outs s " ";
       (case opt of SOME t => outi s (iT t) | NONE => outs s "~");
       List.app (fn v => outtm s v) vs;
       outs s "\n")
  | Thm.TR_EXISTS (r, th, w, t) =>
      (outp s r; outs s " EXISTS"; outth s th; outtm s w; outtm s t;
       outs s "\n")
  | Thm.TR_CHOOSE (r, xth, bth, v) =>
      (outp s r; outs s " CHOOSE"; outth s xth; outth s bth; outtm s v;
       outs s "\n")
  | Thm.TR_CONJ (r, a, b) =>
      (outp s r; outs s " CONJ"; outth s a; outth s b; outs s "\n")
  | Thm.TR_CONJUNCT1 (r, th) =>
      (outp s r; outs s " CONJUNCT1"; outth s th; outs s "\n")
  | Thm.TR_CONJUNCT2 (r, th) =>
      (outp s r; outs s " CONJUNCT2"; outth s th; outs s "\n")
  | Thm.TR_DISJ1 (r, th, w) =>
      (outp s r; outs s " DISJ1"; outth s th; outtm s w; outs s "\n")
  | Thm.TR_DISJ2 (r, th, w) =>
      (outp s r; outs s " DISJ2"; outth s th; outtm s w; outs s "\n")
  | Thm.TR_DISJ_CASES (r, d, a, b) =>
      (outp s r; outs s " DISJ_CASES"; outth s d; outth s a; outth s b;
       outs s "\n")
  | Thm.TR_NOT_INTRO (r, th) =>
      (outp s r; outs s " NOT_INTRO"; outth s th; outs s "\n")
  | Thm.TR_NOT_ELIM (r, th) =>
      (outp s r; outs s " NOT_ELIM"; outth s th; outs s "\n")
  | Thm.TR_CCONTR (r, fth, w) =>
      (outp s r; outs s " CCONTR"; outth s fth; outtm s w; outs s "\n")
  | Thm.TR_Beta (r, th) =>
      (outp s r; outs s " Beta"; outth s th; outs s "\n")
  | Thm.TR_Mk_comb (r, orig, f, x) =>
      (outp s r; outs s " Mk_comb"; outth s orig; outth s f; outth s x;
       outs s "\n")
  | Thm.TR_Mk_abs (r, orig, body, _) =>
      (outp s r; outs s " Mk_abs"; outth s orig; outth s body; outs s "\n")
  | Thm.TR_REFL_RATOR (r, parent) =>
      (outp s r; outs s " REFL_RATOR"; outth s parent; outs s "\n")
  | Thm.TR_REFL_RAND (r, parent) =>
      (outp s r; outs s " REFL_RAND"; outth s parent; outs s "\n")
  | Thm.TR_REFL_BODY (r, parent) =>
      (outp s r; outs s " REFL_BODY"; outth s parent; outs s "\n")
  | Thm.TR_DEF_TYOP (r, wit, thy, tyop) =>
      (defined_types :=
         Redblackset.add(!defined_types, (thy, tyop));
       outp s r; outs s " DEF_TYOP"; outth s wit;
       outs s " "; outs s (esc thy);
       outs s " "; outs s (esc tyop); outs s "\n")
  | Thm.TR_DEF_SPEC (r, wit, thyname, cnames) =>
      (List.app (fn c =>
         defined_consts :=
           Redblackset.add(!defined_consts, (thyname, c))) cnames;
       outp s r; outs s " DEF_SPEC"; outth s wit;
       outs s " "; outs s (esc thyname);
       List.app (fn c => (outs s " "; outs s (esc c))) cnames;
       outs s "\n")
  | Thm.TR_COMPUTE (r, code_eqs, tm) =>
      (outp s r; outs s " COMPUTE"; outtm s tm;
       List.app (fn eq => outth s eq) code_eqs;
       outs s "\n")
  | Thm.TR_COMPUTE_INIT (cval_terms, cval_type, num_type, char_eqns) =>
      (outs s "I"; outty s cval_type; outty s num_type;
       List.app (fn (name, tm) =>
         (outs s " "; outs s (esc name); outtm s tm)) cval_terms;
       List.app (fn (name, th) =>
         (outs s " "; outs s (esc name); outth s th)) char_eqns;
       outs s "\n")
  | Thm.TR_ORACLE (r, tg) =>
      let val (hyps, c) = Thm.dest_thm r
      in outp s r; outs s " ORACLE ";
         outs s (esc tg); outtm s c;
         List.app (fn h => outtm s h) hyps;
         outs s "\n"
      end
  | Thm.TR_AXIOM (r, c) =>
      let val name = case Tag.axioms_of (Thm.tag r) of
                       [n] => Nonce.dest n
                     | _ => raise ERR "record_hook"
                              "AXIOM: expected exactly one axiom nonce"
      in outp s r; outs s " AXIOM ";
         outs s (esc name); outtm s c;
         outs s "\n"
      end
  | Thm.TR_NAME (r, src_thy, name) =>
      (outp s r; outs s " NAME ";
       outs s (esc src_thy); outs s " "; outs s (esc name); outs s "\n")
  | Thm.TR_LOAD (r, src_thy, src_trace_id) =>
      (outp s r; outs s " LOAD ";
       outs s (esc src_thy); outs s " "; outi s src_trace_id; outs s "\n")
  end

(* ------- Cleanup and reset ------- *)

fun cleanup () =
  (close_output () handle _ => ();
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
  (close_output ();
   output_path_ref := NONE;
   keep_on_exit := false;
   (!reset_for_new_session) ())

(* ------- Export hook (theory export) ------- *)

fun export_hook thyname (_:string list) all_thms =
  let
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
