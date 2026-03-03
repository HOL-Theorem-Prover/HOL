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
   Set by check_stale when recovering from a stale stream. *)
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

(* Detect and recover from stale stream after heap restore.
   Must be called BEFORE any intern_type/intern_term calls to avoid
   corrupting intern state mid-recursion. Also re-registers atExit
   since the handler from the original process doesn't survive
   heap save/restore.

   Called at the entry to record_hook and the C/O TheoryDelta hook —
   the only two code paths that lead to intern + write sequences. *)
val cleanup_ref : (unit -> unit) ref = ref (fn () => ())

fun check_stale () =
  case !output_strm of
    NONE => ()
  | SOME s =>
      (TextIO.output(s, ""); ())
      handle _ =>
        let val stale = !output_path_ref
            fun is_tmp p = String.isSuffix ".tmp" p
            fun strip_pft p =
              if String.isSuffix ".pft" p then
                SOME (String.substring(p, 0, size p - 4))
              else NONE
        in output_strm := NONE; output_path_ref := NONE;
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
   output_strm := NONE)

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

(* ------- Parent reference: kernel trace_id ------- *)

fun pi thm = its (Thm.trace_id thm)

(* ------- Record a line ------- *)

fun record_line line =
  let val s = out_strm ()
  in TextIO.output(s, line ^ "\n") end

(* ------- Trace hook ------- *)

fun record_hook (step : (thm, term, hol_type) Thm.trace_step) =
  (check_stale ();
  case step of
    Thm.TR_ASSUME (r, tm) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " ASSUME " ^ its (iT tm))
  | Thm.TR_REFL (r, tm) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " REFL " ^ its (iT tm))
  | Thm.TR_BETA_CONV (r, tm) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " BETA_CONV " ^ its (iT tm))
  | Thm.TR_ALPHA (r, t1, t2) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " ALPHA " ^
        its (iT t1) ^ " " ^ its (iT t2))
  | Thm.TR_ABS (r, th, v) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " ABS " ^
        pi th ^ " " ^ its (iT v))
  | Thm.TR_MK_COMB (r, f, x) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " MK_COMB " ^
        pi f ^ " " ^ pi x)
  | Thm.TR_AP_TERM (r, th, f) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " AP_TERM " ^
        pi th ^ " " ^ its (iT f))
  | Thm.TR_AP_THM (r, th, tm) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " AP_THM " ^
        pi th ^ " " ^ its (iT tm))
  | Thm.TR_SYM (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " SYM " ^ pi th)
  | Thm.TR_TRANS (r, a, b) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " TRANS " ^
        pi a ^ " " ^ pi b)
  | Thm.TR_EQ_MP (r, a, b) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " EQ_MP " ^
        pi a ^ " " ^ pi b)
  | Thm.TR_EQ_IMP_RULE1 (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " EQ_IMP_RULE1 " ^ pi th)
  | Thm.TR_EQ_IMP_RULE2 (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " EQ_IMP_RULE2 " ^ pi th)
  | Thm.TR_MP (r, a, b) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " MP " ^
        pi a ^ " " ^ pi b)
  | Thm.TR_DISCH (r, th, w) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISCH " ^
        pi th ^ " " ^ its (iT w))
  | Thm.TR_INST_TYPE (r, th, theta) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " INST_TYPE " ^ pi th ^
        String.concat (map (fn {redex,residue} =>
          " " ^ its (iY redex) ^ " " ^ its (iY residue)) theta))
  | Thm.TR_INST (r, th, theta) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " INST " ^ pi th ^
        String.concat (map (fn {redex,residue} =>
          " " ^ its (iT redex) ^ " " ^ its (iT residue)) theta))
  | Thm.TR_SUBST (r, repls, template, th) =>
      let val pairs =
            let fun go [] = ""
                  | go ({redex, residue} :: rest) =
                      " " ^ its (iT redex) ^ " " ^ pi residue ^ go rest
            in go repls end
      in record_line ("P " ^ its (Thm.trace_id r) ^ " SUBST " ^ pi th ^
           " " ^ its (iT template) ^ pairs)
      end
  | Thm.TR_SPEC (r, th, t) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " SPEC " ^
        pi th ^ " " ^ its (iT t))
  | Thm.TR_Specialize (r, th, t) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " Specialize " ^
        pi th ^ " " ^ its (iT t))
  | Thm.TR_Specialize_thm (r, th_arg, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " Specialize_thm " ^
        pi th_arg ^ " " ^ pi th)
  | Thm.TR_GEN (r, th, x) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " GEN " ^
        pi th ^ " " ^ its (iT x))
  | Thm.TR_GENL (r, th, vs) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " GENL " ^ pi th ^
        String.concat (map (fn v => " " ^ its (iT v)) vs))
  | Thm.TR_GEN_ABS (r, th, opt, vs) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " GEN_ABS " ^ pi th ^ " " ^
        (case opt of SOME t => its (iT t) | NONE => "~") ^
        String.concat (map (fn v => " " ^ its (iT v)) vs))
  | Thm.TR_EXISTS (r, th, w, t) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " EXISTS " ^
        pi th ^ " " ^ its (iT w) ^ " " ^ its (iT t))
  | Thm.TR_CHOOSE (r, xth, bth, v) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " CHOOSE " ^
        pi xth ^ " " ^ pi bth ^ " " ^ its (iT v))
  | Thm.TR_CONJ (r, a, b) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " CONJ " ^
        pi a ^ " " ^ pi b)
  | Thm.TR_CONJUNCT1 (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " CONJUNCT1 " ^ pi th)
  | Thm.TR_CONJUNCT2 (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " CONJUNCT2 " ^ pi th)
  | Thm.TR_DISJ1 (r, th, w) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISJ1 " ^
        pi th ^ " " ^ its (iT w))
  | Thm.TR_DISJ2 (r, th, w) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISJ2 " ^
        pi th ^ " " ^ its (iT w))
  | Thm.TR_DISJ_CASES (r, d, a, b) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISJ_CASES " ^
        pi d ^ " " ^ pi a ^ " " ^ pi b)
  | Thm.TR_NOT_INTRO (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " NOT_INTRO " ^ pi th)
  | Thm.TR_NOT_ELIM (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " NOT_ELIM " ^ pi th)
  | Thm.TR_CCONTR (r, fth, w) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " CCONTR " ^
        pi fth ^ " " ^ its (iT w))
  | Thm.TR_Beta (r, th) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " Beta " ^ pi th)
  | Thm.TR_Mk_comb (r, orig, f, x) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " Mk_comb " ^
        pi orig ^ " " ^ pi f ^ " " ^ pi x)
  | Thm.TR_Mk_abs (r, orig, body, _) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " Mk_abs " ^
        pi orig ^ " " ^ pi body)
  | Thm.TR_REFL_RATOR (r, parent) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " REFL_RATOR " ^ pi parent)
  | Thm.TR_REFL_RAND (r, parent) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " REFL_RAND " ^ pi parent)
  | Thm.TR_REFL_BODY (r, parent) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " REFL_BODY " ^ pi parent)
  | Thm.TR_DEF_TYOP (r, wit, thy, tyop) =>
      (defined_types :=
         Redblackset.add(!defined_types, (thy, tyop));
       record_line ("P " ^ its (Thm.trace_id r) ^ " DEF_TYOP " ^
         pi wit ^ " " ^ esc thy ^ " " ^ esc tyop))
  | Thm.TR_DEF_SPEC (r, wit, thyname, cnames) =>
      (List.app (fn c =>
         defined_consts :=
           Redblackset.add(!defined_consts, (thyname, c))) cnames;
       record_line ("P " ^ its (Thm.trace_id r) ^ " DEF_SPEC " ^ pi wit ^
         " " ^ esc thyname ^
         String.concat (map (fn c => " " ^ esc c) cnames)))
  | Thm.TR_COMPUTE (r, code_eqs, tm) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " COMPUTE " ^
        its (iT tm) ^
        String.concat (map (fn eq => " " ^ pi eq) code_eqs))
  | Thm.TR_COMPUTE_INIT (cval_terms, cval_type, num_type, char_eqns) =>
      record_line ("I " ^ its (iY cval_type) ^ " " ^
        its (iY num_type) ^
        String.concat (map (fn (name, tm) =>
          " " ^ esc name ^ " " ^ its (iT tm)) cval_terms) ^
        String.concat (map (fn (name, th) =>
          " " ^ esc name ^ " " ^ pi th) char_eqns))
  | Thm.TR_ORACLE (r, tg) =>
      let val (hs, c) = Thm.dest_thm r
      in record_line ("P " ^ its (Thm.trace_id r) ^ " ORACLE " ^
           esc tg ^ " " ^ its (iT c) ^
           String.concat (map (fn h => " " ^ its (iT h)) hs))
      end
  | Thm.TR_AXIOM (r, c) =>
      let val name = case Tag.axioms_of (Thm.tag r) of
                       [n] => Nonce.dest n
                     | _ => raise ERR "record_hook"
                              "AXIOM: expected exactly one axiom nonce"
      in record_line ("P " ^ its (Thm.trace_id r) ^ " AXIOM " ^
           esc name ^ " " ^ its (iT c))
      end
  | Thm.TR_NAME (r, src_thy, name) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " NAME " ^
        esc src_thy ^ " " ^ esc name)
  | Thm.TR_LOAD (r, src_thy, src_trace_id) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " LOAD " ^
        esc src_thy ^ " " ^ its src_trace_id))

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
         (check_stale ();
          if Redblackset.member(!defined_consts, (Thy, Name))
          then ()
          else
            let val ty = Term.type_of
                           (Term.prim_mk_const {Thy=Thy, Name=Name})
                val tyid = iY ty
            in record_line ("C " ^ esc Thy ^ " " ^ esc Name ^
                            " " ^ its tyid)
            end)
     | TheoryDelta.NewTypeOp {Thy, Name} =>
         (check_stale ();
          if Redblackset.member(!defined_types, (Thy, Name))
          then ()
          else
            let val arity = Type.op_arity {Thy=Thy, Tyop=Name}
            in case arity of
                 SOME a =>
                   record_line ("O " ^ esc Thy ^ " " ^ esc Name ^
                                " " ^ its a)
               | NONE => ()
            end)
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
