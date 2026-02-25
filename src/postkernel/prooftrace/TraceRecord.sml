(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step, streaming
   Y/T/P/C entries to the output file. P entries use kernel
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

fun find_heap_input () =
  let val args = CommandLine.arguments ()
  in case find_arg "--holstate" args of
       SOME p => SOME p
     | NONE => find_arg "-b" args
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
    val pft = path ^ ".pft"
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

   Called at the entry to record_hook and the NC/NY TheoryDelta hook —
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
        in output_strm := NONE; output_path_ref := NONE;
           (!reset_for_new_session) ();
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

(* ------- Type interning (writes Y entries inline) ------- *)

val ty_map = ref (Redblackmap.mkDict Type.compare)
val ty_counter = ref 0

fun intern_type ty =
  case Redblackmap.peek(!ty_map, ty) of
    SOME id => id
  | NONE =>
    let
      val _ = if not (Type.is_vartype ty) then
                let val {Args,...} = Type.dest_thy_type ty
                in List.app (ignore o intern_type) Args end
              else ()
      val id = !ty_counter
      val _ = ty_counter := id + 1
      val _ = ty_map := Redblackmap.insert(!ty_map, ty, id)
      val s = out_strm ()
      fun yid t = valOf (Redblackmap.peek(!ty_map, t))
    in
      (if Type.is_vartype ty then
         TextIO.output(s, "Y " ^ its id ^ " V " ^
           esc (Type.dest_vartype ty) ^ "\n")
       else
         let val {Thy, Tyop, Args} = Type.dest_thy_type ty
         in TextIO.output(s, "Y " ^ its id ^ " O " ^
              esc Thy ^ " " ^ esc Tyop ^
              (if null Args then ""
               else " " ^ String.concatWith " "
                             (map (its o yid) Args)) ^ "\n")
         end);
      id
    end

val iY = intern_type

(* ------- Term interning (writes T entries inline) ------- *)

val tm_map = ref (Redblackmap.mkDict Term.compare)
val tm_counter = ref 0

fun intern_term tm =
  case Redblackmap.peek(!tm_map, tm) of
    SOME id => id
  | NONE =>
    let
      val _ = case Term.dest_term tm of
          Term.VAR _ => ignore (intern_type (Term.type_of tm))
        | Term.CONST _ => ignore (intern_type (Term.type_of tm))
        | Term.COMB (f, x) =>
            (ignore (intern_term f); ignore (intern_term x))
        | Term.LAMB (v, b) =>
            (ignore (intern_term v); ignore (intern_term b))
      val id = !tm_counter
      val _ = tm_counter := id + 1
      val _ = tm_map := Redblackmap.insert(!tm_map, tm, id)
      val s = out_strm ()
      fun yid t = valOf (Redblackmap.peek(!ty_map, t))
      fun tid t = valOf (Redblackmap.peek(!tm_map, t))
    in
      (case Term.dest_term tm of
         Term.VAR (name, ty) =>
           TextIO.output(s, "T " ^ its id ^ " V " ^
             esc name ^ " " ^ its (yid ty) ^ "\n")
       | Term.CONST {Thy, Name, Ty} =>
           TextIO.output(s, "T " ^ its id ^ " C " ^
             esc Thy ^ " " ^ esc Name ^ " " ^
             its (yid Ty) ^ "\n")
       | Term.COMB (f, x) =>
           TextIO.output(s, "T " ^ its id ^ " A " ^
             its (tid f) ^ " " ^ its (tid x) ^ "\n")
       | Term.LAMB (v, b) =>
           TextIO.output(s, "T " ^ its id ^ " L " ^
             its (tid v) ^ " " ^ its (tid b) ^ "\n"));
      id
    end

val iT = intern_term

(* ------- DEF_SPEC/DEF_TYOP tracking for NC/NY filtering ------- *)

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
  ty_map := Redblackmap.mkDict Type.compare;
  tm_map := Redblackmap.mkDict Term.compare;
  ty_counter := 0;
  tm_counter := 0;
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
      record_line ("C " ^ its (iY cval_type) ^ " " ^
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
  | Thm.TR_DISK_THM (r, src_thy, name) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISK_THM " ^
        esc src_thy ^ " " ^ esc name)
  | Thm.TR_DISK_DEP (r, src_thy, depid) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISK_DEP " ^
        esc src_thy ^ " " ^ its depid))

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

fun export_hook thyname (_:string list) all_thms dep_thms =
  let
    val () = close_output ()
    val temp = case !output_path_ref of
                 SOME p => p
               | NONE => ""
  in
    if temp = "" then () else
    let
      val final_name = thyname ^ "Theory.pft"

      (* Write N, E, and D lines to the temp file *)
      val s = TextIO.openAppend temp
      val _ = TextIO.output(s, "N " ^ esc thyname ^ "\n")
      val _ = List.app (fn (name, th) =>
        TextIO.output(s, "E " ^ esc name ^ " " ^
          its (Thm.trace_id th) ^ "\n")) all_thms
      (* D lines for anonymous thydata theorems *)
      val _ = List.app (fn (depid, th) =>
        TextIO.output(s, "D " ^ its depid ^ " " ^
          its (Thm.trace_id th) ^ "\n")) dep_thms
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
  (* Clear save_dep_log before .dat file write so that only
     anonymous thydata theorems accumulate during export *)
  Theory.register_hook (
    "TraceRecord.clear_dep_log",
    fn TheoryDelta.ExportTheory _ => Thm.save_dep_log := []
     | _ => ()
  );
  (* Emit NC/NY for constants/types not already defined by
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
            in record_line ("NC " ^ esc Thy ^ " " ^ esc Name ^
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
                   record_line ("NY " ^ esc Thy ^ " " ^ esc Name ^
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
