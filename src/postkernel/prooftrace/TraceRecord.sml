(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step, streaming
   Y/T/P/C entries to an uncompressed temp file. P entries use
   kernel trace_ids for both their own ID and parent references.

   At export time (theory or heap), the temp file is compressed
   and renamed to the final .pft path. No remapping is needed.

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

fun shell_quote s =
  "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"

(* ------- Output stream (uncompressed temp file) ------- *)

val output_strm : TextIO.outstream option ref = ref NONE
val temp_path_ref : string option ref = ref NONE
val is_temp_file : bool ref = ref true  (* false for heap builds *)

(* Reset function ref — set after intern tables are defined *)
val reset_for_new_session = ref (fn () => ())

(* Parse command line for heap-related paths *)
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

val heap_input_path : string option ref = ref NONE

fun open_temp_file () =
  let
    val pid = SysWord.toString
                (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
    val path = ".trace_" ^ pid ^ ".tmp"
    val _ = temp_path_ref := SOME path
    val s = TextIO.openOut path
  in
    output_strm := SOME s;
    TextIO.output(s, "V 1\n");
    s
  end

fun out_strm () =
  case !output_strm of
    NONE => open_temp_file ()
  | SOME s =>
      (TextIO.output(s, ""); s)
      handle _ =>
        (* Stale stream from heap restore — reopen *)
        (output_strm := NONE; temp_path_ref := NONE;
         is_temp_file := true;
         heap_input_path := find_heap_input ();
         (!reset_for_new_session) ();
         case find_heap_output () of
           SOME path =>
             let val pft = path ^ ".pft"
                 val s = TextIO.openOut pft
             in output_strm := SOME s;
                temp_path_ref := SOME pft;
                is_temp_file := false;
                TextIO.output(s, "V 1\n");
                s
             end
         | NONE => open_temp_file ())

fun close_temp () =
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

val _ = reset_for_new_session := (fn () => (
  ty_map := Redblackmap.mkDict Type.compare;
  tm_map := Redblackmap.mkDict Term.compare;
  ty_counter := 0;
  tm_counter := 0
))

(* ------- Parent reference: kernel trace_id ------- *)

fun pi thm = its (Thm.trace_id thm)

(* ------- Record a line ------- *)

fun record_line line =
  let val s = out_strm ()
  in TextIO.output(s, line ^ "\n") end

(* ------- Trace hook ------- *)

fun record_hook (step : (thm, term, hol_type) Thm.trace_step) =
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
      let val remapped_pairs =
            let fun go [] = ""
                  | go ({redex, residue} :: rest) =
                      " " ^ its (iT redex) ^ " " ^ pi residue ^ go rest
            in go repls end
      in record_line ("P " ^ its (Thm.trace_id r) ^ " SUBST " ^ pi th ^
           " " ^ its (iT template) ^ remapped_pairs)
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
      record_line ("P " ^ its (Thm.trace_id r) ^ " DEF_TYOP " ^
        pi wit ^ " " ^ esc thy ^ " " ^ esc tyop)
  | Thm.TR_DEF_SPEC (r, wit, thyname, cnames) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DEF_SPEC " ^ pi wit ^
        " " ^ esc thyname ^
        String.concat (map (fn c => " " ^ esc c) cnames))
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
      record_line ("P " ^ its (Thm.trace_id r) ^ " AXIOM " ^ its (iT c))
  | Thm.TR_DISK_THM (r, src_thy, name) =>
      record_line ("P " ^ its (Thm.trace_id r) ^ " DISK_THM " ^
        esc src_thy ^ " " ^ esc name)

(* ------- Cleanup and reset ------- *)

fun cleanup () =
  (close_temp () handle _ => ();
   if !is_temp_file then
     case !temp_path_ref of
       SOME p => (OS.FileSys.remove p handle _ => ())
     | NONE => ()
   else ())

fun trace_reset () =
  (close_temp ();
   temp_path_ref := NONE;
   (!reset_for_new_session) ())

(* ------- Export hook ------- *)

fun detect_compressor () =
  let fun try cmd =
    (OS.Process.isSuccess
       (OS.Process.system (cmd ^ " --version > /dev/null 2>&1")))
    handle _ => false
  in if try "zstd" then SOME "zstd"
     else if try "gzip" then SOME "gzip"
     else NONE
  end

fun export_hook thyname (_:string list) all_thms =
  let
    val () = close_temp ()
    val temp = case !temp_path_ref of
                 SOME p => p
               | NONE => ""
  in
    if temp = "" then () else
    let
      (* Determine output path and compress *)
      val comp = detect_compressor ()
      val ext = case comp of
          SOME "zstd" => ".pft.zst"
        | SOME "gzip" => ".pft.gz"
        | _ => ".pft"
      val final_name =
        if String.isPrefix "_heap_" thyname then
          String.extract(thyname, 6, NONE) ^ ext
        else
          thyname ^ "Theory" ^ ext

      (* Append N and E lines to the temp file *)
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

      (* Compress and rename *)
      val _ = case comp of
          SOME "zstd" =>
            (OS.Process.system
               ("zstd -q --rm " ^ shell_quote temp ^
                " -o " ^ shell_quote actual_path);
             ())
        | SOME "gzip" =>
            (OS.Process.system
               ("gzip -c " ^ shell_quote temp ^
                " > " ^ shell_quote actual_path ^
                " && rm " ^ shell_quote temp);
             ())
        | _ =>
            (OS.FileSys.rename {old = temp, new = actual_path}; ())

      val _ = Feedback.HOL_MESG ("Proof trace: " ^ final_name)
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
  OS.Process.atExit cleanup
)

val _ = case OS.Process.getEnv "HOL_TRACE_PROOFS" of
          SOME _ =>
          let val _ = activate ()
              val heap_out = find_heap_output ()
              val _ = TextIO.output(TextIO.stdErr,
                "[TraceRecord] heap_output = " ^
                (case heap_out of SOME p => p | NONE => "NONE") ^ "\n")
          in case heap_out of
               SOME path =>
                 let val pft = path ^ ".pft"
                     val s = TextIO.openOut pft
                 in output_strm := SOME s;
                    temp_path_ref := SOME pft;
                    is_temp_file := false;
                    TextIO.output(s, "V 1\n")
                 end
             | NONE => ()
          end
        | NONE => ()

end
