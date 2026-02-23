(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step, streaming
   Y/T/P/C entries to a compressed output file as they happen.
   Sets Thm.trace_export_hook to append N/E entries at export time.

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

(* ------- Output stream (compressed or plain) ------- *)

datatype output =
    OUT_plain of TextIO.outstream
  | OUT_pipe of TextIO.outstream *
                (TextIO.instream, TextIO.outstream) Unix.proc

val output_ref : output option ref = ref NONE
val temp_path_ref : string option ref = ref NONE

fun detect_compressor () =
  let fun try cmd =
    (OS.Process.isSuccess
       (OS.Process.system (cmd ^ " --version > /dev/null 2>&1")))
    handle _ => false
  in if try "zstd" then SOME "zstd"
     else if try "gzip" then SOME "gzip"
     else NONE
  end

fun open_output () =
  let
    val pid = SysWord.toString
                (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
    val comp = detect_compressor ()
    val path = case comp of
        SOME "zstd" => ".trace_" ^ pid ^ ".pftrace.zst"
      | SOME "gzip" => ".trace_" ^ pid ^ ".pftrace.gz"
      | _ => ".trace_" ^ pid ^ ".pftrace"
    val _ = temp_path_ref := SOME path
    val out = case comp of
        SOME "zstd" =>
          let val p = Unix.execute("/bin/sh",
                ["-c", "zstd -q -o " ^ shell_quote path])
          in OUT_pipe (Unix.textOutstreamOf p, p) end
      | SOME "gzip" =>
          let val p = Unix.execute("/bin/sh",
                ["-c", "gzip > " ^ shell_quote path])
          in OUT_pipe (Unix.textOutstreamOf p, p) end
      | _ => OUT_plain (TextIO.openOut path)
    val s = case out of OUT_plain s => s | OUT_pipe (s,_) => s
  in
    output_ref := SOME out;
    TextIO.output(s, "V 1\n");
    out
  end

fun get_out () = case !output_ref of
    SOME out => out | NONE => open_output ()

fun out_strm () = case get_out () of
    OUT_plain s => s | OUT_pipe (s,_) => s

fun close_output () =
  case !output_ref of
    NONE => ()
  | SOME (OUT_plain s) =>
      ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ();
       output_ref := NONE)
  | SOME (OUT_pipe (s, p)) =>
      ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ();
       (ignore (Unix.reap p)) handle _ => ();
       output_ref := NONE)

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

(* ------- Theorem ID tracking ------- *)

val thm_counter = ref 0
val id_to_line : (int, int) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Int.compare)

(* DISK_THM info: trace_id → (theory, name) for on-demand emission *)
val disk_thm_info : (int, string * string) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Int.compare)

(* Look up (theory, name) for a heap thm from DB *)
fun thm_thyname thm =
  let
    val dep = Tag.dep_of (Thm.tag thm)
    val (thy, n) = case dep of
        Dep.DEP_SAVED (did, _) => did
      | _ => ("_unknown", ~1)
    val name =
      case List.find (fn (_, th) =>
        let val d = Tag.dep_of (Thm.tag th)
        in case d of Dep.DEP_SAVED (did, _) => did = (thy, n)
                   | _ => false
        end) (DB.thms thy) of
        SOME (nm, _) => nm
      | NONE => "_unknown_" ^ Int.toString n
  in (thy, name) end
  handle _ => ("_unknown", "_unknown")

(* Resolve parent thm to line number; emit DISK_THM on demand *)
fun parent_line thm =
  let val tid = Thm.trace_id thm
  in case Redblackmap.peek(!id_to_line, tid) of
       SOME ln => ln
     | NONE =>
       let val (thy, name) =
             case Redblackmap.peek(!disk_thm_info, tid) of
               SOME info => info
             | NONE => thm_thyname thm
           val ln = !thm_counter
           val _ = thm_counter := ln + 1
           val s = out_strm ()
       in TextIO.output(s, "P " ^ its ln ^ " DISK_THM " ^
            esc thy ^ " " ^ esc name ^ "\n");
          id_to_line :=
            Redblackmap.insert(!id_to_line, tid, ln);
          ln
       end
  end

val pl = its o parent_line

(* Record a theorem: write P line, register ID *)
fun record_thm result line =
  let val ln = !thm_counter
      val _ = thm_counter := ln + 1
      val s = out_strm ()
  in TextIO.output(s, "P " ^ its ln ^ " " ^ line ^ "\n");
     id_to_line :=
       Redblackmap.insert(!id_to_line, Thm.trace_id result, ln)
  end

(* ------- Trace hook ------- *)

fun record_hook (step : (thm, term, hol_type) Thm.trace_step) =
  case step of
    Thm.TR_ASSUME (r, tm) =>
      record_thm r ("ASSUME " ^ its (iT tm))
  | Thm.TR_REFL (r, tm) =>
      record_thm r ("REFL " ^ its (iT tm))
  | Thm.TR_BETA_CONV (r, tm) =>
      record_thm r ("BETA_CONV " ^ its (iT tm))
  | Thm.TR_ALPHA (r, t1, t2) =>
      record_thm r ("ALPHA " ^ its (iT t1) ^ " " ^ its (iT t2))
  | Thm.TR_ABS (r, th, v) =>
      record_thm r ("ABS " ^ pl th ^ " " ^ its (iT v))
  | Thm.TR_MK_COMB (r, f, x) =>
      record_thm r ("MK_COMB " ^ pl f ^ " " ^ pl x)
  | Thm.TR_AP_TERM (r, th, f) =>
      record_thm r ("AP_TERM " ^ pl th ^ " " ^ its (iT f))
  | Thm.TR_AP_THM (r, th, tm) =>
      record_thm r ("AP_THM " ^ pl th ^ " " ^ its (iT tm))
  | Thm.TR_SYM (r, th) =>
      record_thm r ("SYM " ^ pl th)
  | Thm.TR_TRANS (r, a, b) =>
      record_thm r ("TRANS " ^ pl a ^ " " ^ pl b)
  | Thm.TR_EQ_MP (r, a, b) =>
      record_thm r ("EQ_MP " ^ pl a ^ " " ^ pl b)
  | Thm.TR_EQ_IMP_RULE1 (r, th) =>
      record_thm r ("EQ_IMP_RULE1 " ^ pl th)
  | Thm.TR_EQ_IMP_RULE2 (r, th) =>
      record_thm r ("EQ_IMP_RULE2 " ^ pl th)
  | Thm.TR_MP (r, a, b) =>
      record_thm r ("MP " ^ pl a ^ " " ^ pl b)
  | Thm.TR_DISCH (r, th, w) =>
      record_thm r ("DISCH " ^ pl th ^ " " ^ its (iT w))
  | Thm.TR_INST_TYPE (r, th, theta) =>
      record_thm r ("INST_TYPE " ^ pl th ^
        String.concat (map (fn {redex,residue} =>
          " " ^ its (iY redex) ^ " " ^ its (iY residue)) theta))
  | Thm.TR_INST (r, th, theta) =>
      record_thm r ("INST " ^ pl th ^
        String.concat (map (fn {redex,residue} =>
          " " ^ its (iT redex) ^ " " ^ its (iT residue)) theta))
  | Thm.TR_SUBST (r, repls, template, th) =>
      record_thm r ("SUBST " ^ pl th ^ " " ^ its (iT template) ^
        String.concat (map (fn {redex, residue} =>
          " " ^ its (iT redex) ^ " " ^ pl residue) repls))
  | Thm.TR_SPEC (r, th, t) =>
      record_thm r ("SPEC " ^ pl th ^ " " ^ its (iT t))
  | Thm.TR_Specialize (r, th, t) =>
      record_thm r ("Specialize " ^ pl th ^ " " ^ its (iT t))
  | Thm.TR_GEN (r, th, x) =>
      record_thm r ("GEN " ^ pl th ^ " " ^ its (iT x))
  | Thm.TR_GENL (r, th, vs) =>
      record_thm r ("GENL " ^ pl th ^
        String.concat (map (fn v => " " ^ its (iT v)) vs))
  | Thm.TR_GEN_ABS (r, th, opt, vs) =>
      record_thm r ("GEN_ABS " ^ pl th ^ " " ^
        (case opt of SOME t => its (iT t) | NONE => "~") ^
        String.concat (map (fn v => " " ^ its (iT v)) vs))
  | Thm.TR_EXISTS (r, th, w, t) =>
      record_thm r ("EXISTS " ^ pl th ^ " " ^
        its (iT w) ^ " " ^ its (iT t))
  | Thm.TR_CHOOSE (r, xth, bth, v) =>
      record_thm r ("CHOOSE " ^ pl xth ^ " " ^
        pl bth ^ " " ^ its (iT v))
  | Thm.TR_CONJ (r, a, b) =>
      record_thm r ("CONJ " ^ pl a ^ " " ^ pl b)
  | Thm.TR_CONJUNCT1 (r, th) =>
      record_thm r ("CONJUNCT1 " ^ pl th)
  | Thm.TR_CONJUNCT2 (r, th) =>
      record_thm r ("CONJUNCT2 " ^ pl th)
  | Thm.TR_DISJ1 (r, th, w) =>
      record_thm r ("DISJ1 " ^ pl th ^ " " ^ its (iT w))
  | Thm.TR_DISJ2 (r, th, w) =>
      record_thm r ("DISJ2 " ^ pl th ^ " " ^ its (iT w))
  | Thm.TR_DISJ_CASES (r, d, a, b) =>
      record_thm r ("DISJ_CASES " ^ pl d ^ " " ^
        pl a ^ " " ^ pl b)
  | Thm.TR_NOT_INTRO (r, th) =>
      record_thm r ("NOT_INTRO " ^ pl th)
  | Thm.TR_NOT_ELIM (r, th) =>
      record_thm r ("NOT_ELIM " ^ pl th)
  | Thm.TR_CCONTR (r, fth, w) =>
      record_thm r ("CCONTR " ^ pl fth ^ " " ^ its (iT w))
  | Thm.TR_Beta (r, th) =>
      record_thm r ("Beta " ^ pl th)
  | Thm.TR_Mk_comb (r, orig, f, x) =>
      record_thm r ("Mk_comb " ^ pl orig ^ " " ^
        pl f ^ " " ^ pl x)
  | Thm.TR_Mk_abs (r, orig, body, _) =>
      record_thm r ("Mk_abs " ^ pl orig ^ " " ^ pl body)
  | Thm.TR_DEF_TYOP (r, wit, thy, tyop) =>
      record_thm r ("DEF_TYOP " ^ pl wit ^ " " ^
        esc thy ^ " " ^ esc tyop)
  | Thm.TR_DEF_SPEC (r, wit, thyname, cnames) =>
      record_thm r ("DEF_SPEC " ^ pl wit ^ " " ^ esc thyname ^
        String.concat (map (fn c => " " ^ esc c) cnames))
  | Thm.TR_COMPUTE (r, code_eqs, tm) =>
      record_thm r ("COMPUTE " ^ its (iT tm) ^
        String.concat (map (fn eq => " " ^ pl eq) code_eqs))
  | Thm.TR_COMPUTE_INIT (cval_terms, cval_type, num_type, char_eqns) =>
      let val s = out_strm ()
      in TextIO.output(s, "C " ^ its (iY cval_type) ^ " " ^
           its (iY num_type) ^
           String.concat (map (fn (name, tm) =>
             " " ^ esc name ^ " " ^ its (iT tm)) cval_terms) ^
           String.concat (map (fn (name, th) =>
             " " ^ esc name ^ " " ^ pl th) char_eqns) ^
           "\n")
      end
  | Thm.TR_ORACLE (r, tg) =>
      let val (hs, c) = Thm.dest_thm r
      in record_thm r ("ORACLE " ^ esc tg ^ " " ^ its (iT c) ^
           String.concat (map (fn h => " " ^ its (iT h)) hs))
      end
  | Thm.TR_AXIOM (r, c) =>
      record_thm r ("AXIOM " ^ its (iT c))
  | Thm.TR_DISK_THM (r, src_thy, name) =>
      disk_thm_info := Redblackmap.insert(!disk_thm_info,
        Thm.trace_id r, (src_thy, name))

(* ------- Cleanup and reset ------- *)

fun cleanup () =
  (close_output () handle _ => ();
   case !temp_path_ref of
     SOME p => (OS.FileSys.remove p handle _ => ())
   | NONE => ())

fun trace_reset () =
  (close_output ();
   temp_path_ref := NONE;
   ty_map := Redblackmap.mkDict Type.compare;
   tm_map := Redblackmap.mkDict Term.compare;
   ty_counter := 0;
   tm_counter := 0;
   thm_counter := 0;
   id_to_line := Redblackmap.mkDict Int.compare;
   disk_thm_info := Redblackmap.mkDict Int.compare)

(* ------- Export hook ------- *)

fun export_hook thyname (_:string list) all_thms =
  let val s = out_strm ()
  in
    TextIO.output(s, "N " ^ esc thyname ^ "\n");
    List.app (fn (name, th) =>
      let val ln =
            case Redblackmap.peek(!id_to_line, Thm.trace_id th) of
              SOME l => l
            | NONE => parent_line th
      in TextIO.output(s, "E " ^ esc name ^ " " ^ its ln ^ "\n")
      end) all_thms;
    close_output ();
    (let val temp = valOf (!temp_path_ref)
         val ext = if String.isSuffix ".zst" temp then ".pftrace.zst"
                   else if String.isSuffix ".gz" temp then ".pftrace.gz"
                   else ".pftrace"
         val final_path = thyname ^ "Theory" ^ ext
     in OS.FileSys.rename {old = temp, new = final_path} end
     handle _ => ());
    Feedback.HOL_MESG ("Proof trace: " ^ thyname ^ "Theory.pftrace*");
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

val _ = Thm.trace_hook := SOME record_hook
val _ = Thm.trace_export_hook := SOME export_hook
val _ = OS.Process.atExit cleanup

end
