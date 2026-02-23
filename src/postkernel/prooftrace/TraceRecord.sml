(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step to a per-PID temp file.
   Sets Thm.trace_export_hook to export .pftrace files at theory export.

   Activated unconditionally on load. Loading is controlled by the build
   system (only when tracing is requested).

   NOT in the trust boundary: output is verified by ReplayTrace.sml
   replaying through the kernel.
*)

structure TraceRecord :> TraceRecord =
struct

open HolKernel

val ERR = mk_HOL_ERR "TraceRecord"
val its = Int.toString

(* -----------------------------------------------------------------------
   Intern tables: types and terms get sequential IDs
   ----------------------------------------------------------------------- *)

val ty_map = ref (Redblackmap.mkDict Type.compare)
val tm_map = ref (Redblackmap.mkDict Term.compare)
val ty_counter = ref 0
val tm_counter = ref 0
val ty_list : hol_type list ref = ref []  (* reverse order *)
val tm_list : term list ref = ref []      (* reverse order *)

fun intern_type ty =
  case Redblackmap.peek (!ty_map, ty) of
    SOME id => id
  | NONE =>
    let val _ = if not (Type.is_vartype ty) then
                  let val {Args,...} = Type.dest_thy_type ty
                  in List.app (ignore o intern_type) Args end
                else ()
        val id = !ty_counter
    in ty_counter := id + 1;
       ty_map := Redblackmap.insert (!ty_map, ty, id);
       ty_list := ty :: !ty_list;
       id
    end

fun intern_term tm =
  case Redblackmap.peek (!tm_map, tm) of
    SOME id => id
  | NONE =>
    let val _ = case Term.dest_term tm of
            Term.VAR _ => ignore (intern_type (Term.type_of tm))
          | Term.CONST _ => ignore (intern_type (Term.type_of tm))
          | Term.COMB (f, x) =>
              (ignore (intern_term f); ignore (intern_term x))
          | Term.LAMB (v, b) =>
              (ignore (intern_term v); ignore (intern_term b))
        val id = !tm_counter
    in tm_counter := id + 1;
       tm_map := Redblackmap.insert (!tm_map, tm, id);
       tm_list := tm :: !tm_list;
       id
    end

val iT = intern_term
val iY = intern_type

(* -----------------------------------------------------------------------
   Per-PID temp file and trace_id → line_number mapping
   ----------------------------------------------------------------------- *)

val steps_strm : TextIO.outstream option ref = ref NONE
val lines_written : int ref = ref 0
val steps_path_ref : string option ref = ref NONE

(* Map from thm trace_id to line number in the temp file *)
val id_to_line : (int, int) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Int.compare)

fun steps_path () =
  case !steps_path_ref of
    SOME s => s
  | NONE =>
    let val pid = SysWord.toString (Posix.Process.pidToWord
                    (Posix.ProcEnv.getpid ()))
        val s = ".trace_" ^ pid ^ "_steps.log"
    in steps_path_ref := SOME s; s end

fun get_steps () = case !steps_strm of
    SOME s => s
  | NONE =>
    let val s = TextIO.openOut (steps_path ())
    in steps_strm := SOME s; s end

(* -----------------------------------------------------------------------
   Look up (theory, name) for an external thm from DB
   ----------------------------------------------------------------------- *)

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

(* -----------------------------------------------------------------------
   Emit an external (ancestor) thm as an ORACLE DISK_THM step.
   Called on demand when an ext thm first appears as a parent.
   ----------------------------------------------------------------------- *)

fun emit_ext_thm thm =
  let val ln = !lines_written
      val (thy, name) = thm_thyname thm
      val sf = get_steps ()
  in
    TextIO.output(sf, "ORACLE DISK_THM " ^
      TraceExport.escape_string thy ^ " " ^
      TraceExport.escape_string name ^ "\n");
    lines_written := ln + 1;
    id_to_line := Redblackmap.insert(!id_to_line, Thm.trace_id thm, ln);
    ln
  end

(* Resolve a parent thm to its line number, emitting a DISK_THM step
   on demand if it's an external thm not yet recorded *)
fun parent_line thm =
  let val tid = Thm.trace_id thm
  in case Redblackmap.peek(!id_to_line, tid) of
       SOME ln => ln
     | NONE => emit_ext_thm thm
  end

(* -----------------------------------------------------------------------
   Cleanup and file management
   ----------------------------------------------------------------------- *)

fun close_files () =
  (case !steps_strm of
     SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
   | NONE => ();
   steps_strm := NONE)

val cleanup_fn : (unit -> unit) ref = ref (fn () => ())
fun cleanup () = (!cleanup_fn) ()

val _ = cleanup_fn := (fn () =>
  ((close_files () handle _ => ());
   (case !steps_path_ref of
      SOME s => (OS.FileSys.remove s handle _ => ()) | NONE => ())))

fun trace_reset () =
  (close_files ();
   (OS.FileSys.remove (steps_path ()) handle OS.SysErr _ => ());
   steps_path_ref := NONE;
   ty_map := Redblackmap.mkDict Type.compare;
   tm_map := Redblackmap.mkDict Term.compare;
   ty_counter := 0;
   tm_counter := 0;
   ty_list := [];
   tm_list := [];
   lines_written := 0;
   id_to_line := Redblackmap.mkDict Int.compare)

(* -----------------------------------------------------------------------
   Step recording: write step line with inline parent line numbers
   ----------------------------------------------------------------------- *)

fun record_step result_thm_opt line parent_thms =
  let
    val parent_lns = map parent_line parent_thms
    val ln = !lines_written
    val sf = get_steps ()
  in
    TextIO.output(sf, line ^
      (if null parent_lns then ""
       else " | " ^ String.concatWith " " (map its parent_lns)) ^
      "\n");
    lines_written := ln + 1;
    (case result_thm_opt of
       SOME th =>
         id_to_line := Redblackmap.insert(!id_to_line, Thm.trace_id th, ln)
     | NONE => ())
  end
  handle IO.Io _ =>
    (* Stale streams after heap restore — reopen *)
    (steps_strm := NONE;
     steps_path_ref := NONE;
     lines_written := 0;
     id_to_line := Redblackmap.mkDict Int.compare;
     (OS.Process.atExit cleanup handle _ => ());
     let val parent_lns = map parent_line parent_thms
         val ln = !lines_written
         val sf = get_steps ()
     in
       TextIO.output(sf, line ^
         (if null parent_lns then ""
          else " | " ^ String.concatWith " " (map its parent_lns)) ^
         "\n");
       lines_written := ln + 1;
       (case result_thm_opt of
          SOME th =>
            id_to_line := Redblackmap.insert(!id_to_line, Thm.trace_id th, ln)
        | NONE => ())
     end)

(* -----------------------------------------------------------------------
   Hook: pattern-match on trace_step, format step line, record
   ----------------------------------------------------------------------- *)

fun record_hook (step : (thm, term, hol_type) Thm.trace_step) =
  case step of
    Thm.TR_ASSUME (result, tm) =>
      record_step (SOME result) ("ASSUME " ^ its (iT tm)) []
  | Thm.TR_REFL (result, tm) =>
      record_step (SOME result) ("REFL " ^ its (iT tm)) []
  | Thm.TR_BETA_CONV (result, tm) =>
      record_step (SOME result) ("BETA_CONV " ^ its (iT tm)) []
  | Thm.TR_SUBST (result, replacements, template, th) =>
      let val n = length replacements
          val var_ids = String.concatWith " "
            (map (fn {redex,...} => its (iT redex)) replacements)
          val tmpl_id = its (iT template)
      in record_step (SOME result)
           ("SUBST " ^ its n ^ " " ^ var_ids ^ " " ^ tmpl_id)
           (map #residue replacements @ [th])
      end
  | Thm.TR_ABS (result, th, v) =>
      record_step (SOME result) ("ABS " ^ its (iT v)) [th]
  | Thm.TR_GEN_ABS (result, th, opt, vlist) =>
      let val opt_id = case opt of SOME t => its (iT t) | NONE => "~"
          val v_ids = String.concatWith " " (map (its o iT) vlist)
      in record_step (SOME result)
           ("GEN_ABS " ^ opt_id ^ " " ^ its (length vlist) ^
            " " ^ v_ids) [th]
      end
  | Thm.TR_INST_TYPE (result, th, theta) =>
      let val n = length theta
          val pairs = String.concatWith " "
            (map (fn {redex,residue} =>
              its (iY redex) ^ " " ^ its (iY residue)) theta)
      in record_step (SOME result) ("INST_TYPE " ^ its n ^ " " ^ pairs) [th]
      end
  | Thm.TR_DISCH (result, th, w) =>
      record_step (SOME result) ("DISCH " ^ its (iT w)) [th]
  | Thm.TR_MP (result, th1, th2) =>
      record_step (SOME result) "MP" [th1, th2]
  | Thm.TR_ALPHA (result, t1, t2) =>
      record_step (SOME result)
        ("ALPHA " ^ its (iT t1) ^ " " ^ its (iT t2)) []
  | Thm.TR_SYM (result, th) =>
      record_step (SOME result) "SYM" [th]
  | Thm.TR_TRANS (result, th1, th2) =>
      record_step (SOME result) "TRANS" [th1, th2]
  | Thm.TR_MK_COMB (result, funth, argth) =>
      record_step (SOME result) "MK_COMB" [funth, argth]
  | Thm.TR_AP_TERM (result, th, f) =>
      record_step (SOME result) ("AP_TERM " ^ its (iT f)) [th]
  | Thm.TR_AP_THM (result, th, tm) =>
      record_step (SOME result) ("AP_THM " ^ its (iT tm)) [th]
  | Thm.TR_EQ_MP (result, th1, th2) =>
      record_step (SOME result) "EQ_MP" [th1, th2]
  | Thm.TR_EQ_IMP_RULE1 (result, th) =>
      record_step (SOME result) "EQ_IMP_RULE1" [th]
  | Thm.TR_EQ_IMP_RULE2 (result, th) =>
      record_step (SOME result) "EQ_IMP_RULE2" [th]
  | Thm.TR_SPEC (result, th, t) =>
      record_step (SOME result) ("SPEC " ^ its (iT t)) [th]
  | Thm.TR_GEN (result, th, x) =>
      record_step (SOME result) ("GEN " ^ its (iT x)) [th]
  | Thm.TR_GENL (result, th, vs) =>
      let val n = length vs
          val v_ids = String.concatWith " " (map (its o iT) vs)
      in record_step (SOME result) ("GENL " ^ its n ^ " " ^ v_ids) [th]
      end
  | Thm.TR_EXISTS (result, th, w, t) =>
      record_step (SOME result)
        ("EXISTS " ^ its (iT w) ^ " " ^ its (iT t)) [th]
  | Thm.TR_CHOOSE (result, xth, bth, v) =>
      record_step (SOME result) ("CHOOSE " ^ its (iT v)) [xth, bth]
  | Thm.TR_CONJ (result, th1, th2) =>
      record_step (SOME result) "CONJ" [th1, th2]
  | Thm.TR_CONJUNCT1 (result, th) =>
      record_step (SOME result) "CONJUNCT1" [th]
  | Thm.TR_CONJUNCT2 (result, th) =>
      record_step (SOME result) "CONJUNCT2" [th]
  | Thm.TR_DISJ1 (result, th, w) =>
      record_step (SOME result) ("DISJ1 " ^ its (iT w)) [th]
  | Thm.TR_DISJ2 (result, th, w) =>
      record_step (SOME result) ("DISJ2 " ^ its (iT w)) [th]
  | Thm.TR_DISJ_CASES (result, dth, ath, bth) =>
      record_step (SOME result) "DISJ_CASES" [dth, ath, bth]
  | Thm.TR_NOT_INTRO (result, th) =>
      record_step (SOME result) "NOT_INTRO" [th]
  | Thm.TR_NOT_ELIM (result, th) =>
      record_step (SOME result) "NOT_ELIM" [th]
  | Thm.TR_CCONTR (result, fth, w) =>
      record_step (SOME result) ("CCONTR " ^ its (iT w)) [fth]
  | Thm.TR_INST (result, th, theta) =>
      let val n = length theta
          val pairs = String.concatWith " "
            (map (fn {redex,residue} =>
              its (iT redex) ^ " " ^ its (iT residue)) theta)
      in record_step (SOME result) ("INST " ^ its n ^ " " ^ pairs) [th]
      end
  | Thm.TR_Beta (result, th) =>
      record_step (SOME result) "Beta" [th]
  | Thm.TR_Mk_comb (result, thm, th1', th2') =>
      record_step (SOME result) "Mk_comb" [thm, th1', th2']
  | Thm.TR_Mk_abs (result, thm, th1', _) =>
      record_step (SOME result) "Mk_abs" [thm, th1']
  | Thm.TR_Specialize (result, th, t) =>
      record_step (SOME result) ("Specialize " ^ its (iT t)) [th]
  | Thm.TR_ORACLE (result, tg) =>
      record_step (SOME result) ("ORACLE " ^ tg ^ " " ^
        let val (hyp_list, c) = Thm.dest_thm result
            val c_id = iT c
            val hyp_ids = map iT hyp_list
        in its c_id ^ " " ^ its (length hyp_ids) ^
           (if null hyp_ids then ""
            else " " ^ String.concatWith " " (map its hyp_ids))
        end) []
  | Thm.TR_AXIOM (result, c) =>
      record_step (SOME result) ("AXIOM " ^ its (iT c)) []
  | Thm.TR_DEF_TYOP (result, thm, thy, tyop) =>
      record_step (SOME result) ("DEF_TYOP " ^ thy ^ " " ^ tyop ^ " " ^
                    its (iT (Thm.concl result))) [thm]
  | Thm.TR_DEF_SPEC (result, th, thyname, cnames) =>
      let val names_str = String.concatWith " "
            (map TraceExport.escape_string cnames)
      in record_step (SOME result) ("DEF_SPEC " ^
           TraceExport.escape_string thyname ^ " " ^
           its (length cnames) ^ " " ^ names_str ^ " " ^
           its (iT (Thm.concl result))) [th]
      end
  | Thm.TR_DISK_THM (result, src_thy, name) =>
      record_step (SOME result) ("ORACLE DISK_THM " ^
        TraceExport.escape_string src_thy ^ " " ^
        TraceExport.escape_string name) []
  | Thm.TR_COMPUTE_INIT (cval_terms, cval_type, num_type, char_eqns) =>
      let val cval_str = String.concatWith " "
            (map (fn (name, tm) =>
              TraceExport.escape_string name ^ " " ^ its (iT tm))
              cval_terms)
          val char_str = String.concatWith " "
            (map (fn (name, _) => TraceExport.escape_string name) char_eqns)
          val char_thms = map #2 char_eqns
      in record_step NONE ("COMPUTE_INIT " ^
           its (length cval_terms) ^ " " ^ cval_str ^ " " ^
           its (iY cval_type) ^ " " ^ its (iY num_type) ^ " " ^
           its (length char_eqns) ^ " " ^ char_str)
           char_thms
      end
  | Thm.TR_COMPUTE (result, code_eqs, tm) =>
      record_step (SOME result) ("COMPUTE " ^ its (iT tm)) code_eqs

(* -----------------------------------------------------------------------
   Export hook: called by Theory.export_theory via Thm.trace_export
   ----------------------------------------------------------------------- *)

fun export_hook thyname (_:string list) all_thms =
  let val () = close_files ()
  in
    TraceExport.export {
      thyname      = thyname,
      exports      = all_thms,
      types        = rev (!ty_list),
      terms        = rev (!tm_list),
      n_steps      = !lines_written,
      steps_path   = steps_path (),
      thm_line     = fn th =>
        case Redblackmap.peek(!id_to_line, Thm.trace_id th) of
          SOME ln => ln
        | NONE => ~1
    };
    (OS.FileSys.remove (steps_path ()) handle OS.SysErr _ => ());
    trace_reset ()
  end
  handle e =>
    (Feedback.HOL_WARNING "TraceRecord" "export_hook"
       ("export failed: " ^ General.exnMessage e);
     trace_reset ())

(* -----------------------------------------------------------------------
   Public API
   ----------------------------------------------------------------------- *)

fun is_active () = isSome (!Thm.trace_hook)
fun trace_step_count () = !Thm.trace_counter

(* -----------------------------------------------------------------------
   Activation: set hooks on load
   ----------------------------------------------------------------------- *)

val _ = Thm.trace_hook := SOME record_hook
val _ = Thm.trace_export_hook := SOME export_hook
val _ = OS.Process.atExit cleanup

end (* structure TraceRecord *)
