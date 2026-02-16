(* TraceRecord: proof trace recording for stdknl.

   Sets Thm.trace_hook to record each inference step to per-PID temp files.
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
   Per-PID temp files for parallel build safety
   ----------------------------------------------------------------------- *)

val steps_strm : TextIO.outstream option ref = ref NONE
val parents_strm : TextIO.outstream option ref = ref NONE
val lines_written : int ref = ref 0

val steps_path_ref : string option ref = ref NONE
val parents_path_ref : string option ref = ref NONE

fun trace_paths () =
  case (!steps_path_ref, !parents_path_ref) of
    (SOME s, SOME p) => (s, p)
  | _ =>
    let val pid = SysWord.toString (Posix.Process.pidToWord
                    (Posix.ProcEnv.getpid ()))
        val s = ".trace_" ^ pid ^ "_steps.log"
        val p = ".trace_" ^ pid ^ "_parents.tbl"
    in steps_path_ref := SOME s;
       parents_path_ref := SOME p;
       (s, p)
    end

fun steps_path () = #1 (trace_paths ())
fun parents_path () = #2 (trace_paths ())

fun open_streams () =
  let val s = TextIO.openOut (steps_path ())
      val p = TextIO.openOut (parents_path ())
  in steps_strm := SOME s;
     parents_strm := SOME p;
     (s, p)
  end

fun get_steps () = case !steps_strm of
    SOME s => s | NONE => #1 (open_streams ())
fun get_parents () = case !parents_strm of
    SOME s => s | NONE => #2 (open_streams ())

(* -----------------------------------------------------------------------
   External thm cache: parent thms from ancestor theories
   ----------------------------------------------------------------------- *)

(* Maps thm_id → (hyps, concl, source_theory_opt) *)
val ext_thm_cache : (int, term list * term * string option) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Int.compare)

fun thm_src_theory thm =
  (case Tag.dep_of (Thm.tag thm) of
     Dep.DEP_SAVED (did, _) => SOME (Dep.depthy_of did)
   | _ => NONE)
  handle _ => NONE

fun cache_ext_parents parent_thms =
  let val base = !Thm.trace_counter - !lines_written
  in
    if !lines_written = 0 then ()
    else List.app (fn thm =>
      let val id = Thm.trace_id thm
      in if id < base then
        (case Redblackmap.peek(!ext_thm_cache, id) of
           SOME _ => ()
         | NONE =>
           let val (hyp_list, c) = Thm.dest_thm thm
               val thy_opt = thm_src_theory thm
           in ignore (iT c);
              List.app (ignore o iT) hyp_list;
              ext_thm_cache :=
                Redblackmap.insert(!ext_thm_cache, id,
                                   (hyp_list, c, thy_opt))
           end)
        else ()
      end) parent_thms
  end

fun cache_ext_thm_with_thy thm thy_opt =
  case Redblackmap.peek(!ext_thm_cache, Thm.trace_id thm) of
    SOME _ => ()
  | NONE =>
    let val (hyp_list, c) = Thm.dest_thm thm
    in ignore (iT c);
       List.app (ignore o iT) hyp_list;
       ext_thm_cache :=
         Redblackmap.insert(!ext_thm_cache, Thm.trace_id thm,
                            (hyp_list, c, thy_opt))
    end

fun cache_ext_thm thm = cache_ext_thm_with_thy thm NONE

(* -----------------------------------------------------------------------
   Cleanup and file management
   ----------------------------------------------------------------------- *)

val cleanup_fn : (unit -> unit) ref = ref (fn () => ())
fun cleanup () = (!cleanup_fn) ()

fun close_files () =
  ((case !steps_strm of
      SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
    | NONE => ());
   (case !parents_strm of
      SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
    | NONE => ());
   steps_strm := NONE;
   parents_strm := NONE)

val _ = cleanup_fn := (fn () =>
  ((close_files () handle _ => ());
   (case !steps_path_ref of
      SOME s => (OS.FileSys.remove s handle _ => ()) | NONE => ());
   (case !parents_path_ref of
      SOME p => (OS.FileSys.remove p handle _ => ()) | NONE => ())))

fun trace_reset () =
  (close_files ();
   (OS.FileSys.remove (steps_path ()) handle OS.SysErr _ => ());
   (OS.FileSys.remove (parents_path ()) handle OS.SysErr _ => ());
   steps_path_ref := NONE;
   parents_path_ref := NONE;
   ty_map := Redblackmap.mkDict Type.compare;
   tm_map := Redblackmap.mkDict Term.compare;
   ty_counter := 0;
   tm_counter := 0;
   ty_list := [];
   tm_list := [];
   lines_written := 0;
   ext_thm_cache := Redblackmap.mkDict Int.compare)

(* -----------------------------------------------------------------------
   Step recording: write step line + parent IDs to temp files
   ----------------------------------------------------------------------- *)

fun record_step line parent_thms =
  let
    val parent_ids = map Thm.trace_id parent_thms
    val sf = get_steps ()
    val pf = get_parents ()
    fun write (s, p) =
      (TextIO.output(s, line);
       TextIO.output(s, "\n");
       TextIO.output(p, String.concatWith " " (map its parent_ids));
       TextIO.output(p, "\n"))
  in
    write (sf, pf)
    handle IO.Io _ =>
      (* Stale streams after heap restore — reopen both atomically *)
      (steps_strm := NONE; parents_strm := NONE;
       steps_path_ref := NONE; parents_path_ref := NONE;
       lines_written := 0;
       (OS.Process.atExit cleanup handle _ => ());
       write (open_streams ()));
    lines_written := !lines_written + 1;
    cache_ext_parents parent_thms
  end

(* Format thm statement: "<concl_id> <n_hyps> <hyp1_id> ..." *)
fun fmt_thm_stmt thm =
  let val (hyp_list, c) = Thm.dest_thm thm
      val c_id = iT c
      val hyp_ids = map iT hyp_list
  in its c_id ^ " " ^ its (length hyp_ids) ^
     (if null hyp_ids then ""
      else " " ^ String.concatWith " " (map its hyp_ids))
  end

(* -----------------------------------------------------------------------
   Hook: pattern-match on trace_step, format step line, record
   ----------------------------------------------------------------------- *)

fun record_hook (step : Thm.trace_step) =
  case step of
    Thm.TR_ASSUME (_, tm) =>
      record_step ("ASSUME " ^ its (iT tm)) []
  | Thm.TR_REFL (_, tm) =>
      record_step ("REFL " ^ its (iT tm)) []
  | Thm.TR_BETA_CONV (_, tm) =>
      record_step ("BETA_CONV " ^ its (iT tm)) []
  | Thm.TR_SUBST (_, replacements, template, th) =>
      let val n = length replacements
          val var_ids = String.concatWith " "
            (map (fn {redex,...} => its (iT redex)) replacements)
          val tmpl_id = its (iT template)
      in record_step ("SUBST " ^ its n ^ " " ^ var_ids ^ " " ^ tmpl_id)
           (map #residue replacements @ [th])
      end
  | Thm.TR_ABS (_, th, v) =>
      record_step ("ABS " ^ its (iT v)) [th]
  | Thm.TR_GEN_ABS (_, th, opt, vlist) =>
      let val opt_id = case opt of SOME t => its (iT t) | NONE => "~"
          val v_ids = String.concatWith " " (map (its o iT) vlist)
      in record_step ("GEN_ABS " ^ opt_id ^ " " ^ its (length vlist) ^
                       " " ^ v_ids) [th]
      end
  | Thm.TR_INST_TYPE (_, th, theta) =>
      let val n = length theta
          val pairs = String.concatWith " "
            (map (fn {redex,residue} =>
              its (iY redex) ^ " " ^ its (iY residue)) theta)
      in record_step ("INST_TYPE " ^ its n ^ " " ^ pairs) [th]
      end
  | Thm.TR_DISCH (_, th, w) =>
      record_step ("DISCH " ^ its (iT w)) [th]
  | Thm.TR_MP (_, th1, th2) =>
      record_step "MP" [th1, th2]
  | Thm.TR_ALPHA (_, t1, t2) =>
      record_step ("ALPHA " ^ its (iT t1) ^ " " ^ its (iT t2)) []
  | Thm.TR_SYM (_, th) =>
      record_step "SYM" [th]
  | Thm.TR_TRANS (_, th1, th2) =>
      record_step "TRANS" [th1, th2]
  | Thm.TR_MK_COMB (_, funth, argth) =>
      record_step "MK_COMB" [funth, argth]
  | Thm.TR_AP_TERM (_, th, f) =>
      record_step ("AP_TERM " ^ its (iT f)) [th]
  | Thm.TR_AP_THM (_, th, tm) =>
      record_step ("AP_THM " ^ its (iT tm)) [th]
  | Thm.TR_EQ_MP (_, th1, th2) =>
      record_step "EQ_MP" [th1, th2]
  | Thm.TR_EQ_IMP_RULE1 (_, th) =>
      record_step "EQ_IMP_RULE1" [th]
  | Thm.TR_EQ_IMP_RULE2 (_, th) =>
      record_step "EQ_IMP_RULE2" [th]
  | Thm.TR_SPEC (_, th, t) =>
      record_step ("SPEC " ^ its (iT t)) [th]
  | Thm.TR_GEN (_, th, x) =>
      record_step ("GEN " ^ its (iT x)) [th]
  | Thm.TR_GENL (_, th, vs) =>
      let val n = length vs
          val v_ids = String.concatWith " " (map (its o iT) vs)
      in record_step ("GENL " ^ its n ^ " " ^ v_ids) [th]
      end
  | Thm.TR_EXISTS (_, th, w, t) =>
      record_step ("EXISTS " ^ its (iT w) ^ " " ^ its (iT t)) [th]
  | Thm.TR_CHOOSE (_, xth, bth, v) =>
      record_step ("CHOOSE " ^ its (iT v)) [xth, bth]
  | Thm.TR_CONJ (_, th1, th2) =>
      record_step "CONJ" [th1, th2]
  | Thm.TR_CONJUNCT1 (_, th) =>
      record_step "CONJUNCT1" [th]
  | Thm.TR_CONJUNCT2 (_, th) =>
      record_step "CONJUNCT2" [th]
  | Thm.TR_DISJ1 (_, th, w) =>
      record_step ("DISJ1 " ^ its (iT w)) [th]
  | Thm.TR_DISJ2 (_, th, w) =>
      record_step ("DISJ2 " ^ its (iT w)) [th]
  | Thm.TR_DISJ_CASES (_, dth, ath, bth) =>
      record_step "DISJ_CASES" [dth, ath, bth]
  | Thm.TR_NOT_INTRO (_, th) =>
      record_step "NOT_INTRO" [th]
  | Thm.TR_NOT_ELIM (_, th) =>
      record_step "NOT_ELIM" [th]
  | Thm.TR_CCONTR (_, fth, w) =>
      record_step ("CCONTR " ^ its (iT w)) [fth]
  | Thm.TR_INST (_, th, theta) =>
      let val n = length theta
          val pairs = String.concatWith " "
            (map (fn {redex,residue} =>
              its (iT redex) ^ " " ^ its (iT residue)) theta)
      in record_step ("INST " ^ its n ^ " " ^ pairs) [th]
      end
  | Thm.TR_Beta (_, th) =>
      record_step "Beta" [th]
  | Thm.TR_Mk_comb (_, thm, th1', th2') =>
      record_step "Mk_comb" [thm, th1', th2']
  | Thm.TR_Mk_abs (_, thm, th1', bvar) =>
      record_step ("Mk_abs " ^ its (iT bvar)) [thm, th1']
  | Thm.TR_Specialize (_, th, t) =>
      record_step ("Specialize " ^ its (iT t)) [th]
  | Thm.TR_ORACLE (result, tg) =>
      record_step ("ORACLE " ^ tg ^ " " ^ fmt_thm_stmt result) []
  | Thm.TR_AXIOM (_, c) =>
      record_step ("AXIOM " ^ its (iT c)) []
  | Thm.TR_DEF_TYOP (result, thm, thy, tyop) =>
      record_step ("DEF_TYOP " ^ thy ^ " " ^ tyop ^ " " ^
                    its (iT (Thm.concl result))) [thm]
  | Thm.TR_DEF_SPEC (result, th, thyname, cnames) =>
      let val names_str = String.concatWith " "
            (map TraceExport.escape_string cnames)
      in record_step ("DEF_SPEC " ^
           TraceExport.escape_string thyname ^ " " ^
           its (length cnames) ^ " " ^ names_str ^ " " ^
           its (iT (Thm.concl result))) [th]
      end
  | Thm.TR_DISK_THM (result, src_thy) =>
      (cache_ext_thm_with_thy result (SOME src_thy);
       record_step ("DISK_THM " ^ fmt_thm_stmt result) [])
  | Thm.TR_COMPUTE (_, parents, tm, eqn) =>
      record_step ("COMPUTE " ^ its (iT tm) ^ " " ^ its (iT eqn)) parents

(* -----------------------------------------------------------------------
   Export hook: called by Theory.export_theory via Thm.trace_export
   ----------------------------------------------------------------------- *)

fun export_hook thyname thy_parents all_thms =
  let
    val () = close_files ()
    (* Cache re-exported ancestor thms that were never parents of local steps *)
    val base = !Thm.trace_counter - !lines_written
    val _ = List.app (fn (_, th) =>
      let val tid = Thm.trace_id th
      in if tid < base then cache_ext_thm th else ()
      end) all_thms
  in
    TraceExport.export {
      thyname      = thyname,
      thy_parents  = thy_parents,
      exports      = all_thms,
      types        = rev (!ty_list),
      terms        = rev (!tm_list),
      counter      = !Thm.trace_counter,
      ext_cache    = !ext_thm_cache,
      steps_path   = steps_path (),
      parents_path = parents_path (),
      thm_id       = Thm.trace_id
    };
    (* Clean up temp files *)
    (OS.FileSys.remove (steps_path ()) handle OS.SysErr _ => ());
    (OS.FileSys.remove (parents_path ()) handle OS.SysErr _ => ());
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
val _ = case OS.Process.getEnv "HOL_TRACE_BENCHMARKS" of
          SOME _ => TraceExport.bench_mode := true
        | NONE => ()

end (* structure TraceRecord *)
