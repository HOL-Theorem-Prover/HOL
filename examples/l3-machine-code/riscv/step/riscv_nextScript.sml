(* ------------------------------------------------------------------------
   The step function Next of the RISC-V model (riscvTheory), decomposed

   Next clears the log and the flag that says that minstret was written
   (next_pre).  Then it enters the trap of the interrupt that
   checkInterrupts finds, or else fetches and runs an instruction
   (fetchAndExecute) and dispatches on NextFetch (next_post).  Last it
   counts the cycle (cycle_step).

     Next_split                 Next as these parts
     checkInterrupts_next_pre,
     Fetch_next_pre             checkInterrupts and Fetch do not depend on
                                what next_pre resets
     fetchAndExecute_next_pre   the instruction that runs (fetch_inst), the
                                bits that are returned (fetch_bits) and the
                                state in which it runs (exec_state)
     step_inst                  the instruction of a step, if it runs one

   Supporting lemmas: Fetch, checkInterrupts and the functions that they
   call commute with an update of log and of c_minstret_written (generated:
   f_log, f_minstret); the record of the instruction that Fetch writes
   collapses into one write (Delta_write'Delta, write'Delta_write'Delta);
   and Fetch changes only c_Skip and c_update (rawReadInst_state,
   Fetch_state).

   P §x p.N cites the privileged RISC-V specification, version 20260120, by
   section and printed page.
   ------------------------------------------------------------------------ *)
Theory riscv_next
Ancestors
  riscv
Libs
  wordsLib

val ERR = mk_HOL_ERR "riscv_nextTheory"

(* ------------------------------------------------------------------------
   1. The parts of Next
   ------------------------------------------------------------------------ *)

(* Next first clears the log and the flag that minstret was written *)
Definition next_pre_def:
  next_pre s =
    (s with log := []) with
      c_minstret_written := (s.procID =+ F) s.c_minstret_written
End

(* and last counts the cycle, unless mcountinhibit.CY is set after the
   step (P §3.1.12 p.47) *)
Definition cycle_step_def:
  cycle_step t =
    if ~word_bit 0 (t.c_MCSR t.procID).mcountinhibit then
      t with c_cycles := (t.procID =+ t.c_cycles t.procID + 1w) t.c_cycles
    else t
End

(* What Next does after the instruction has run, with the value v0 that
   fetchAndExecute returns (the instruction bits): the NextFetch dispatch.
   incIR says whether the instruction is counted in minstret. *)
Definition next_post_def:
  next_post incIR (v0 : word64, t) =
    case t.c_NextFetch t.procID of
      NONE =>
        write'PC (PC (incrInstret incIR t) + Skip (incrInstret incIR t))
          (incrInstret incIR t)
    | SOME (BranchTo addr) =>
        write'PC addr (write'NextFetch NONE (incrInstret incIR t))
    | SOME Mret => mret () (write'NextFetch NONE (incrInstret incIR t))
    | SOME Sret => sret () (write'NextFetch NONE (incrInstret incIR t))
    | SOME (Trap e) =>
        takeTrap
          (F, excCode e.trap, PC (write'NextFetch NONE t),
           (if e.trap = Illegal_Instr then v0 else e.tval),
           excDest (excCode e.trap, curPrivilege () (write'NextFetch NONE t))
             (write'NextFetch NONE t))
          (write'NextFetch NONE t)
End

(* The instruction that the fetch result decodes to, as fetchAndExecute
   runs it, and the bits that it returns *)
Definition fetch_inst_def:
  (fetch_inst (F_Error i) (rvc : bool) = i) /\
  (fetch_inst (F_Result (Half h)) rvc =
     if rvc then DecodeRVC h else UnknownInstruction) /\
  (fetch_inst (F_Result (Word w)) rvc = Decode w)
End

Definition fetch_bits_def:
  (fetch_bits (F_Error i) = 0w : word64) /\
  (fetch_bits (F_Result (Half h)) = w2w h) /\
  (fetch_bits (F_Result (Word w)) = w2w w)
End

(* The instruction that the step runs, or NONE if it takes an interrupt
   instead (P §3.1.14 p.49): the one decoded from the parcels that Fetch
   reads, or the internal FETCH_MISALIGNED or FETCH_FAULT of a misaligned
   pc or of a parcel that fetchAddr refuses *)
Definition step_inst_def:
  step_inst s =
    if IS_SOME (checkInterrupts () s) then NONE
    else SOME (fetch_inst (FST (Fetch () s)) (haveRVC () s))
End

(* The state in which the instruction runs *)
Definition exec_state_def:
  exec_state s = SND (Fetch () (next_pre s))
End

(* ------------------------------------------------------------------------
   2. Fetch and checkInterrupts commute with the resets of next_pre

   Neither Fetch nor checkInterrupts, nor a function that they call, reads
   or writes log or c_minstret_written (checked).  So each of them commutes
   with an update of either field (generated, one pass per field):

     f x (s with F := v) = f x s with F := v                  state
     f x (s with F := v) = (FST (f x s), SND (f x s) with F := v)
                                                              value and state
     f x (s with F := v) = f x s                              value
   ------------------------------------------------------------------------ *)

val sty = ``:riscv_state``
fun occurs ty = ty = sty orelse
                (case Lib.total dest_type ty of
                   SOME (_, args) => List.exists occurs args
                 | NONE => false)
fun lhs_of th = lhs (snd (strip_forall (concl th)))
fun lhs_const th = fst (strip_comb (lhs_of th))
val name = fst o dest_const
val def_tab =
  List.foldl (fn ((_, th), tab) =>
                case Lib.total lhs_const th of
                  SOME c => Redblackmap.insert (tab, name c, th)
                | NONE => tab)
             (Redblackmap.mkDict String.compare) (DB.definitions "riscv")
fun def_of_name n = Redblackmap.peek (def_tab, n)
(* the constants of riscvTheory in the right-hand side of a definition *)
fun callees th =
  Lib.mk_set
    (map name (List.filter (fn t => #Thy (dest_thy_const t) = "riscv")
       (find_terms is_const (rhs (snd (strip_forall (concl th)))))))
fun reach_from roots =
  let
    fun reach seen [] = seen
      | reach seen (n :: rest) =
          if Binaryset.member (seen, n) then reach seen rest
          else case def_of_name n of
                 NONE => reach (Binaryset.add (seen, n)) rest
               | SOME th => reach (Binaryset.add (seen, n)) (callees th @ rest)
  in
    Binaryset.listItems (reach (Binaryset.empty String.compare) roots)
  end
(* the functions that take the state, but for the fields of its record *)
fun is_state_fn n =
  not (String.isPrefix "recordtype." n) andalso
  (case def_of_name n of
     SOME th => occurs (type_of (lhs_const th))
   | NONE => false)

val pre_reach = reach_from ["Fetch", "checkInterrupts"]
val pre_fns =
  let
    val fns = List.filter is_state_fn pre_reach
    fun deps n = List.filter (fn d => d <> n andalso Lib.mem d fns)
                             (callees (valOf (def_of_name n)))
    (* callees first *)
    fun topo done [] = rev done
      | topo done todo =
          let
            val (ready, later) =
              List.partition
                (fn c => List.all (fn d => Lib.mem d done) (deps c)) todo
          in
            if null ready then raise ERR "topo" "cycle"
            else topo (rev ready @ done) later
          end
  in
    topo [] fns
  end

val fld_prefix = "recordtype.riscv_state.seldef."

(* the check: neither field is read or written *)
val () =
  let
    val marks =
      map (fn f => fld_prefix ^ f)
          ["log", "log_fupd", "c_minstret_written", "c_minstret_written_fupd"]
  in
    case List.filter (fn n => Lib.mem n marks) pre_reach of
      [] => ()
    | l => raise ERR "next_pre"
             ("Fetch or checkInterrupts reaches " ^ String.concatWith ", " l)
  end

(* the application of f to its arguments and the state s, as in its
   definition *)
fun applied n s =
  let
    val th = valOf (def_of_name n)
    val c = lhs_const th
    val (_, dargs) = strip_comb (lhs_of th)
    val (args, rty) = strip_fun (type_of c)
    val app =
      case (args, dargs) of
        ([_], _) => mk_comb (c, s)
      | ([_, _], [d]) => mk_comb (mk_comb (c, d), s)
      | _ => raise ERR "applied" n
  in
    (app, rty)
  end

(* The lemmas f_<suffix> of the functions of pre_fns for the field fld,
   updated to the variable v *)
fun comm_pass (fld, v, suffix) =
  let
    val upd = prim_mk_const {Name = fld_prefix ^ fld ^ "_fupd", Thy = "riscv"}
    (* st with fld := v *)
    fun with_v st =
      mk_comb (mk_comb (upd, combinSyntax.mk_K_1 (v, type_of v)), st)
    val COND_UP =
      let
        val b = mk_var ("b", bool)
        val x = mk_var ("x", sty)
        val y = mk_var ("y", sty)
      in
        prove (list_mk_forall ([b, x, y, v],
                 mk_eq (mk_cond (b, with_v x, with_v y),
                        with_v (mk_cond (b, x, y)))), rw [])
      end
    fun goal n =
      let
        val s = mk_var ("s", sty)
        val (app, rty) = applied n s
        val (lapp, _) = applied n (with_v s)
        val r =
          if rty = sty then with_v app
          else if occurs rty then
            pairSyntax.mk_pair (pairSyntax.mk_fst app,
                                with_v (pairSyntax.mk_snd app))
          else app
        val g = mk_eq (lapp, r)
      in
        list_mk_forall (free_vars g, g)
      end
    val lemmas = ref ([] : thm list)
    fun tac def =
      rpt gen_tac
      \\ simp ([def, COND_UP, pairTheory.UNCURRY] @ !lemmas)
      \\ rpt (CASE_TAC \\ simp ([COND_UP, pairTheory.UNCURRY] @ !lemmas))
    fun prove_one n =
      let
        val th = prove (goal n, tac (valOf (def_of_name n)))
                 handle e => (print ("riscv_next: no " ^ suffix ^
                                     " lemma for " ^ n ^ "\n"); raise e)
      in
        lemmas := th :: !lemmas;
        (n, save_thm (n ^ "_" ^ suffix, th))
      end
  in
    map prove_one pre_fns
  end

val log_thms =
  comm_pass ("log", mk_var ("l", ``:(num # string) list``), "log")
val minstret_thms =
  comm_pass ("c_minstret_written", mk_var ("w", ``:word8 -> bool``),
             "minstret")
(* f_log and f_minstret *)
fun pre_thms n = [Lib.assoc n log_thms, Lib.assoc n minstret_thms]

Theorem checkInterrupts_next_pre:
  !s. checkInterrupts () (next_pre s) = checkInterrupts () s
Proof
  simp (next_pre_def :: pre_thms "checkInterrupts")
QED

Theorem Fetch_next_pre:
  !s. Fetch () (next_pre s) =
      (FST (Fetch () s),
       SND (Fetch () s) with
         <| log := [];
            c_minstret_written := (s.procID =+ F) s.c_minstret_written |>)
Proof
  simp (next_pre_def :: pre_thms "Fetch")
QED

(* ------------------------------------------------------------------------
   3. Next, split
   ------------------------------------------------------------------------ *)

(* Next, as clear_logs and the reset of c_minstret_written (next_pre),
   then the trap entry of an interrupt, or the fetch and the instruction
   followed by the NextFetch dispatch (next_post), then the cycle count
   (cycle_step) *)
Theorem Next_split:
  !s. Next s =
      cycle_step
        (case checkInterrupts () s of
           SOME (i, p) =>
             takeTrap (T, interruptIndex i, PC s, 0w, p) (next_pre s)
         | NONE =>
             next_post (~word_bit 2 (s.c_MCSR s.procID).mcountinhibit)
               (fetchAndExecute () (next_pre s)))
Proof
  gen_tac
  \\ simp_tac (srw_ss()) [Next_def, LET_THM, clear_logs_def,
                          pairTheory.UNCURRY,
                          GSYM (SIMP_RULE (srw_ss()) [] next_pre_def),
                          NextFetch_def, MCSR_def]
  \\ simp_tac std_ss [checkInterrupts_next_pre]
  \\ `(PC (next_pre s) = PC s) /\
      ((next_pre s).c_MCSR (next_pre s).procID = s.c_MCSR s.procID)`
     by simp [next_pre_def, PC_def]
  \\ asm_simp_tac std_ss []
  \\ Cases_on `fetchAndExecute () (next_pre s)`
  \\ asm_simp_tac (srw_ss()) [next_post_def, cycle_step_def, LET_THM]
  \\ rpt CASE_TAC
  \\ asm_simp_tac (srw_ss()) []
QED

(* ------------------------------------------------------------------------
   4. The fetch and the instruction
   ------------------------------------------------------------------------ *)

(* Fetch records the instruction in the StateDelta record of the hart by a
   chain of nine writes, each reading the record back; these collapse it *)
Theorem Delta_write'Delta:
  !x s. Delta (write'Delta x s) = x
Proof
  simp [Delta_def, write'Delta_def]
QED

Theorem write'Delta_write'Delta:
  !x y s. write'Delta x (write'Delta y s) = write'Delta x s
Proof
  simp [write'Delta_def, combinTheory.UPDATE_EQ]
QED

(* rawReadInst changes only c_Skip (the length of the instruction), and
   so Fetch only c_Skip and c_update (the record of the instruction) *)
Theorem rawReadInst_state:
  !a s. ?k. SND (rawReadInst a s) = s with c_Skip := k
Proof
  rw [rawReadInst_def, write'Skip_def, pairTheory.UNCURRY]
  \\ metis_tac []
QED

Theorem Fetch_state:
  !s. ?k u. SND (Fetch () s) = s with <| c_Skip := k; c_update := u |>
Proof
  gen_tac
  \\ simp_tac std_ss
       [Fetch_def, Delta_write'Delta, write'Delta_write'Delta, LET_THM,
        pairTheory.UNCURRY, TypeBase.case_def_of ``:rawInstType``,
        TypeBase.case_def_of ``:TransResult``]
  \\ rpt (CASE_TAC \\ asm_simp_tac std_ss [])
  \\ TRY (qmatch_goalsub_rename_tac `rawReadInst a s`
          \\ qspecl_then [`a`, `s`] strip_assume_tac rawReadInst_state)
  \\ asm_simp_tac (srw_ss())
       [write'Delta_def, riscv_state_component_equality]
QED

Theorem fetchAndExecute_next_pre:
  !s. fetchAndExecute () (next_pre s) =
      (fetch_bits (FST (Fetch () s)),
       Run (fetch_inst (FST (Fetch () s)) (haveRVC () s)) (exec_state s))
Proof
  gen_tac
  \\ `haveRVC () (exec_state s) = haveRVC () s`
     by (qspec_then `next_pre s` strip_assume_tac Fetch_state
         \\ asm_simp_tac (srw_ss())
              [exec_state_def, haveRVC_def, MCSR_def, next_pre_def])
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [fetchAndExecute_def, LET_THM, pairTheory.UNCURRY,
                      GSYM exec_state_def, Fetch_next_pre]
  \\ strip_tac
  \\ Cases_on `FST (Fetch () s)`
  \\ TRY (Cases_on `r`)
  \\ asm_simp_tac (srw_ss()) [fetch_inst_def, fetch_bits_def]
QED
