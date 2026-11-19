(* ------------------------------------------------------------------------
   The step function Next of the RISC-V model and the step function
   NextRISCV of the step library agree up to the ghost fields of the state,
   for an instruction that reads no counter CSR.

   Next (riscvTheory) clears the log, resets c_minstret_written, takes the
   interrupt that checkInterrupts finds, fetches with the logging of the
   model (the StateDelta record c_update), runs the instruction, counts it
   in c_instret and the cycle in c_cycles.  NextRISCV (riscv_stepTheory)
   takes no interrupt, fetches without the logging, runs the same
   instruction, returns NONE if an exception was raised, and counts
   nothing.  So the two differ in

     log, c_update, exception, c_cycles, c_instret, c_minstret_written

   (the ghost fields), and in nothing else as long as the instruction reads
   no counter CSR: no function of the model reads a ghost field except to
   compute another ghost field, but for the CSR reads of mcycle, minstret,
   cycle and instret (counter_csr).

   - ghost_reset s is s with the ghost fields set to fixed values, and
     ghost_eq s t says that s and t agree on every other field;
   - <f>_ghost, generated for the functions reachable from Next that do
     not mention a ghost field: f commutes with ghost_reset; and for the
     functions that do, the relational form (ghost-equal states give
     ghost-equal results and equal values), or that the function changes
     only ghost fields;
   - Run_ghost: Run i is a congruence for ghost_eq when i reads no counter;
   - Fetch_step_spec: where the step library's Fetch succeeds, the model's
     Fetch returns the same instruction bits and state, but for c_update;
   - Next_NextRISCV_ghost: from a state that takes no interrupt and whose
     fetched instruction reads no counter, Next and NextRISCV step to
     ghost-equal states, from any two ghost-equal states.

   The build checks which functions mention which ghost field (section 1),
   so that a change of the model that adds a reader or writer of a ghost
   field stops it.

   The theory has the step library's riscv_stepTheory as an ancestor,
   opened qualified only (its Fetch_def would shadow the model's); its
   Fetch and the model's are named riscv_step$Fetch and riscv$Fetch.

   P §x p.N cites the privileged RISC-V specification, version 20260120, by
   section and printed page.
   ------------------------------------------------------------------------ *)
Theory riscv_refine
Ancestors
  riscv riscv_next riscv_step[qualified]
Libs
  wordsLib blastLib

val ERR = mk_HOL_ERR "riscv_refineTheory"

(* ------------------------------------------------------------------------
   1. The ghost fields, and the functions that mention them (checked)
   ------------------------------------------------------------------------ *)

Definition ghost_reset_def:
  ghost_reset (s:riscv_state) =
    s with <| log := []; c_update := K ARB; exception := NoException;
              c_cycles := K 0w; c_instret := K 0w;
              c_minstret_written := K F |>
End

Definition ghost_eq_def:
  ghost_eq s t <=> (ghost_reset s = ghost_reset t)
End

(* The counter CSRs: mcycle, minstret and their read-only shadows cycle
   and instret (P §3.1.10 p.46, §3.1.11 p.47; Table 4 p.16, Table 7
   p.20-21), the only CSRs whose read reads c_cycles or c_instret (checked
   below). *)
Definition counter_csr_def:
  counter_csr (c:word12) <=> MEM c [0xB00w; 0xB02w; 0xC00w; 0xC02w]
End

(* The instructions that read a counter CSR into a register. *)
Definition reads_counter_def:
  (reads_counter (System (CSRRW (rd, rs1, c))) <=> counter_csr c) /\
  (reads_counter (System (CSRRS (rd, rs1, c))) <=> counter_csr c) /\
  (reads_counter (System (CSRRC (rd, rs1, c))) <=> counter_csr c) /\
  (reads_counter (System (CSRRWI (rd, rs1, c))) <=> counter_csr c) /\
  (reads_counter (System (CSRRSI (rd, rs1, c))) <=> counter_csr c) /\
  (reads_counter (System (CSRRCI (rd, rs1, c))) <=> counter_csr c) /\
  (reads_counter _ <=> F)
End

(* The call graph of the model, from its definitions *)
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
fun def_of n = case def_of_name n of
                 SOME th => th
               | NONE => raise ERR "def_of" n
fun def_rhs n = rhs (snd (strip_forall (concl (def_of n))))
(* the constants of riscvTheory in a term, and in a definition *)
fun consts_of tm =
  Lib.mk_set
    (map name (List.filter (fn t => #Thy (dest_thy_const t) = "riscv")
                 (find_terms is_const tm)))
fun callees n = case def_of_name n of
                  SOME _ => consts_of (def_rhs n)
                | NONE => []
fun reach_from roots =
  let
    fun reach seen [] = seen
      | reach seen (n :: rest) =
          if Binaryset.member (seen, n) then reach seen rest
          else reach (Binaryset.add (seen, n)) (callees n @ rest)
  in
    Binaryset.listItems (reach (Binaryset.empty String.compare) roots)
  end
val reachable = reach_from ["Next"]
(* the functions that take the state, but for the fields of its record *)
fun is_state_fn n =
  not (String.isPrefix "recordtype." n) andalso
  (case def_of_name n of
     SOME th => occurs (type_of (lhs_const th))
   | NONE => false)
val state_fns = List.filter is_state_fn reachable

val fld_prefix = "recordtype.riscv_state.seldef."
val ghost_fields =
  ["log", "c_update", "exception", "c_cycles", "c_instret",
   "c_minstret_written"]
val all_fields = map fst (TypeBase.fields_of sty)
val other_fields =
  List.filter (fn f => not (Lib.mem f ghost_fields)) all_fields
val () =
  if List.all (fn f => Lib.mem f all_fields) ghost_fields then ()
  else raise ERR "ghost_fields" "not a field of riscv_state"
fun field_sel fld = prim_mk_const {Name = fld_prefix ^ fld, Thy = "riscv"}
fun field_upd fld =
  prim_mk_const {Name = fld_prefix ^ fld ^ "_fupd", Thy = "riscv"}

fun set_check what got expected =
  if Lib.set_eq got expected then ()
  else raise ERR "classification"
         (what ^ " are not the expected ones: unexpected [" ^
          String.concatWith ", " (Lib.set_diff got expected) ^
          "], missing [" ^
          String.concatWith ", " (Lib.set_diff expected got) ^ "]")

(* the fields whose selector or update a term mentions, and those that it
   updates *)
fun fields_in tm =
  let val cs = consts_of tm in
    List.filter (fn f => Lib.mem (fld_prefix ^ f) cs orelse
                         Lib.mem (fld_prefix ^ f ^ "_fupd") cs) all_fields
  end
fun upds_in tm =
  let val cs = consts_of tm in
    List.filter (fn f => Lib.mem (fld_prefix ^ f ^ "_fupd") cs) all_fields
  end
(* direct n, closed under the callees of n *)
fun fixpoint direct =
  let
    val init =
      List.foldl (fn (n, t) => Redblackmap.insert (t, n, direct n))
                 (Redblackmap.mkDict String.compare) reachable
    fun step t =
      List.foldl
        (fn (n, (t', ch)) =>
           let
             val cur = Redblackmap.find (t', n)
             val new = List.foldl (fn (c, acc) =>
                          case Redblackmap.peek (t', c) of
                            SOME u => Lib.union u acc
                          | NONE => acc) cur (callees n)
           in
             if length new > length cur
             then (Redblackmap.insert (t', n, new), true)
             else (t', ch)
           end) (t, false) reachable
    fun fix t = case step t of (t', true) => fix t' | (t', false) => t'
  in
    fix init
  end
(* the ghost fields that a function mentions, itself or through a callee *)
fun direct_ghosts n =
  case def_of_name n of
    NONE => []
  | SOME _ =>
      List.filter (fn f => Lib.mem f ghost_fields) (fields_in (def_rhs n))
val ghost_tab = fixpoint direct_ghosts
fun ghosts n = Redblackmap.find (ghost_tab, n)
(* the fields that a function updates, itself or through a callee *)
val upd_tab =
  fixpoint (fn n => case def_of_name n of
                      NONE => []
                    | SOME _ => upds_in (def_rhs n))
fun upds_of_term tm =
  List.foldl (fn (c, acc) => case Redblackmap.peek (upd_tab, c) of
                               SOME u => Lib.union u acc
                             | NONE => acc) (upds_in tm) (consts_of tm)

(* The ghost fields are exactly the fields that Next updates outside the
   instruction (in its own definition, clear_logs and incrInstret), the
   fields that the model's Fetch updates and the step library's does not
   (c_update, the record of the instruction), and the fields that NextRISCV
   reads itself (the exception, for its NONE result). *)
val () =
  let
    val step_fetch =
      rhs (snd (strip_forall (concl riscv_stepTheory.Fetch_def)))
    val nextriscv =
      rhs (snd (strip_forall (concl riscv_stepTheory.NextRISCV_def)))
    val computed =
      Lib.U [upds_in (def_rhs "Next"),
             upds_of_term (def_rhs "clear_logs"),
             upds_of_term (def_rhs "incrInstret"),
             Lib.set_diff (upds_of_term (def_rhs "Fetch"))
                          (upds_of_term step_fetch),
             fields_in nextriscv]
  in
    set_check "the fields that Next and NextRISCV treat differently"
      computed ghost_fields
  end

(* Which definitions mention a ghost field themselves *)
val () =
  let
    fun check (n, expected) =
      set_check ("the ghost fields of " ^ n) (direct_ghosts n) expected
    val direct = List.filter (fn n => not (null (direct_ghosts n))) reachable
  in
    set_check "the definitions that mention a ghost field" direct
      ["clear_logs", "Delta", "write'Delta", "raise'exception", "CSRMap",
       "write'CSRMap", "incrInstret", "Next"];
    List.app check
      [("clear_logs", ["log"]),                     (* log := [] *)
       ("Delta", ["c_update"]),                     (* the StateDelta record *)
       ("write'Delta", ["c_update"]),
       ("raise'exception", ["exception"]),          (* the only reader *)
       ("CSRMap", ["c_cycles", "c_instret"]),       (* the counter CSRs *)
       ("write'CSRMap", ["c_cycles", "c_instret", "c_minstret_written"]),
       ("incrInstret", ["c_instret", "c_minstret_written"]),
       ("Next", ["c_cycles", "c_minstret_written"])]
  end

(* c_update is read and written only through Delta and write'Delta, and
   only by the fetch and by the writes of a CSR or an FPR *)
val () =
  set_check "the callers of Delta and write'Delta"
    (List.filter (fn n => Lib.mem "Delta" (callees n) orelse
                          Lib.mem "write'Delta" (callees n)) reachable)
    ["Fetch", "writeCSR", "writeFPRS", "writeFPRD"]

(* The cases of CSRMap that read c_cycles or c_instret are those of the
   counter CSRs *)
val () =
  let
    val (_, body) = dest_abs (def_rhs "CSRMap")
    val case_fn = rand (rator body)            (* literal_case case_fn csr *)
    val (_, cb) = dest_abs case_fn
    fun walk t acc =
      if is_cond t then
        let val (c, a, b) = dest_cond t in walk b ((c, a) :: acc) end
      else (rev acc, t)
    val (cases, default) = walk cb []
    fun counter a =
      List.exists (fn f => Lib.mem f ["c_cycles", "c_instret"]) (fields_in a)
    val readers =
      List.mapPartial
        (fn (c, a) =>
           if counter a
           then SOME (Arbnum.toString (wordsSyntax.dest_word_literal (rhs c)))
           else NONE) cases
  in
    set_check "the CSRs whose read reads a counter" readers
      ["2816", "2818", "3072", "3074"];   (* 0xB00, 0xB02, 0xC00, 0xC02 *)
    if counter default
    then raise ERR "classification" "CSRMap: default case" else ()
  end

(* The functions reachable from Next that mention a ghost field, themselves
   or through a callee *)
val touching = List.filter (fn n => not (null (ghosts n))) state_fns
val fp_writers =
  ["dfn'FADD_S", "dfn'FSUB_S", "dfn'FMUL_S", "dfn'FDIV_S", "dfn'FSQRT_S",
   "dfn'FMIN_S", "dfn'FMAX_S", "dfn'FMADD_S", "dfn'FMSUB_S", "dfn'FNMADD_S",
   "dfn'FNMSUB_S", "dfn'FSGNJ_S", "dfn'FSGNJN_S", "dfn'FSGNJX_S",
   "dfn'FMV_S_X", "dfn'FCVT_S_W", "dfn'FCVT_S_WU", "dfn'FCVT_S_L",
   "dfn'FCVT_S_LU", "dfn'FCVT_S_D", "dfn'FLW",
   "dfn'FADD_D", "dfn'FSUB_D", "dfn'FMUL_D", "dfn'FDIV_D", "dfn'FSQRT_D",
   "dfn'FMIN_D", "dfn'FMAX_D", "dfn'FMADD_D", "dfn'FMSUB_D", "dfn'FNMADD_D",
   "dfn'FNMSUB_D", "dfn'FSGNJ_D", "dfn'FSGNJN_D", "dfn'FSGNJX_D",
   "dfn'FMV_D_X", "dfn'FCVT_D_W", "dfn'FCVT_D_WU", "dfn'FCVT_D_L",
   "dfn'FCVT_D_LU", "dfn'FCVT_D_S", "dfn'FLD"]
val csr_insts =
  ["dfn'CSRRW", "dfn'CSRRS", "dfn'CSRRC", "dfn'CSRRWI", "dfn'CSRRSI",
   "dfn'CSRRCI"]
val () =
  set_check "the functions that mention a ghost field" touching
    ([(* the definitions above *)
      "clear_logs", "Delta", "write'Delta", "raise'exception", "CSRMap",
      "write'CSRMap", "incrInstret", "Next",
      (* the CSR accesses, the fetch, the FPR writes, the trap entry *)
      "CSR", "write'CSR", "writeCSR", "accessCSR", "Fetch", "writeFPRS",
      "writeFPRD", "takeTrap",
      (* the step *)
      "Run", "fetchAndExecute"] @ csr_insts @ fp_writers)
val () =
  set_check "the F and D instructions whose only ghost field is c_update"
    (List.filter
       (fn n => String.isPrefix "dfn'" n andalso ghosts n = ["c_update"])
       touching) fp_writers

(* the functions that take the state, callees first *)
val order =
  let
    fun deps n =
      List.filter (fn d => d <> n andalso Lib.mem d state_fns) (callees n)
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
    topo [] state_fns
  end
val ghost_free = List.filter (fn n => not (Lib.mem n touching)) order

val () =
  print ("riscv_refine: of the " ^ Int.toString (length state_fns) ^
         " state functions reachable from Next, " ^
         Int.toString (length touching) ^ " mention a ghost field\n")

(* ------------------------------------------------------------------------
   2. ghost_reset and ghost_eq
   ------------------------------------------------------------------------ *)

val ghost_reset_tm = fst (strip_comb (lhs_of ghost_reset_def))
val ghost_eq_tm = fst (strip_comb (lhs_of ghost_eq_def))
fun gr t = mk_comb (ghost_reset_tm, t)
fun geq (a, b) = list_mk_comb (ghost_eq_tm, [a, b])
val s_var = mk_var ("s", sty)
val t_var = mk_var ("t", sty)
(* fld_fupd f, with f a variable *)
fun fupd_f fld =
  let val u = field_upd fld in
    mk_comb (u, mk_var ("f", fst (dom_rng (type_of u))))
  end

(* the other fields of ghost_reset s are those of s *)
val ghost_reset_fields =
  LIST_CONJ (map (fn fld =>
    GEN s_var (prove (mk_eq (mk_comb (field_sel fld, gr s_var),
                             mk_comb (field_sel fld, s_var)),
                      simp [ghost_reset_def]))) other_fields)

Theorem ghost_reset_values[local]:
  !s. ((ghost_reset s).log = []) /\ ((ghost_reset s).c_update = K ARB) /\
      ((ghost_reset s).exception = NoException) /\
      ((ghost_reset s).c_cycles = K 0w) /\
      ((ghost_reset s).c_instret = K 0w) /\
      ((ghost_reset s).c_minstret_written = K F)
Proof
  simp [ghost_reset_def]
QED

(* an update of another field commutes with ghost_reset ... *)
val ghost_reset_fupd =
  LIST_CONJ (map (fn fld =>
    GEN_ALL (prove (mk_eq (mk_comb (fupd_f fld, gr s_var),
                           gr (mk_comb (fupd_f fld, s_var))),
                    simp [ghost_reset_def]))) other_fields)

(* ... and one of a ghost field is lost *)
val ghost_reset_ghost_fupd =
  LIST_CONJ (map (fn fld =>
    GEN_ALL (prove (mk_eq (gr (mk_comb (fupd_f fld, s_var)), gr s_var),
                    simp [ghost_reset_def]))) ghost_fields)

Theorem ghost_reset_idem:
  !s. ghost_reset (ghost_reset s) = ghost_reset s
Proof
  simp [ghost_reset_def]
QED

Theorem ghost_eq_refl:
  !s. ghost_eq s s
Proof
  simp [ghost_eq_def]
QED

Theorem ghost_eq_sym:
  !s t. ghost_eq s t ==> ghost_eq t s
Proof
  simp [ghost_eq_def]
QED

Theorem ghost_eq_trans:
  !s t u. ghost_eq s t /\ ghost_eq t u ==> ghost_eq s u
Proof
  simp [ghost_eq_def]
QED

(* Ghost-equal states agree on every field but the six ghost fields ... *)
Theorem ghost_eq_fields =
  LIST_CONJ (map (fn fld =>
    GEN_ALL (prove (mk_imp (geq (s_var, t_var),
                            mk_eq (mk_comb (field_sel fld, s_var),
                                   mk_comb (field_sel fld, t_var))),
               rw [ghost_eq_def]
               \\ pop_assum (mp_tac o AP_TERM (field_sel fld))
               \\ simp [ghost_reset_fields]))) other_fields)

(* ... and an update of a ghost field gives a ghost-equal state *)
Theorem ghost_eq_ghost_fupd =
  LIST_CONJ (map (fn fld =>
    GEN_ALL (prove (geq (mk_comb (fupd_f fld, s_var), s_var),
                    simp [ghost_eq_def, ghost_reset_ghost_fupd])))
    ghost_fields)

(* ------------------------------------------------------------------------
   3. The functions that mention no ghost field commute with ghost_reset
      (generated: f_ghost)

     f x (ghost_reset s) = ghost_reset (f x s)                state
     f x (ghost_reset s) = (FST (f x s), ghost_reset (SND (f x s)))
                                                              value and state
     f x (ghost_reset s) = f x s                              value
   ------------------------------------------------------------------------ *)

Theorem word4_cases[local]:
  !i : word4.
    (i = 0w) \/ (i = 1w) \/ (i = 2w) \/ (i = 3w) \/ (i = 4w) \/ (i = 5w) \/
    (i = 6w) \/ (i = 7w) \/ (i = 8w) \/ (i = 9w) \/ (i = 10w) \/
    (i = 11w) \/ (i = 12w) \/ (i = 13w) \/ (i = 14w) \/ (i = 15w)
Proof
  BBLAST_TAC
QED

(* The cases of the first word4 variable of the goal: the index of the PMP
   entry in write_pmpaddr, whose case on it has a default case ARB *)
fun word4_cases_tac (g as (_, w)) =
  case List.filter (fn v => type_of v = ``:word4``) (free_vars w) of
    i :: _ => strip_assume_tac (SPEC i word4_cases) g
  | [] => raise ERR "word4_cases_tac" "no word4 variable"

(* a conditional under FST, SND and ghost_reset *)
val COND_RAND_FST = ISPEC ``FST : 'a # 'b -> 'a`` COND_RAND
val COND_RAND_SND = ISPEC ``SND : 'a # 'b -> 'b`` COND_RAND
val COND_RAND_GHOST = ISPEC ghost_reset_tm COND_RAND
val ghost_COND_UP = GSYM COND_RAND_GHOST

(* the application of f to its arguments and the state s, as in its
   definition *)
fun applied n s =
  let
    val th = def_of n
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

fun commute_goal n =
  let
    val (app, rty) = applied n s_var
    val (lapp, _) = applied n (gr s_var)
    val r = if rty = sty then gr app
            else if occurs rty then
              pairSyntax.mk_pair (pairSyntax.mk_fst app,
                                  gr (pairSyntax.mk_snd app))
            else app
    val g = mk_eq (lapp, r)
  in
    list_mk_forall (free_vars g, g)
  end

(* the rewrites of the generated proofs; ghost_COND_UP is left out where
   COND_RAND_GHOST is used, with which it loops *)
val base_nc =
  [pairTheory.UNCURRY, ghost_reset_fields, ghost_reset_fupd,
   ghost_reset_ghost_fupd, ghost_reset_idem, ghost_reset_values]
val base = ghost_COND_UP :: base_nc

local
  val lemmas = ref ([] : thm list)
  fun tacA def =
    rpt gen_tac
    \\ simp ([def] @ base @ !lemmas)
    \\ rpt (CASE_TAC \\ simp (base @ !lemmas))
  (* write_pmpaddr *)
  fun tacC def =
    rpt gen_tac \\ word4_cases_tac \\ simp ([def] @ base @ !lemmas)
  fun prove_one n =
    let
      val def = def_of n
      val th = prove (commute_goal n,
                      FIRST [tacA def \\ NO_TAC, tacC def \\ NO_TAC])
               handle e =>
                 (print ("riscv_refine: no ghost lemma for " ^ n ^ "\n");
                  raise e)
    in
      lemmas := th :: !lemmas;
      (n, save_thm (n ^ "_ghost", th))
    end
in
  val commute_thms = map prove_one ghost_free
end

fun commute_of n = Lib.assoc n commute_thms
val commute_lemmas = map snd commute_thms

val () =
  print ("riscv_refine: " ^ Int.toString (length commute_thms) ^
         " functions commute with ghost_reset\n")

(* The relational form of a commuting function, for the proofs below *)
fun rel_goal n =
  let
    val (aps, rty) = applied n s_var
    val (apt, _) = applied n t_var
    val c = if rty = sty then geq (aps, apt)
            else if occurs rty then
              mk_conj (mk_eq (pairSyntax.mk_fst aps, pairSyntax.mk_fst apt),
                       geq (pairSyntax.mk_snd aps, pairSyntax.mk_snd apt))
            else mk_eq (aps, apt)
    val g = mk_imp (geq (s_var, t_var), c)
  in
    list_mk_forall (free_vars g, g)
  end
fun rel_of n =
  prove (rel_goal n,
    rpt strip_tac \\ fs [ghost_eq_def]
    \\ metis_tac [commute_of n, pairTheory.FST, pairTheory.SND])

(* ------------------------------------------------------------------------
   4. The functions that mention a ghost field (by hand)

   Each changes only ghost fields, or gives ghost-equal results (and equal
   values) on ghost-equal states; the CSR reads give equal values except
   for a counter CSR.  The proofs also give, for the generated passes
   below, the form  ghost_reset (f x (ghost_reset s)) = ghost_reset (f x s).
   ------------------------------------------------------------------------ *)

Theorem write'Delta_reset[local]:
  !v s. ghost_reset (write'Delta v s) = ghost_reset s
Proof
  rw [write'Delta_def, ghost_reset_ghost_fupd]
QED

(* write'Delta and clear_logs change only c_update and log *)
Theorem write'Delta_ghost:
  !v s. ghost_eq (write'Delta v s) s
Proof
  simp [ghost_eq_def, write'Delta_reset]
QED

Theorem clear_logs_ghost:
  !s. ghost_eq (clear_logs () s) s
Proof
  rw [clear_logs_def, ghost_eq_ghost_fupd]
QED

(* incrInstret changes only c_instret *)
Theorem incrInstret_ghost:
  !b s. ghost_eq (incrInstret b s) s
Proof
  rw [incrInstret_def, ghost_eq_ghost_fupd, ghost_eq_refl]
QED

Theorem raise'exception_reset[local]:
  !e s. ghost_reset (SND (raise'exception e s)) = ghost_reset s
Proof
  rw [raise'exception_def, ghost_reset_ghost_fupd]
QED

Theorem raise'exception_FST[local]:
  !e s. FST (raise'exception e s) = ARB
Proof
  rw [raise'exception_def]
QED

(* raise'exception changes only the exception field *)
Theorem raise'exception_ghost:
  !e s. (FST (raise'exception e s) = ARB) /\
        ghost_eq (SND (raise'exception e s)) s
Proof
  simp [ghost_eq_def, raise'exception_reset, raise'exception_FST]
QED

(* A CSR read changes at most the exception (of an undefined CSR) ... *)
Theorem CSRMap_state:
  !c s. ghost_eq (SND (CSRMap c s)) s
Proof
  simp_tac std_ss [ghost_eq_def, CSRMap_def, literal_case_THM, COND_RAND_SND,
                   COND_RAND_GHOST, raise'exception_reset, COND_ID]
QED

(* ... and reads no ghost field but for the counter CSRs *)
Theorem CSRMap_value[local]:
  !c s. ~counter_csr c ==>
        (FST (CSRMap c (ghost_reset s)) = FST (CSRMap c s))
Proof
  rpt gen_tac
  \\ simp_tac (std_ss ++ listSimps.LIST_ss) [counter_csr_def]
  \\ strip_tac
  \\ asm_simp_tac std_ss
       ([CSRMap_def, literal_case_THM, COND_RAND_FST, raise'exception_FST] @
        base @ commute_lemmas)
QED

Theorem CSRMap_ghost:
  !c s t.
    ghost_eq s t ==>
    ghost_eq (SND (CSRMap c s)) (SND (CSRMap c t)) /\
    (~counter_csr c ==> (FST (CSRMap c s) = FST (CSRMap c t)))
Proof
  rw [ghost_eq_def, REWRITE_RULE [ghost_eq_def] CSRMap_state]
  \\ metis_tac [CSRMap_value]
QED

Theorem CSR_ghost:
  !c s t.
    ghost_eq s t ==>
    ghost_eq (SND (CSR c s)) (SND (CSR c t)) /\
    (~counter_csr c ==> (FST (CSR c s) = FST (CSR c t)))
Proof
  simp [CSR_def, CSRMap_ghost]
QED

(* A CSR write, also of a counter, changes the same fields of ghost-equal
   states in the same way *)
Theorem write'CSRMap_reset[local]:
  !v c s. ghost_reset (write'CSRMap (v, c) (ghost_reset s)) =
          ghost_reset (write'CSRMap (v, c) s)
Proof
  rpt gen_tac
  \\ simp_tac std_ss
       ([write'CSRMap_def, literal_case_THM, COND_RAND_GHOST, LET_THM,
         raise'exception_reset] @ base_nc @ commute_lemmas)
QED

Theorem write'CSRMap_ghost:
  !v c s t.
    ghost_eq s t ==> ghost_eq (write'CSRMap (v, c) s) (write'CSRMap (v, c) t)
Proof
  rw [ghost_eq_def] \\ metis_tac [write'CSRMap_reset]
QED

Theorem write'CSR_ghost:
  !v c s t.
    ghost_eq s t ==> ghost_eq (write'CSR (v, c) s) (write'CSR (v, c) t)
Proof
  simp [write'CSR_def, write'CSRMap_ghost]
QED

(* writeCSR is write'CSR followed by the logging of the new value, which it
   reads back: up to the ghost fields, write'CSRMap *)
Theorem writeCSR_write'CSRMap:
  !c v s. ghost_eq (writeCSR (c, v) s) (write'CSRMap (v, c) s)
Proof
  simp_tac std_ss [ghost_eq_def, writeCSR_def, LET_THM, pairTheory.UNCURRY,
                   write'CSR_def, CSR_def]
  \\ simp [write'Delta_reset, REWRITE_RULE [ghost_eq_def] CSRMap_state]
QED

Theorem writeCSR_ghost:
  !c v s t.
    ghost_eq s t ==> ghost_eq (writeCSR (c, v) s) (writeCSR (c, v) t)
Proof
  metis_tac [writeCSR_write'CSRMap, write'CSRMap_ghost, ghost_eq_trans,
             ghost_eq_sym]
QED

(* The CSR instructions' access to a CSR other than a counter *)
Theorem accessCSR_ghost:
  !op rd f src c s t.
    ~counter_csr c /\ ghost_eq s t ==>
    ghost_eq (accessCSR (op, rd, f, src, c) s)
             (accessCSR (op, rd, f, src, c) t)
Proof
  rpt strip_tac
  \\ imp_res_tac (rel_of "checkCSROp")
  \\ `!c'. ghost_eq (SND (CSRMap c' s)) (SND (CSRMap c' t))`
     by metis_tac [CSRMap_ghost]
  \\ `!c'. ~counter_csr c' ==> (FST (CSRMap c' s) = FST (CSRMap c' t))`
     by metis_tac [CSRMap_ghost]
  \\ `!c'. MCSR (SND (CSRMap c' s)) = MCSR (SND (CSRMap c' t))`
     by (gen_tac \\ irule (rel_of "MCSR") \\ asm_simp_tac std_ss [])
  \\ `~counter_csr 836w` by simp [counter_csr_def]
  \\ simp_tac std_ss [accessCSR_def, LET_THM, pairTheory.UNCURRY, CSR_def]
  \\ asm_simp_tac std_ss []
  \\ IF_CASES_TAC
  \\ asm_simp_tac std_ss [rel_of "signalException"]
  \\ irule (rel_of "write'GPR")
  \\ IF_CASES_TAC
  \\ asm_simp_tac std_ss [writeCSR_ghost]
QED

(* An FPR write logs the value in c_update *)
Theorem writeFPRS_reset[local]:
  !rd v s. ghost_reset (writeFPRS (rd, v) (ghost_reset s)) =
           ghost_reset (writeFPRS (rd, v) s)
Proof
  simp_tac std_ss [writeFPRS_def, LET_THM, pairTheory.UNCURRY]
  \\ simp ([write'Delta_reset] @ base @ commute_lemmas)
QED

Theorem writeFPRD_reset[local]:
  !rd v s. ghost_reset (writeFPRD (rd, v) (ghost_reset s)) =
           ghost_reset (writeFPRD (rd, v) s)
Proof
  simp_tac std_ss [writeFPRD_def, LET_THM, pairTheory.UNCURRY]
  \\ simp ([write'Delta_reset] @ base @ commute_lemmas)
QED

Theorem writeFPRS_ghost:
  !rd v s t.
    ghost_eq s t ==> ghost_eq (writeFPRS (rd, v) s) (writeFPRS (rd, v) t)
Proof
  rw [ghost_eq_def] \\ metis_tac [writeFPRS_reset]
QED

Theorem writeFPRD_ghost:
  !rd v s t.
    ghost_eq s t ==> ghost_eq (writeFPRD (rd, v) s) (writeFPRD (rd, v) t)
Proof
  rw [ghost_eq_def] \\ metis_tac [writeFPRD_reset]
QED

(* The fetch: the records of the instruction that the model's Fetch writes
   collapse into one (Delta_write'Delta, write'Delta_write'Delta) *)
val fetch_ss =
  [Delta_write'Delta, write'Delta_write'Delta, LET_THM, pairTheory.UNCURRY,
   TypeBase.case_def_of ``:rawInstType``,
   TypeBase.case_def_of ``:TransResult``,
   write'Delta_reset, ghost_reset_idem, ghost_reset_fields,
   ghost_reset_values, commute_of "PC", commute_of "haveRVC",
   commute_of "fetchAddr", commute_of "rawReadInst"]

Theorem Fetch_reset[local]:
  !s. (FST (riscv$Fetch () (ghost_reset s)) = FST (riscv$Fetch () s)) /\
      (ghost_reset (SND (riscv$Fetch () (ghost_reset s))) =
       ghost_reset (SND (riscv$Fetch () s)))
Proof
  gen_tac
  \\ simp_tac std_ss ([riscvTheory.Fetch_def] @ fetch_ss)
  \\ rpt (CASE_TAC \\ asm_simp_tac std_ss fetch_ss)
QED

Theorem Fetch_ghost:
  !s t. ghost_eq s t ==>
        (FST (riscv$Fetch () s) = FST (riscv$Fetch () t)) /\
        ghost_eq (SND (riscv$Fetch () s)) (SND (riscv$Fetch () t))
Proof
  rw [ghost_eq_def] \\ metis_tac [Fetch_reset]
QED

(* ------------------------------------------------------------------------
   5. The other functions that mention a ghost field (generated): the F and
      D instructions that write an FPR, the trap entry and the CSR
      instructions
   ------------------------------------------------------------------------ *)

fun cong_goal n =
  let
    val (app, rty) = applied n s_var
    val (lapp, _) = applied n (gr s_var)
    val _ = rty = sty orelse raise ERR "cong_goal" n
    val g = mk_eq (gr lapp, gr app)
  in
    list_mk_forall (free_vars g, g)
  end

val cong_lemmas =
  [writeFPRS_reset, writeFPRD_reset, raise'exception_reset,
   raise'exception_FST]

(* the equation, and the relational form that is saved *)
fun cong_thm n =
  let
    val eq =
      prove (cong_goal n,
        rpt gen_tac
        \\ simp ([def_of n] @ base @ commute_lemmas @ cong_lemmas)
        \\ rpt (CASE_TAC \\ simp (base @ commute_lemmas @ cong_lemmas)))
      handle e =>
        (print ("riscv_refine: no ghost lemma for " ^ n ^ "\n"); raise e)
    val rel =
      prove (rel_goal n,
        rpt strip_tac \\ fs [ghost_eq_def] \\ metis_tac [eq])
  in
    (n, eq, save_thm (n ^ "_ghost", rel))
  end

val fp_thms = map cong_thm fp_writers
val (_, _, takeTrap_ghost) = cong_thm "takeTrap"

Theorem accessCSR_reset[local]:
  !op rd f src c s.
    ~counter_csr c ==>
    (ghost_reset (accessCSR (op, rd, f, src, c) (ghost_reset s)) =
     ghost_reset (accessCSR (op, rd, f, src, c) s))
Proof
  rpt strip_tac
  \\ irule (REWRITE_RULE [ghost_eq_def] accessCSR_ghost)
  \\ simp [ghost_reset_idem]
QED

(* the CSR instructions, on a CSR other than a counter *)
val csr_thms =
  map (fn n =>
         let
           val (app, _) = applied n s_var
           val f = rator app
           val csr = List.last (pairSyntax.strip_pair (rand f))
           val not_counter = mk_neg ``counter_csr ^csr``
           fun closed g = list_mk_forall (free_vars g, g)
           val eq =
             prove (closed (mk_imp (not_counter,
                                    mk_eq (gr (mk_comb (f, gr s_var)),
                                           gr app))),
               rpt strip_tac
               \\ asm_simp_tac std_ss
                    [def_of n, accessCSR_reset, commute_of "GPR"])
           val rel =
             prove (closed (mk_imp (mk_conj (not_counter, geq (s_var, t_var)),
                                    geq (app, mk_comb (f, t_var)))),
               rpt strip_tac \\ fs [ghost_eq_def] \\ metis_tac [eq])
         in
           (n, eq, save_thm (n ^ "_ghost", rel))
         end) csr_insts

(* ------------------------------------------------------------------------
   6. Run
   ------------------------------------------------------------------------ *)

fun pair_cases_tac (g as (_, w)) =
  let
    val vs = List.filter (fn v => can pairSyntax.dest_prod (type_of v))
                         (free_vars w)
  in
    MAP_EVERY (fn v => PairCases_on `^v`) vs g
  end

Theorem Run_reset[local]:
  !i s. ~reads_counter i ==>
        (ghost_reset (Run i (ghost_reset s)) = ghost_reset (Run i s))
Proof
  Cases_on `i`
  \\ simp_tac (srw_ss()) [Run_def]
  \\ rpt CASE_TAC
  \\ pair_cases_tac
  \\ simp_tac (srw_ss()) [reads_counter_def]
  \\ rpt strip_tac
  \\ asm_simp_tac std_ss
       ([ghost_reset_idem] @ commute_lemmas @ map #2 fp_thms @
        map #2 csr_thms)
QED

(* An instruction that reads no counter CSR runs from ghost-equal states to
   ghost-equal states *)
Theorem Run_ghost:
  !i s t. ~reads_counter i /\ ghost_eq s t ==> ghost_eq (Run i s) (Run i t)
Proof
  rw [ghost_eq_def] \\ metis_tac [Run_reset]
QED

(* ------------------------------------------------------------------------
   7. An exception, once raised, stays

   raise'exception sets the exception field only if it holds NoException,
   and no other function writes it.  So every function reachable from Run
   commutes with an update of the exception field to a value other than
   NoException (generated, local), and Run keeps a raised exception.
   ------------------------------------------------------------------------ *)

local
  val exc_ty = ``:exception``
  val e_var = mk_var ("e", exc_ty)
  fun with_e st =
    mk_comb (mk_comb (field_upd "exception",
                      combinSyntax.mk_K_1 (e_var, exc_ty)), st)
  val COND_UP_E = Q.prove (
    `!b x y e. (if b then x with exception := e else y with exception := e) =
               (if b then x else y) with exception := e`, rw [])
  val COND_RAND_E = GSYM COND_UP_E
  fun goal n =
    let
      val (app, rty) = applied n s_var
      val (lapp, _) = applied n (with_e s_var)
      val r = if rty = sty then with_e app
              else if occurs rty then
                pairSyntax.mk_pair (pairSyntax.mk_fst app,
                                    with_e (pairSyntax.mk_snd app))
              else app
      val g = mk_imp (mk_neg (mk_eq (e_var, ``NoException``)),
                      mk_eq (lapp, r))
    in
      list_mk_forall (free_vars g, g)
    end
  val raise'exception_exc = Q.prove (
    `!e' s e.
       e <> NoException ==>
       (raise'exception e' (s with exception := e) =
        (FST (raise'exception e' s : 'a # riscv_state),
         SND (raise'exception e' s : 'a # riscv_state) with exception := e))`,
    rw [raise'exception_def])
  val lemmas = ref [raise'exception_exc]
  val rwts = [COND_UP_E, pairTheory.UNCURRY, LET_THM]
  fun tacA def =
    rpt gen_tac \\ strip_tac
    \\ asm_simp_tac (srw_ss()) ([def] @ rwts @ !lemmas)
    \\ rpt (CASE_TAC \\ asm_simp_tac (srw_ss()) (rwts @ !lemmas))
  (* write_pmpaddr *)
  fun tacC def =
    rpt gen_tac \\ strip_tac \\ word4_cases_tac
    \\ asm_simp_tac (srw_ss()) ([def] @ rwts @ !lemmas)
  (* the CSR maps: a case on a 12-bit word, as nested conditionals *)
  fun tacL def =
    rpt gen_tac \\ strip_tac
    \\ simp_tac std_ss [pairTheory.PAIR_FST_SND_EQ]
    \\ asm_simp_tac (srw_ss())
         ([def, literal_case_THM, COND_RAND_FST, COND_RAND_SND, COND_RAND_E,
           LET_THM, pairTheory.UNCURRY] @ !lemmas)
  fun prove_one n =
    let
      val tacs = if Lib.mem n ["CSRMap", "write'CSRMap"] then [tacL]
                 else [tacA, tacC]
      val th =
        prove (goal n, FIRST (map (fn t => t (def_of n) \\ NO_TAC) tacs))
        handle e =>
          (print ("riscv_refine: no exception lemma for " ^ n ^ "\n");
           raise e)
    in
      lemmas := th :: !lemmas
    end
  val run_reach = reach_from ["Run"]
  val run_fns =
    List.filter (fn n => Lib.mem n run_reach andalso
                         n <> "Run" andalso n <> "raise'exception") order
  val () = List.app prove_one run_fns
in
  val exception_lemmas = !lemmas
end

Theorem Run_exception_upd[local]:
  !i s e. e <> NoException ==>
          (Run i (s with exception := e) = Run i s with exception := e)
Proof
  Cases_on `i`
  \\ simp_tac (srw_ss()) [Run_def]
  \\ rpt CASE_TAC
  \\ pair_cases_tac
  \\ rpt strip_tac
  \\ asm_simp_tac std_ss exception_lemmas
QED

Theorem Run_exception:
  !i s. s.exception <> NoException ==> ((Run i s).exception = s.exception)
Proof
  rpt strip_tac
  \\ qspecl_then [`i`, `s`, `s.exception`] mp_tac Run_exception_upd
  \\ asm_rewrite_tac [riscv_state_fupdselfid]
  \\ disch_then SUBST1_TAC
  \\ simp_tac (srw_ss()) []
QED

(* ------------------------------------------------------------------------
   8. The two fetches
   ------------------------------------------------------------------------ *)

Theorem rawReadInst_exception[local]:
  !a s. (SND (rawReadInst a s)).exception = s.exception
Proof
  rpt gen_tac
  \\ qspecl_then [`a`, `s`] strip_assume_tac rawReadInst_state
  \\ asm_simp_tac (srw_ss()) []
QED

(* Where the step library's Fetch succeeds (raises no exception), the
   model's Fetch returns its instruction bits and state, but for the record
   of the instruction *)
Theorem Fetch_step_spec:
  !s w s1. (riscv_step$Fetch s = (w, s1)) /\ (s.exception = NoException) /\
           (s1.exception = NoException) ==>
           ?u. riscv$Fetch () s = (F_Result w, s1 with c_update := u)
Proof
  rpt gen_tac
  \\ simp_tac std_ss
       ([riscv_stepTheory.Fetch_def, riscvTheory.Fetch_def] @ fetch_ss)
  \\ rpt (CASE_TAC \\ asm_simp_tac std_ss fetch_ss)
  \\ rpt strip_tac
  \\ gvs [raise'exception_def, write'Delta_def, rawReadInst_exception]
  \\ metis_tac []
QED

(* The step library's Fetch keeps a raised exception *)
Theorem Fetch_step_exception:
  !s w s1. (riscv_step$Fetch s = (w, s1)) /\ (s1.exception = NoException) ==>
           (s.exception = NoException)
Proof
  rpt gen_tac
  \\ simp_tac std_ss ([riscv_stepTheory.Fetch_def] @ fetch_ss)
  \\ rpt (CASE_TAC \\ asm_simp_tac std_ss fetch_ss)
  \\ rpt strip_tac
  \\ CCONTR_TAC
  \\ gvs [raise'exception_def, rawReadInst_exception]
QED

(* So a step of NextRISCV starts with no exception, and its fetch raises
   none *)
Theorem NextRISCV_exception:
  !s s'. (NextRISCV s = SOME s') ==>
         (s.exception = NoException) /\
         ((SND (riscv_step$Fetch s)).exception = NoException)
Proof
  rpt gen_tac
  \\ Cases_on `riscv_step$Fetch s`
  \\ simp_tac std_ss [riscv_stepTheory.NextRISCV_def, LET_THM]
  \\ asm_simp_tac std_ss [pairTheory.UNCURRY_DEF]
  \\ strip_tac
  \\ `r.exception = NoException` by metis_tac [Run_exception]
  \\ metis_tac [Fetch_step_exception]
QED

(* ------------------------------------------------------------------------
   9. Next and NextRISCV
   ------------------------------------------------------------------------ *)

(* The parts of Next around the instruction change only ghost fields *)
Theorem cycle_step_ghost:
  !t. ghost_eq (cycle_step t) t
Proof
  rw [cycle_step_def, ghost_eq_ghost_fupd, ghost_eq_refl]
QED

Theorem next_pre_ghost:
  !s. ghost_eq (next_pre s) s
Proof
  simp [next_pre_def, ghost_eq_def, ghost_reset_ghost_fupd]
QED

Theorem exec_state_ghost:
  !s. ghost_eq (exec_state s) (SND (riscv$Fetch () s))
Proof
  simp [exec_state_def, Fetch_next_pre, ghost_eq_def, ghost_reset_ghost_fupd]
QED

Theorem fetch_F_Result[local]:
  !w rvc. (fetch_inst (F_Result w) rvc = DecodeAny rvc w) /\
          (fetch_bits (F_Result w) = rawInstBits w)
Proof
  Cases
  \\ simp [fetch_inst_def, fetch_bits_def, riscv_stepTheory.DecodeAny_def,
           riscv_stepTheory.rawInstBits_def]
QED

Theorem incrInstret_values[local]:
  !b s. (PC (incrInstret b s) = PC s) /\ (Skip (incrInstret b s) = Skip s)
Proof
  rw [incrInstret_def, PC_def, Skip_def]
QED

Theorem write'NextFetch_values[local]:
  !v s. (PC (write'NextFetch v s) = PC s) /\
        (curPrivilege () (write'NextFetch v s) = curPrivilege () s) /\
        (!ec p. excDest (ec, p) (write'NextFetch v s) = excDest (ec, p) s)
Proof
  simp [write'NextFetch_def, PC_def, curPrivilege_def, excDest_def, MCSR_def]
QED

val rel_PC = rel_of "PC"
val rel_Skip = rel_of "Skip"
val rel_write'PC = rel_of "write'PC"
val rel_write'NextFetch = rel_of "write'NextFetch"
val rel_mret = rel_of "mret"
val rel_sret = rel_of "sret"
val rel_curPrivilege = rel_of "curPrivilege"
val rel_excDest = rel_of "excDest"
val rel_checkInterrupts = rel_of "checkInterrupts"
val rel_haveRVC = rel_of "haveRVC"

(* The dispatch on NextFetch after the instruction (next_post, with or
   without counting the instruction) is a congruence for ghost_eq *)
Theorem next_post_ghost:
  !b v r r'.
    ghost_eq r r' ==> ghost_eq (next_post b (v, r)) (next_post b (v, r'))
Proof
  rpt strip_tac
  \\ `ghost_eq (incrInstret b r) (incrInstret b r')`
     by metis_tac [incrInstret_ghost, ghost_eq_trans, ghost_eq_sym]
  \\ `ghost_eq (write'NextFetch NONE r) (write'NextFetch NONE r')`
     by metis_tac [rel_write'NextFetch]
  \\ `ghost_eq (write'NextFetch NONE (incrInstret b r))
               (write'NextFetch NONE (incrInstret b r'))`
     by metis_tac [rel_write'NextFetch]
  \\ `r'.c_NextFetch r'.procID = r.c_NextFetch r.procID`
     by metis_tac [ghost_eq_fields]
  \\ `(PC (incrInstret b r) = PC (incrInstret b r')) /\
      (Skip (incrInstret b r) = Skip (incrInstret b r'))`
     by metis_tac [rel_PC, rel_Skip]
  \\ `(PC (write'NextFetch NONE r) = PC (write'NextFetch NONE r')) /\
      (curPrivilege () (write'NextFetch NONE r) =
       curPrivilege () (write'NextFetch NONE r'))`
     by metis_tac [rel_PC, rel_curPrivilege]
  \\ `!ec p. excDest (ec, p) (write'NextFetch NONE r) =
             excDest (ec, p) (write'NextFetch NONE r')`
     by metis_tac [rel_excDest]
  \\ simp_tac std_ss [next_post_def]
  \\ asm_rewrite_tac []
  \\ Cases_on `r.c_NextFetch r.procID`
  \\ simp_tac (srw_ss()) []
  >- (irule rel_write'PC \\ first_assum ACCEPT_TAC)
  \\ Cases_on `x` \\ simp_tac (srw_ss()) []
  >- (irule rel_write'PC \\ first_assum ACCEPT_TAC)
  >- (irule rel_mret \\ first_assum ACCEPT_TAC)
  >- (irule rel_sret \\ first_assum ACCEPT_TAC)
  \\ irule takeTrap_ghost \\ first_assum ACCEPT_TAC
QED

(* A step of NextRISCV is, up to the ghost fields, the dispatch of Next
   after the instruction that its fetch read *)
Theorem NextRISCV_next_post:
  !t t'. (NextRISCV t = SOME t') ==>
     ?w t1. (riscv_step$Fetch t = (w, t1)) /\ (t.exception = NoException) /\
            (t1.exception = NoException) /\
            !b. ghost_eq
                  (next_post b
                     (rawInstBits w, Run (DecodeAny (haveRVC () t) w) t1))
                  t'
Proof
  rpt strip_tac
  \\ Cases_on `riscv_step$Fetch t`
  \\ rename1 `riscv_step$Fetch t = (w, t1)`
  \\ imp_res_tac NextRISCV_exception
  \\ qexistsl_tac [`w`, `t1`]
  \\ rfs []
  \\ qpat_x_assum `NextRISCV t = SOME t'` mp_tac
  \\ simp_tac std_ss [riscv_stepTheory.NextRISCV_def, LET_THM]
  \\ asm_simp_tac std_ss [pairTheory.UNCURRY_DEF]
  \\ qabbrev_tac `r = Run (DecodeAny (haveRVC () t) w) t1`
  \\ simp_tac std_ss [next_post_def, riscvTheory.NextFetch_def]
  \\ Cases_on `r.c_NextFetch r.procID`
  \\ simp_tac (srw_ss()) [riscv_stepTheory.update_pc_def]
  >- (rpt strip_tac
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ simp_tac std_ss [incrInstret_values]
      \\ irule rel_write'PC
      \\ simp [incrInstret_ghost])
  \\ Cases_on `x`
  \\ simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  >- (irule rel_write'PC \\ irule rel_write'NextFetch
      \\ simp [incrInstret_ghost])
  >- (irule rel_mret \\ irule rel_write'NextFetch
      \\ simp [incrInstret_ghost])
  \\ simp [write'NextFetch_values, ghost_eq_refl]
QED

(* The refinement: from a state t that takes no interrupt and whose fetched
   instruction reads no counter CSR, a NextRISCV step to t' is a Next step
   up to the ghost fields, also from any state s ghost-equal to t *)
Theorem Next_NextRISCV_ghost:
  !s t t'. ghost_eq s t /\ (checkInterrupts () t = NONE) /\
           (!w t1. (riscv_step$Fetch t = (w, t1)) ==>
                   ~reads_counter (DecodeAny (haveRVC () t) w)) /\
           (NextRISCV t = SOME t') ==>
           ghost_eq (Next s) t'
Proof
  rpt strip_tac
  \\ drule NextRISCV_next_post
  \\ strip_tac
  (* the model's fetch at t reads what the step library's read *)
  \\ drule_all Fetch_step_spec
  \\ strip_tac
  \\ `~reads_counter (DecodeAny (haveRVC () t) w)`
     by (qpat_x_assum `!w t1. _` (qspecl_then [`w`, `t1`] mp_tac)
         \\ asm_rewrite_tac [])
  (* and so does the one at s, which takes no interrupt either *)
  \\ `checkInterrupts () s = NONE` by metis_tac [rel_checkInterrupts]
  \\ `haveRVC () s = haveRVC () t` by metis_tac [rel_haveRVC]
  \\ qspecl_then [`s`, `t`] mp_tac Fetch_ghost
  \\ asm_simp_tac std_ss []
  \\ strip_tac
  \\ `ghost_eq (exec_state s) t1`
     by (irule ghost_eq_trans
         \\ qexists_tac `SND (riscv$Fetch () s)`
         \\ asm_simp_tac std_ss [exec_state_ghost]
         \\ irule ghost_eq_trans
         \\ qexists_tac `t1 with c_update := u`
         \\ asm_simp_tac std_ss [ghost_eq_ghost_fupd])
  (* the instruction *)
  \\ qabbrev_tac `i = DecodeAny (haveRVC () t) w`
  \\ `ghost_eq (Run i (exec_state s)) (Run i t1)`
     by (irule Run_ghost \\ asm_simp_tac std_ss [])
  \\ `Next s =
      cycle_step
        (next_post (~word_bit 2 (s.c_MCSR s.procID).mcountinhibit)
           (rawInstBits w, Run i (exec_state s)))`
     by (qunabbrev_tac `i`
         \\ asm_simp_tac (srw_ss())
              [Next_split, fetchAndExecute_next_pre, fetch_F_Result])
  \\ pop_assum SUBST1_TAC
  (* the dispatch and the cycle count *)
  \\ irule ghost_eq_trans
  \\ qexists_tac `next_post (~word_bit 2 (s.c_MCSR s.procID).mcountinhibit)
                    (rawInstBits w, Run i (exec_state s))`
  \\ conj_tac
  >- simp_tac std_ss [cycle_step_ghost]
  \\ irule ghost_eq_trans
  \\ qexists_tac `next_post (~word_bit 2 (s.c_MCSR s.procID).mcountinhibit)
                    (rawInstBits w, Run i t1)`
  \\ conj_tac
  >- (irule next_post_ghost \\ first_assum ACCEPT_TAC)
  \\ asm_simp_tac std_ss []
QED

(* Next itself, from two ghost-equal states whose step runs no instruction
   that reads a counter CSR, steps to ghost-equal states *)
Theorem Next_ghost:
  !s t. ghost_eq s t /\ (!i. (step_inst s = SOME i) ==> ~reads_counter i) ==>
        ghost_eq (Next s) (Next t)
Proof
  rpt strip_tac
  \\ `checkInterrupts () t = checkInterrupts () s`
     by metis_tac [rel_checkInterrupts]
  \\ `(t.c_MCSR t.procID = s.c_MCSR s.procID) /\ (PC t = PC s)`
     by metis_tac [ghost_eq_fields, rel_PC, ghost_eq_sym]
  \\ `!a b. ghost_eq a b ==> ghost_eq (cycle_step a) (cycle_step b)`
     by metis_tac [cycle_step_ghost, ghost_eq_trans, ghost_eq_sym]
  \\ pop_assum (fn th => simp_tac std_ss [Next_split] \\ irule th)
  \\ asm_rewrite_tac []
  \\ Cases_on `checkInterrupts () s`
  >- (simp_tac (srw_ss()) [fetchAndExecute_next_pre]
      \\ qspecl_then [`s`, `t`] mp_tac Fetch_ghost
      \\ asm_simp_tac std_ss []
      \\ strip_tac
      \\ `haveRVC () t = haveRVC () s` by metis_tac [rel_haveRVC]
      \\ pop_assum SUBST1_TAC
      \\ irule next_post_ghost
      \\ irule Run_ghost
      \\ conj_tac
      >- (first_x_assum irule \\ asm_simp_tac std_ss [step_inst_def])
      \\ metis_tac [exec_state_ghost, ghost_eq_trans, ghost_eq_sym])
  \\ PairCases_on `x`
  \\ simp_tac (srw_ss()) []
  \\ irule takeTrap_ghost
  \\ metis_tac [next_pre_ghost, ghost_eq_trans, ghost_eq_sym]
QED

(* Every function reachable from Next has its lemma: f_ghost for those
   that mention no ghost field (section 3), and for the others but Delta,
   whose value is the ghost field c_update, and fetchAndExecute, whose
   instruction depends on the fetch (it is covered through Next_ghost and
   Next_NextRISCV_ghost) *)
val () =
  let
    val covered =
      map fst commute_thms @ map #1 fp_thms @ map #1 csr_thms @
      ["write'Delta", "clear_logs", "incrInstret", "raise'exception",
       "CSRMap", "CSR", "write'CSRMap", "write'CSR", "writeCSR", "accessCSR",
       "writeFPRS", "writeFPRD", "Fetch", "takeTrap", "Run", "Next"]
  in
    set_check "the functions with a ghost lemma" covered
      (Lib.set_diff state_fns ["Delta", "fetchAndExecute"])
  end
