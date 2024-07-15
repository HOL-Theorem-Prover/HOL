(* ------------------------------------------------------------------------ *)
(*  Support running ARM model with a Patricia tree program memory           *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["arm_decoderTheory", "armTheory", "wordsLib",
            "patriciaTheory", "parmonadsyntax"];
*)

open HolKernel boolLib bossLib Parse;

open patriciaTheory arm_coretypesTheory arm_astTheory arm_seq_monadTheory
     arm_decoderTheory arm_opsemTheory armTheory;

val _ = new_theory "arm_eval";

(* ------------------------------------------------------------------------ *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

infix \\ << >>

val op \\ = op THEN;

val _ = temp_overload_on (parmonadsyntax.monad_bind, ``seqT``);
val _ = temp_overload_on (parmonadsyntax.monad_par,  ``parT``);
val _ = temp_overload_on ("return", ``constT``);

(* ------------------------------------------------------------------------ *)

val ptree_read_word_def = Define`
  ptree_read_word (prog:word8 ptree) (a:word32) : word32 M =
  let pc = w2n a in
   (case prog ' pc
    of SOME b1 =>
       (case prog ' (pc + 1)
        of SOME b2 =>
           (case prog ' (pc + 2)
            of SOME b3 =>
               (case prog ' (pc + 3)
                of SOME b4 => constT (word32 [b1; b2; b3; b4])
                 | NONE => errorT "couldn't fetch an instruction")
             | NONE => errorT "couldn't fetch an instruction")
         | NONE => errorT "couldn't fetch an instruction")
     | NONE => errorT "couldn't fetch an instruction")`;

val ptree_read_halfword_def = Define`
  ptree_read_halfword (prog:word8 ptree) (a:word32) : word16 M =
  let pc = w2n a in
    case prog ' pc
    of SOME b1 =>
       (case prog ' (pc + 1)
        of SOME b2 => constT (word16 [b1; b2])
         | NONE => errorT "couldn't fetch an instruction")
     | NONE => errorT "couldn't fetch an instruction"`;

val ptree_arm_next_def = zDefine
  `ptree_arm_next ii (x:string # Encoding # word4 # ARMinstruction)
     (pc:word32) (cycle:num) : unit M =
   arm_instr ii (SND x)`;

val attempt_def = Define`
  attempt c f g =
  \s:arm_state.
      case f s
      of Error e => ValueState (c, e) s
       | ValueState v s' => g v s'`;

val ptree_arm_loop_def = Define`
  ptree_arm_loop ii cycle prog t : (num # string) M =
    if t = 0 then
      constT (cycle, "finished")
    else
      attempt cycle
        (fetch_instruction ii (ptree_read_word prog) (ptree_read_halfword prog))
        (\x.
          read_pc ii >>=
          (\pc:word32.
              ptree_arm_next ii x pc cycle >>=
              (\u:unit.
                 ptree_arm_loop ii (cycle + 1) prog (t - 1))))`;

val ptree_arm_run_def = Define`
  ptree_arm_run prog state t =
    case ptree_arm_loop <| proc := 0 |> 0 prog t state
    of Error e => (e, NONE)
     | ValueState (c,v) s =>
          ("at cycle " ++ num_to_dec_string c ++ ": " ++ v, SOME s)`;

(* ------------------------------------------------------------------------ *)

val proc_def = zDefine `proc (n:num) f = \(i,x). if i = n then f x else ARB`;

val mk_arm_state_def = Define`
  mk_arm_state arch regs psrs md mem =
    <| registers := proc 0 regs;
       psrs := proc 0 psrs;
       event_register := (K T);
       interrupt_wait := (K F);
       memory := (\a. case patricia$PEEK mem (w2n a)
                        of SOME d => d
                         | NONE => md);
       accesses := [];
       information := <| arch := arch;
                         unaligned_support := T;
                         extensions := {} |>;
       coprocessors updated_by
         (Coprocessors_state_fupd
            (cp15_fupd (CP15reg_SCTLR_fupd
              (\sctlr. sctlr with <| V := F; A := T; U := F;
                                     IE := T; TE := F; NMFI := T;
                                     EE := T; VE := F |>)) o
             cp14_fupd (CP14reg_TEEHBR_fupd (K 0xF0000000w))));
       monitors := <| ClearExclusiveByAddress := (K (constE ())) |> |>`;

(* ------------------------------------------------------------------------ *)

val registers_def = Define`
   registers r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
             r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
             r26 r27 r28 r29 r30 r31 (r32:word32) =
   \name.
      RName_CASE
         name r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
              r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
              r26 r27 r28 r29 r30 r31 r32`

val psrs_def = Define`
   psrs r0 r1 r2 r3 r4 r5 (r6:ARMpsr) =
   \name. PSRName_CASE name r0 r1 r2 r3 r4 r5 r6`

(* ------------------------------------------------------------------------ *)

local
  val tm1 = ``((n:num,r:RName) =+ d:word32)``

  val tm2 =
    ``proc n
        (registers r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
                   r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
                   r26 r27 r28 r29 r30 r31 r32)``

  fun reg n = mk_var ("r" ^ Int.toString n, ``:word32``)

  fun reg_update (n,name) =
        mk_eq (mk_comb (Term.subst [``r:RName`` |-> name] tm1, tm2),
               Term.subst [reg n  |-> ``d:word32``] tm2)

  val thm = list_mk_conj (map reg_update (Lib.zip (List.tabulate(33,I))
           [``RName_0usr ``, ``RName_1usr ``, ``RName_2usr ``, ``RName_3usr``,
            ``RName_4usr ``, ``RName_5usr ``, ``RName_6usr ``, ``RName_7usr``,
            ``RName_8usr ``, ``RName_8fiq ``, ``RName_9usr ``, ``RName_9fiq``,
            ``RName_10usr``, ``RName_10fiq``, ``RName_11usr``, ``RName_11fiq``,
            ``RName_12usr``, ``RName_12fiq``,
            ``RName_SPusr``, ``RName_SPfiq``, ``RName_SPirq``, ``RName_SPsvc``,
            ``RName_SPabt``, ``RName_SPund``, ``RName_SPmon``,
            ``RName_LRusr``, ``RName_LRfiq``, ``RName_LRirq``, ``RName_LRsvc``,
            ``RName_LRabt``, ``RName_LRund``, ``RName_LRmon``, ``RName_PC``]))

  val register_update = Tactical.prove(thm,
    SRW_TAC [] [combinTheory.UPDATE_def, FUN_EQ_THM, registers_def, proc_def]
      \\ Cases_on `x` \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [])
in
  val register_update = save_thm("register_update", GEN_ALL register_update)
end

local
  val tm1 = ``((n:num,p:PSRName) =+ d:ARMpsr)``
  val tm2 = ``proc n (psrs r0 r1 r2 r3 r4 r5 r6)``;

  fun psr n = mk_var ("r" ^ Int.toString n, ``:ARMpsr``)

  fun psr_update (n,name) =
        mk_eq (mk_comb (Term.subst [``p:PSRName`` |-> name] tm1, tm2),
               Term.subst [psr n  |-> ``d:ARMpsr``] tm2)

  val thm = list_mk_conj (map psr_update (Lib.zip (List.tabulate(7,I))
           [``CPSR ``, ``SPSR_fiq ``, ``SPSR_irq ``, ``SPSR_svc``,
            ``SPSR_mon``, ``SPSR_abt``, ``SPSR_und``]))

  val psr_update = Tactical.prove(thm,
    SRW_TAC [] [combinTheory.UPDATE_def, FUN_EQ_THM, psrs_def, proc_def]
      \\ Cases_on `x` \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [])
in
  val psr_update = save_thm("psr_update", GEN_ALL psr_update)
end

val proc = Q.store_thm("proc", `proc n f (n,x) = f x`, SRW_TAC [] [proc_def])

val _ = computeLib.add_persistent_funs
  ["combin.o_THM", "proc", "register_update", "psr_update"]

(* ------------------------------------------------------------------------ *)

val _ = export_theory ()
