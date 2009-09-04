(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Top-level: fetch and run instructions                                *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["arm_decoderTheory", "arm_opsemTheory", "pred_setLib", "wordsLib",
            "parmonadsyntax"];
*)

open HolKernel boolLib bossLib Parse pred_setLib;

open arm_coretypesTheory arm_astTheory arm_seq_monadTheory
     arm_decoderTheory arm_opsemTheory;

val _ = new_theory "arm";

(* ------------------------------------------------------------------------ *)

val _ = numLib.prefer_num();
val _ = wordsLib.prefer_word();

val _ = temp_overload_on (parmonadsyntax.monad_bind, ``seqT``);
val _ = temp_overload_on (parmonadsyntax.monad_par,  ``parT``);
val _ = temp_overload_on ("return", ``constT``);

(* ------------------------------------------------------------------------ *)

val fetch_instruction_def = Define`
  fetch_instruction ii : (Encoding # word4 # ARMinstruction) M =
    (read_arch ii ||| read_cpsr ii ||| read_pc ii) >>=
    (\(arch,cpsr,pc).
       if cpsr.T /\ arch <> ARMv4 then (* Thumb *)
         read_memA ii (pc,2) >>=
         (\ireg1. let ireg1 = word16 ireg1 in
            if ((15 -- 13) ireg1 = 0b111w) /\ (12 -- 11) ireg1 <> 0b00w
            then (* 32-bit Thumb *)
              read_memA ii (pc + 2w, 2) >>=
              (\ireg2.
                 constT (Encoding_Thumb2,
                         thumb2_decode cpsr.IT (ireg1,word16 ireg2)))
            else (* 16-bit Thumb *)
              constT (Encoding_Thumb, thumb_decode arch cpsr.IT ireg1))
       else if ~cpsr.T /\ arch <> ARMv7_M then (* ARM *)
         read_memA ii (pc,4) >>=
         (\ireg.
            constT (Encoding_ARM,
                    arm_decode (version_number arch < 5) (word32 ireg)))
       else
         errorT "fetch_instruction: unpredictable")`;

val arm_next_def = Define`
  arm_next ii =
    (event_registered ii ||| waiting_for_interrupt ii) >>=
    (\(registered,wfi).
      if ~registered \/ wfi then
        constT ()
      else
        fetch_instruction ii >>= arm_instr ii)`;

val arm_run_def = Define`
  arm_run t ii =
    (forT 0 t (K (arm_next ii))) >>=
    (\unit_list:unit list. constT ())`;

val arm_test_def = Define`
  arm_test (f:'a M) (c:'b) P s =
    case f s
    of Error e -> F
    || ValueState v q -> P q`;

(* ------------------------------------------------------------------------ *)

val _ = export_theory ();
