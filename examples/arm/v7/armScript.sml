(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics (A and R profiles)                        *)
(*     =============================================                        *)
(*     Top-level: fetch and run instructions                                *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["arm_decoderTheory", "arm_opsemTheory",
            "pred_setLib", "wordsLib", "parmonadsyntax"];
*)

open HolKernel boolLib bossLib Parse pred_setLib;

open arm_coretypesTheory arm_astTheory arm_seq_monadTheory
     arm_decoderTheory arm_opsemTheory;

val _ = new_theory "arm";

(* ------------------------------------------------------------------------ *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

val _ = temp_overload_on (parmonadsyntax.monad_bind, ``seqT``);
val _ = temp_overload_on (parmonadsyntax.monad_par,  ``parT``);
val _ = temp_overload_on ("return", ``constT``);

val _ = temp_overload_on ("PAD0", ``list$PAD_LEFT #"0"``);

(* ------------------------------------------------------------------------ *)

(* Get the actual instruction set.  An alternative version could raise an error
   if iset is Thumb, Jazelle or ThumbEE when these aren't avaialble. *)

val actual_instr_set_def = Define`
  actual_instr_set ii : InstrSet M =
    read_arch ii >>=
    (\arch.
      if arch = ARMv4 then
        constT InstrSet_ARM
      else
        current_instr_set ii >>=
        (\iset.
          if iset = InstrSet_Jazelle then
            have_jazelle ii >>=
            (\HaveJazelle.
              constT (if HaveJazelle then iset else InstrSet_ARM))
          else if iset = InstrSet_ThumbEE then
            have_thumbEE ii >>=
            (\HaveThumbEE.
              constT (if HaveThumbEE then iset else InstrSet_Thumb))
          else
            constT iset))`;

val fetch_arm_def = Define`
  fetch_arm ii read_word : (string # Encoding # word4 # ARMinstruction) M =
    (read_pc ii ||| arch_version ii) >>=
    (\(pc,v).
       read_word pc >>=
       (\ireg.
          constT (PAD0 8 (word_to_hex_string ireg),
                  Encoding_ARM, arm_decode (v < 5) ireg)))`;

val fetch_thumb_def = Define`
  fetch_thumb ii ee read_halfword
    : (string # Encoding # word4 # ARMinstruction) M =
    (read_pc ii ||| read_cpsr ii ||| read_arch ii) >>=
    (\(pc,cpsr,arch).
      read_halfword pc >>= (\ireg1.
        if ((15 -- 13) ireg1 = 0b111w) /\ (12 -- 11) ireg1 <> 0b00w then
          read_halfword (pc + 2w) >>= (\ireg2.
            constT (PAD0 4 (word_to_hex_string ireg1) ++ " " ++
                    PAD0 4 (word_to_hex_string ireg2),
                    Encoding_Thumb2, thumb2_decode arch cpsr.IT (ireg1,ireg2)))
        else
          constT
            (PAD0 4 (word_to_hex_string ireg1),
             if ee then
               thumbee_decode arch cpsr.IT ireg1
             else
               (Encoding_Thumb, thumb_decode arch cpsr.IT ireg1))))`;

val fetch_instruction_def = Define`
  fetch_instruction ii
    read_word read_halfword : (string # Encoding # word4 # ARMinstruction) M =
    actual_instr_set ii >>=
    (\iset.
       case iset
       of InstrSet_ARM     => fetch_arm ii read_word
        | InstrSet_Thumb   => fetch_thumb ii F read_halfword
        | InstrSet_ThumbEE => fetch_thumb ii T read_halfword
        | InstrSet_Jazelle =>
            errorT ("fetch_instruction: Jazelle not supported"))`;

val arm_next_def = Define`
  arm_next ii irpt : unit M =
    if irpt = NoInterrupt then
      waiting_for_interrupt ii >>=
      (\wfi.
         condT (~wfi)
           (fetch_instruction ii
               (\a. read_memA ii (a, 4) >>= (\d. return (word32 d)))
               (\a. read_memA ii (a, 2) >>= (\d. return (word16 d))) >>=
            (\(opc,instr). arm_instr ii instr)))
    else
      (if irpt = HW_Reset then
          take_reset ii
        else if irpt = HW_Fiq then
          take_fiq_exception ii
        else (* irpt = HW_Irq *)
          take_irq_exception ii) >>=
      (\u:unit. clear_wait_for_interrupt ii)`;

val arm_run_def = Define`
  arm_run t ii inp =
    (forT 0 t
      (\t.
         let irpt = inp t in
           if (irpt = NoInterrupt) \/ (irpt = HW_Reset) then
             arm_next ii irpt
           else
             read_cpsr ii >>=
             (\cpsr.
                arm_next ii NoInterrupt >>=
                (\u:unit.
                  condT ((irpt = HW_Fiq) /\ ~cpsr.F \/
                         (irpt = HW_Irq) /\ ~cpsr.I)
                        (arm_next ii irpt))))) >>=
    (\unit_list:unit list. constT ())`;

(* ------------------------------------------------------------------------ *)

val _ = export_theory ();
