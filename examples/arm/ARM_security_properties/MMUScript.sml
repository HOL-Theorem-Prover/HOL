(*
Updates since version 4:
------------------------

  - integrate MMU into monad
  - understand access lists already with one violating entry, even if the other entries are not understood
  - leaving only one mmu_arm_next

maybe todo:

  - integrate evaluation for priv mode


Updates since version 3:
-----------------------

  - cleaning up
  - fixing a logical error in data_abort

Updates since version 2:
------------------------

  - old access list is truncated
  - todos fixed


Updates since version 1:
------------------------

  - checking only recent updates in the access list
  - correct values in mmu_supported
  - check MMU_support for needed section descriptors only
  - consistent error handling

  - obtain coprocessor registers only once
  - add mode to permitted_byte
  - correct/check case analysis of permitted_byte
  - more detailed version of mmu_arm_next (ValueState and Error X)
  - distinction between read and write


*)


(* Loading: I assume that armLib is already loaded

loadPath := "/NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/" :: !loadPath;
loadPath := "/NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/eval" :: !loadPath;

load "armLib";
open armLib;
*)

open HolKernel boolLib bossLib Parse;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory armTheory;
open parmonadsyntax;

val _ =  new_theory("MMU");

val _ = overload_on("UNKNOWN", ``ARB:bool``);
val _ = overload_on("UNKNOWN", ``ARB:word32``);

val _ = temp_delsimps ["NORMEQ_CONV"]

val read_mem32_def  = Define ` read_mem32 add mem =
    word32 ([mem (add);mem (add+1w);mem (add+2w);mem (add+3w)])`;


val enabled_MMU_def = Define `enabled_MMU (c1:word32) =
                                     let bit0 = BIT 0 (w2n(c1)) in
                                         bit0`;


(* checking MMU support only for one section descriptor *)
(* further changes in version 2: expr3 = 0 and expr7 may be 01 as well *)
val sd_supports_MMU_def = Define `sd_supports_MMU content_of_sd si =
                let expr1 = (content_of_sd && 0x00000003w) in
                let expr2 = (content_of_sd && 0x0000000Cw) >>> 2 in
                let expr3 = (content_of_sd && 0x00000010w) >>> 4 in
                let expr4 = (content_of_sd && 0x00000200w) >>> 9 in
                let expr7 = (content_of_sd && 0x00000C00w) >>> 10 in
                let expr5 = (content_of_sd && 0x000FF000w) >>> 12 in
                let expr6 = (content_of_sd && 0xFFF00000w) >>> 20 in
                    (expr1 = 0b10w:bool[32]) /\
                        (expr2 = 0b00w:word32) /\
                             (expr3 = 0b0w:word32) /\
                               (expr4 = 0b0w:word32) /\
                                   ((expr7 = 0b11w:word32) \/ (expr7 = 0b01w:word32)) /\
                                        (expr5 = 0b0w:word32) /\
                                             (expr6 = si)`;



(* permitted_byte *)
(* returns (understood, permitted, message) *)
val permitted_byte_def = Define `permitted_byte adr is_write (c1:word32) c2 (c3:bool[32]) priv mem =
                    if (~(enabled_MMU c1)) then
                        (T, T, "MMU is disabled")
                    else
                        let si = (adr >>> 20) in
                        let first_sd = c2 && (0xFFFFC000w:bool[32]) in
                        let adr_sd =  first_sd + 4w * si in
                        let content_of_sd = read_mem32 adr_sd mem in
                        let domain:bool[32] =
                                   (content_of_sd && 0x000001E0w:bool[32]) >>> 5 in
                        (* make sure that it starts with one *)
                        let bit1_c3 = BIT (2*w2n(domain)) (w2n(c3)) in
                        let bit2_c3 = BIT (2*w2n(domain)+1) (w2n(c3)) in
                        let AP = (content_of_sd && 0x00000C00w) >>> 10 in
                        if (sd_supports_MMU content_of_sd si)
                            then
                            (case (bit2_c3, bit1_c3) of
                                (T,T)  => (T, T, "uncontrolled manager domain")
                             | (F,F)  => (T, F, "no access domain")
                             | (T,F)  => (F, UNKNOWN , "unpredictable domain status")
                             | (F,T)  => (case AP of
                                             0b00w => (T, F, "no access according to PTE")
                                           |0b01w => (if priv
                                                         then (T, T , "permitted by PTE")
                                                         else (T, F, "no access according to PTE")
                                                      )
                                           |0b10w => (if priv
                                                         then (T, T , "permitted by PTE")
                                                         else (T, ~is_write, "read-only access according to PTE")
                                                      )
                                           |0b11w => (T, T , "permitted by PTE")
                                           | _    => (F, UNKNOWN, "AP wrongly determined")
                                          )
                            )
                            else
                                (F, UNKNOWN, "no support")
                        `;


(* permitted_byte_pure                       *)
(* returns boolean "permitted"               *)
(* similar to permitted_byte when assuming   *)
(*   that we always understand the MMU setup *)

val permitted_byte_pure_def = Define `permitted_byte_pure adr is_write (c1:word32) c2 (c3:bool[32]) priv mem =
                    if (~(enabled_MMU c1)) then
                        T
                    else
                        let si = (adr >>> 20) in
                        let first_sd = c2 && (0xFFFFC000w:bool[32]) in
                        let adr_sd =  first_sd + 4w * si in
                        let content_of_sd = read_mem32 adr_sd mem in
                        let domain:bool[32] =
                                   (content_of_sd && 0x000001E0w:bool[32]) >>> 5 in
                        (* make sure that it starts with one *)
                        let bit1_c3 = BIT (2*w2n(domain)) (w2n(c3)) in
                        let bit2_c3 = BIT (2*w2n(domain)+1) (w2n(c3)) in
                        let AP = (content_of_sd && 0x00000C00w) >>> 10 in
                             case (bit2_c3, bit1_c3) of
                                (T,T) => T
                             | (F,F)  => F
                             | (F,T)  => (case AP of
                                             0b00w => F
                                           |0b01w => (if priv
                                                        then T
                                                        else F
                                                     )
                                           |0b10w => (if priv
                                                        then T
                                                        else (~is_write)
                                                     )
                                           |0b11w => T
                                          )
                        `;


(* relate permitted_byte with permitted_byte_pure *)

val permitted_byte_simp = store_thm (
    "permitted_byte_simp",
    ``!u p m adr is_write c1 c2 c3 priv mem.
      ((u,p,m) = permitted_byte adr is_write c1 c2 c3 priv mem) /\ u
       ==> (permitted_byte_pure adr is_write c1 c2 c3 priv mem = p)``,
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [permitted_byte_def, permitted_byte_pure_def]
    THEN Cases_on `~enabled_MMU c1` THEN FULL_SIMP_TAC (srw_ss()) []
    THEN RW_TAC (srw_ss()) []
    THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    THEN Cases_on `sd_supports_MMU content_of_sd si` THEN Cases_on `bit2_c3` THEN Cases_on `bit1_c3` THEN Cases_on `AP=0w` THEN Cases_on `AP=1w` THEN Cases_on `priv` THEN Cases_on `AP=2w` THEN Cases_on `AP=3w` THEN FULL_SIMP_TAC (srw_ss()) []
);


(* check_accesses                            *)
(*   returns (understood, abort, address)    *);


val check_accesses_def = Define `check_accesses accesses c1 c2 c3 priv memory =
                         case accesses of
                         x::tl =>
                         ( let (adr, is_write) =
                               ( case x of
                                  MEM_READ address => (address, F)
                               | MEM_WRITE address _ => (address, T)
                               ) in

                            let (und, per, msg) = (permitted_byte adr is_write c1 c2 c3 priv memory) in
                            (
                                if (und /\ (~per)) then
                                    (T, T, adr)
                                else
                                (
                                  let (u, d, a) =  check_accesses tl c1 c2 c3 priv memory in
                                  if (u /\ d) then
                                     (T, T, a)
                                  else
                                  (
                                     if (und /\ u) then
                                        (T,F,UNKNOWN)
                                     else
                                        (F,UNKNOWN, UNKNOWN)
                                  )
                               )
                            )
                          )
                          |   _ => (T, F, UNKNOWN)`;




(* check_accesses_pure                             *)
(*   returns boolean "abort"                       *)
(* similar to check_accesses when assuming that we *)
(*   always understand the MMU setup               *)
val check_accesses_pure_def = Define `check_accesses_pure accesses c1 c2 c3 priv memory =
                       case accesses of
                         x::tl =>
                         ( let (adr, is_write) =
                               ( case x of
                                  MEM_READ address => (address, F)
                               | MEM_WRITE address _ => (address, T)
                               ) in
                            (~permitted_byte_pure adr is_write c1 c2 c3 priv memory) \/  (check_accesses_pure tl c1 c2 c3 priv memory)
                          )
                          | _ => F`;





(* relate check_accesses with check_accesses_pure *)


val check_accesses_TAC  = (fn IS_WRITE =>
 FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    THEN Cases_on [QUOTE ("permitted_byte c "^IS_WRITE^" c1 c2 c3 priv mem")]
    THEN Cases_on `r`
    THEN Cases_on `q`
    THEN FULL_SIMP_TAC (srw_ss()) [permitted_byte_simp]
    THEN MP_TAC ( SPECL [``T``,
                         ``q':bool``,
                         ``r':string``,
                         ``c:word32``,
                         Term [QUOTE IS_WRITE],
                         ``c1:word32``,
                         ``c2:word32``,
                         ``c3:word32``,
                         ``priv:bool``,
                         ``mem:bool[32] -> bool[8]``] permitted_byte_simp)
    THEN RW_TAC (srw_ss()) []
    THEN Cases_on `check_accesses acc c1 c2 c3 priv mem`
    THEN Cases_on `r`
    THEN FULL_SIMP_TAC (srw_ss())[permitted_byte_simp]
    THEN Cases_on `q`
    THEN Cases_on `q'`
    THEN (TRY (Cases_on `q''`))
    THEN FULL_SIMP_TAC (srw_ss()) []
    THEN (NO_TAC ORELSE METIS_TAC []));


val check_accesses_simp = store_thm (
    "check_accesses_simp",
    ``!u a add acc c1 c2 c3 priv mem.
      ((u,a,add) = check_accesses acc c1 c2 c3 priv mem) /\ u
       ==> (check_accesses_pure acc c1 c2 c3 priv mem = a)``,
    Induct_on `acc`
    THENL [RW_TAC (srw_ss()) [check_accesses_def, check_accesses_pure_def],
           ONCE_REWRITE_TAC [check_accesses_def, check_accesses_pure_def]
             THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
             THEN NTAC 8 STRIP_TAC
             THEN CASE_TAC
             THENL [check_accesses_TAC ("F"), check_accesses_TAC ("T")]
        ]);




(* conclude the understandability of check_accesses from the understandability of permitted_byte *)

val check_accesses_understand = store_thm (
    "check_accesses_understand",
    ``!acc c1 c2 c3 priv mem.
       (!add is_write. FST (permitted_byte add is_write c1 c2 c3 priv mem))
     ==>  (FST (check_accesses acc c1 c2 c3 priv mem))``,
    Induct_on `acc`
    THENL [RW_TAC (srw_ss()) [check_accesses_def],
             ONCE_REWRITE_TAC [check_accesses_def]
             THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
             THEN STRIP_TAC
             THEN CASE_TAC
             THEN PairRules.PBETA_TAC
             THEN RW_TAC (srw_ss()) []
        ]);



(* access_violation_full *)


val access_violation_full_def = Define `access_violation_full s = check_accesses s.accesses
                                                           s.coprocessors.state.cp15.C1
                                                           s.coprocessors.state.cp15.C2
                                                           s.coprocessors.state.cp15.C3
                                                           F
                                                           s.memory`;

(* empty access list, no violation *)

val empty_accesses_full_lem = store_thm(
    "empty_accesses_full_lem",
    ``(s.accesses = []) ==> ((access_violation_full s) = (T,F, ARB))``,
    NTAC 2 (PURE_ONCE_REWRITE_TAC [access_violation_full_def, check_accesses_def])
      THEN RW_TAC (srw_ss()) []);



(* access_violation_pure *)


val access_violation_pure_def = Define `access_violation_pure s = check_accesses_pure s.accesses
                                                           s.coprocessors.state.cp15.C1
                                                           s.coprocessors.state.cp15.C2
                                                           s.coprocessors.state.cp15.C3
                                                           F

                                               s.memory`;

(* relate access_violation_pure and access_violation_full *)

val access_violation_simp_pure= store_thm(
    "access_violation_simp_pure",
    ``!u a add s.
      ((u,a,add) = access_violation_full s) /\ u
       ==> (access_violation_pure s = a)``,
      FULL_SIMP_TAC (srw_ss()) [access_violation_full_def, access_violation_pure_def]
        THEN METIS_TAC [check_accesses_simp]);


(* partially specified access_violation *)

(*new_constant("access_violation", ``:arm_state -> bool``);*)

val access_violation_def = new_axiom("access_violation_axiom", ``!state u x add.
         ((u,x,add) = access_violation_full state)  /\ u
   ==>   (access_violation state = x) ``);


(* if full version is understood, access_violation is equal to pure version *)

val access_violation_simp = store_thm (
    "access_violation_simp",
    ``!s x add.
      ((T,x,add) = access_violation_full s)
       ==> (access_violation s = access_violation_pure s)``,
      METIS_TAC [access_violation_simp_pure, access_violation_def]);

val access_violation_simp_FST = store_thm (
    "access_violation_simp_FST",
    ``!s. (FST (access_violation_full s))
       ==> (access_violation s = access_violation_pure s)``,
     REPEAT STRIP_TAC
       THEN Cases_on `access_violation_full s`
       THEN Cases_on `r`
       THEN FULL_SIMP_TAC (srw_ss()) [access_violation_simp]);

(* empty access list, no violation *)

val empty_accesses_lem = store_thm(
    "empty_accesses_lem",
    ``(s.accesses = []) ==> (~access_violation s)``,
    STRIP_TAC
      THEN IMP_RES_TAC empty_accesses_full_lem
      THEN ASSUME_TAC (SPECL [``s:arm_state``, ``T``, ``F``, ``ARB:word32``] access_violation_def)
      THEN FULL_SIMP_TAC (srw_ss()) []);

(* take data abort exception *)

val _ = temp_overload_on ("unit4", ``\( u1:unit,u2:unit,u3:unit,u4:unit). constT ()``);

(* mmu_arm_next *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

(*val _ = temp_overload_on (parmonadsyntax.monad_bind, ``seqT``);*)
val _ = temp_overload_on (parmonadsyntax.monad_par,  ``parT``);
val _ = temp_overload_on ("return", ``constT``);

val _ = temp_overload_on ("PAD0", ``list$PAD_LEFT #"0"``);


val mmu_arm_next_def = Define `mmu_arm_next irpt state  =
    if irpt = NoInterrupt then
    (
       case (waiting_for_interrupt  <|proc:=0|> (state with accesses := [])) of
               Error e => Error e
            |  ValueState wfi wfi_state =>
               (
                  if (wfi) then ValueState () wfi_state
                  else
                  (
                     case (fetch_instruction <|proc:=0|> (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))
                                                         (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))
                                                         (wfi_state with accesses := [])) of
                             Error e => Error e
                          |  ValueState (opc,instr) fetched_state =>
                             (
                                if access_violation fetched_state then
                                   take_prefetch_abort_exception <| proc := 0 |> (fetched_state with accesses := [])
                                else
                                   case arm_instr <|proc:=0|> instr (fetched_state with accesses := []) of
                                        Error e => Error e
                                     |  ValueState x end_state =>
                                        (
                                            if access_violation end_state then
                                               take_data_abort_exception <| proc := 0 |> (end_state with accesses := [])
                                            else
                                               ValueState () end_state
                                        )
                             )
                   )
               )

     )
    else
      (((if irpt = HW_Reset then
          take_reset <|proc:=0|>
        else if irpt = HW_Fiq then
          take_fiq_exception <|proc:=0|>
        else (* irpt = HW_Irq *)
          take_irq_exception <|proc:=0|>) >>=
      (\u:unit. clear_wait_for_interrupt <|proc:=0|>)) (state with accesses := []))`;


val _ = export_theory();


