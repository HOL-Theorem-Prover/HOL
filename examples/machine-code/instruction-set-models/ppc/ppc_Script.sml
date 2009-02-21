
open HolKernel boolLib bossLib Parse;

open ppc_coretypesTheory ppc_astTheory ppc_opsemTheory ppc_seq_monadTheory ppc_decoderTheory ;

val _ = new_theory "ppc_";

(* ---------------------------------------------------------------------------------- *>

  Here the decoder from ppc_decoderTheory is put together with ppc_exec_instr
  from ppc_opsemTheory and the sequential monad from ppc_seq_monadTheory.

<* ---------------------------------------------------------------------------------- *)

val iiid_dummy_def = Define `iiid_dummy = <| proc:=0; program_order_index:=0 |>`;

val PPC_NEXT_def = Define `
  PPC_NEXT s = 
    let pc = PREAD_R PPC_PC s in
    let w0 = PREAD_M (pc + 0w) s in
    let w1 = PREAD_M (pc + 1w) s in
    let w2 = PREAD_M (pc + 2w) s in
    let w3 = PREAD_M (pc + 3w) s in
    let raw_instruction = w2bits (THE w3) ++ w2bits (THE w2) ++ w2bits (THE w1) ++ w2bits (THE w0) in
    let i = ppc_decode raw_instruction in
    let s' = ppc_exec_instr iiid_dummy (THE i) s in
      if ~(pc && 3w = 0w) \/ MEM NONE [w0;w1;w2;w3] \/ (i = NONE) \/ (s' = NONE) then NONE
      else SOME (SND (THE s'))`;

val PPC_NEXT_THM = store_thm("PPC_NEXT_THM",
  ``(ppc_decode xs = SOME i) ==>
    !w0 w1 w2 w3.
      (w2bits w3 ++ w2bits w2 ++ w2bits w1 ++ w2bits w0 = xs) ==>
      (ppc_exec_instr iiid_dummy i s = SOME (tt,s')) ==>   
      (PREAD_R PPC_PC s && 3w = 0w) ==>
      (PREAD_M (PREAD_R PPC_PC s + 0w) s = SOME w0) ==>
      (PREAD_M (PREAD_R PPC_PC s + 1w) s = SOME w1) ==>
      (PREAD_M (PREAD_R PPC_PC s + 2w) s = SOME w2) ==>
      (PREAD_M (PREAD_R PPC_PC s + 3w) s = SOME w3) ==>
      (PPC_NEXT s = SOME s')``,
  SIMP_TAC std_ss [PPC_NEXT_def,LET_DEF,listTheory.MEM]);


val _ = export_theory ();
