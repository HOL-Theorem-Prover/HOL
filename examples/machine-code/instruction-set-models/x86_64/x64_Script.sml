
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory;

open x64_coretypesTheory x64_astTheory x64_opsemTheory;
open x64_seq_monadTheory x64_decoderTheory x64_icacheTheory;

val _ = new_theory "x64_";

(* ---------------------------------------------------------------------------------- *>

  Here the decoder from x64_decoderTheory is put together with x64_execute
  from x64_opsemTheory and the sequential monad from x64_seq_monadTheory.

<* ---------------------------------------------------------------------------------- *)

val iiid_dummy_def = Define `iiid_dummy = <| proc:=0; program_order_index:=0 |>`;

val x64_decode_bytes_def = Define `
  x64_decode_bytes b = x64_decode (FOLDR APPEND [] (MAP w2bits b))`;

val x64_execute_some_def = Define `
  x64_execute_some i w s = option_apply (x64_execute iiid_dummy i w s) (\t. SOME (SND t))`;

val Z64_NEXT_def = Define `
  Z64_NEXT s =
    let e = ZREAD_RIP s in                                     (* read rip *)
    let xs = MAP THE (ZREAD_INSTR_BYTES 20 e s) in             (* read next 20 bytes *)
    let m = x64_decode_bytes xs in                             (* attempt to decode *)
      if m = NONE then NONE else                               (* if decoded fail, return NONE *)
        let (i,w) = THE m in                                   (* otherwise extract content *)
        let n = 20 - (LENGTH w DIV 8) in                       (* calc length of instruction *)
          if EVERY (\x. ~(x = NONE)) (ZREAD_INSTR_BYTES n e s) (* check that the memory is there *)
          then x64_execute_some i (n2w n) s else NONE          (* execute the instruction *)`;

val Z64_NEXT_REL_def = Define `
  Z64_NEXT_REL s t = ?u. Z64_ICACHE s u /\ (Z64_NEXT u = SOME t)`;


(* help to evaluate Z64_NEXT *)

val Z64_NEXT_THM = store_thm("Z64_NEXT_THM",
  ``(x64_decode xs = SOME (i,w)) ==>
    (FOLDR APPEND [] (MAP w2bits (MAP THE (ZREAD_INSTR_BYTES 20 (ZREAD_RIP s) s))) = xs) ==>
    (EVERY (\x. ~(x = NONE)) (ZREAD_INSTR_BYTES (20 - (LENGTH w DIV 8)) (ZREAD_RIP s) s)) ==>
    (x64_execute iiid_dummy i (n2w (20 - (LENGTH w DIV 8))) s = SOME (tt,s')) ==>
    (Z64_NEXT s = SOME s')``,
  SIMP_TAC std_ss [Z64_NEXT_def,LET_DEF,ZREAD_REG_def,x64_decode_bytes_def,
    x64_execute_some_def,option_apply_def]);


val _ = export_theory ();
