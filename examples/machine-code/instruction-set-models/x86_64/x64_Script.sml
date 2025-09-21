
Theory x64_
Ancestors
  words bit_list x64_coretypes x64_ast x64_opsem x64_seq_monad
  x64_decoder x64_icache

(* ---------------------------------------------------------------------------------- *>

  Here the decoder from x64_decoderTheory is put together with x64_execute
  from x64_opsemTheory and the sequential monad from x64_seq_monadTheory.

<* ---------------------------------------------------------------------------------- *)

val iiid_dummy_def = Define `iiid_dummy = <| proc:=0; program_order_index:=0 |>`;

val x64_decode_bytes_def = Define `
  x64_decode_bytes b = x64_decode (FOLDR APPEND [] (MAP w2bits b))`;

val x64_execute_some_def = Define `
  x64_execute_some i w s = option_apply (x64_execute iiid_dummy i w s) (\t. SOME (SND t))`;

val X64_NEXT_def = Define `
  X64_NEXT s =
    let e = ZREAD_RIP s in                                     (* read rip *)
    let xs = MAP THE (ZREAD_INSTR_BYTES 20 e s) in             (* read next 20 bytes *)
    let m = x64_decode_bytes xs in                             (* attempt to decode *)
      if m = NONE then NONE else                               (* if decoded fail, return NONE *)
        let (i,w) = THE m in                                   (* otherwise extract content *)
        let n = 20 - (LENGTH w DIV 8) in                       (* calc length of instruction *)
          if EVERY (\x. ~(x = NONE)) (ZREAD_INSTR_BYTES n e s) (* check that the memory is there *)
          then x64_execute_some i (n2w n) s else NONE          (* execute the instruction *)`;

val X64_NEXT_REL_def = Define `
  X64_NEXT_REL s t = ?u. X64_ICACHE s u /\ (X64_NEXT u = SOME t)`;


(* help to evaluate X64_NEXT *)

val X64_NEXT_THM = store_thm("X64_NEXT_THM",
  ``(x64_decode xs = SOME (i,w)) ==>
    (FOLDR APPEND [] (MAP w2bits (MAP THE (ZREAD_INSTR_BYTES 20 (ZREAD_RIP s) s))) = xs) ==>
    (EVERY (\x. ~(x = NONE)) (ZREAD_INSTR_BYTES (20 - (LENGTH w DIV 8)) (ZREAD_RIP s) s)) ==>
    (x64_execute iiid_dummy i (n2w (20 - (LENGTH w DIV 8))) s = SOME (tt,s')) ==>
    (X64_NEXT s = SOME s')``,
  SIMP_TAC std_ss [X64_NEXT_def,LET_DEF,ZREAD_REG_def,x64_decode_bytes_def,
    x64_execute_some_def,option_apply_def]);


