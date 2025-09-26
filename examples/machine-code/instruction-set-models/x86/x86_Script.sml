
Theory x86_
Ancestors
  words bit_list x86_coretypes x86_ast x86_opsem x86_seq_monad
  x86_decoder x86_icache

(* ---------------------------------------------------------------------------------- *>

  Here the decoder from x86_decoderTheory is put together with x86_execute
  from x86_opsemTheory and the sequential monad from x86_seq_monadTheory.

<* ---------------------------------------------------------------------------------- *)

val iiid_dummy_def = Define `iiid_dummy = <| proc:=0; program_order_index:=0 |>`;

val x86_decode_bytes_def = Define `
  x86_decode_bytes b = x86_decode (FOLDR APPEND [] (MAP w2bits b))`;

val x86_execute_some_def = Define `
  x86_execute_some i w s = option_apply (x86_execute iiid_dummy i w s) (\t. SOME (SND t))`;

val X86_NEXT_def = Define `
  X86_NEXT s =
    let e = XREAD_EIP s in                                     (* read eip *)
    let xs = MAP THE (XREAD_INSTR_BYTES 20 e s) in             (* read next 20 bytes *)
    let m = x86_decode_bytes xs in                             (* attempt to decode *)
      if m = NONE then NONE else                               (* if decoded fail, return NONE *)
        let (i,w) = THE m in                                   (* otherwise extract content *)
        let n = 20 - (LENGTH w DIV 8) in                       (* calc length of instruction *)
          if EVERY (\x. ~(x = NONE)) (XREAD_INSTR_BYTES n e s) (* check that the memory is there *)
          then x86_execute_some i (n2w n) s else NONE          (* execute the instruction *)`;

val X86_NEXT_REL_def = Define `
  X86_NEXT_REL s t = ?u. X86_ICACHE s u /\ (X86_NEXT u = SOME t)`;


(* help to evaluate X86_NEXT *)

val X86_NEXT_THM = store_thm("X86_NEXT_THM",
  ``(x86_decode xs = SOME (i,w)) ==>
    (FOLDR APPEND [] (MAP w2bits (MAP THE (XREAD_INSTR_BYTES 20 (XREAD_EIP s) s))) = xs) ==>
    (EVERY (\x. ~(x = NONE)) (XREAD_INSTR_BYTES (20 - (LENGTH w DIV 8)) (XREAD_EIP s) s)) ==>
    (x86_execute iiid_dummy i (n2w (20 - (LENGTH w DIV 8))) s = SOME (tt,s')) ==>
    (X86_NEXT s = SOME s')``,
  SIMP_TAC std_ss [X86_NEXT_def,LET_DEF,XREAD_REG_def,x86_decode_bytes_def,
    x86_execute_some_def,option_apply_def]);


(* test whether decoding works, if this is slow then something's wrong *)

val t1 = Time.now();
val th = EVAL ``x86_decode(bytebits "D1F8")``;  (* sar eax, 1 *)
val t2 = Time.now();
val elapsed_time = Time.toReal t2 - Time.toReal t1
val _ = elapsed_time < 5.0 orelse failwith("Decoding failed to use compset properly.")

