
open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib listTheory;

open armTheory arm_coretypesTheory;

val _ = new_theory "lpc_uart";


(* We define the state of a UART interface *)

val _ = Hol_datatype `
  uart0_state = <|

    (* physical state components *)

    U0RBR : word8;   (* receive buffer *)
    U0THR : word8;   (* transmit holding buffer *)
    U0LCR : word32;  (* line control register *)
    U0LSR : word32;  (* line status register *)

    (* logical state components *)

    input_list  : word8 list;  (* list of bytes that will be received from serial cable *)
    input_time  : num;         (* time from which U0THR is ready for next read *)

    output_list : word8 list;  (* list of bytes that have been sent via serial cable *)
    output_time : num          (* time from which U0RBR is ready for next write *)

    (* Why are these time components here? Answer: we want the
       interface to eventually respond: both in and out can either be
       in a state ready for operation {in,out}put_time <= current_time
       or be in a state which waits for current_time to increase to
       the point where {in,out}put_time <= current_time is true. This
       has a baked in assumption of liveness of the other party: we
       assume that the UART never has to wait forever for the other
       party (device at the other end of the serial cable). *)

  |>`;


(* We define an invariant for the UART0 state *)

val uart0_ok_def = Define `
  uart0_ok current_time (uart0:uart0_state) =
    (* U0LCR must be in a usable state *)
    (uart0.U0LCR ' 7 = F) /\
    (* U0LSR bit 0 and bit 5 indicate whether U0RBR and U0THR, resp., are ready for use *)
    (uart0.U0LSR ' 0 = (uart0.input_time <= current_time) /\ ~(uart0.input_list = [])) /\
    (uart0.U0LSR ' 5 = (uart0.output_time <= current_time)) /\
    (* Content of U0RBR and U0THR is determined by state of U0LSR *)
    (?w. uart0.U0RBR = if uart0.U0LSR ' 0 then HD (uart0.input_list) else w) /\
    (?w. uart0.U0THR = if uart0.U0LSR ' 5 then w else HD (uart0.output_list))`;


(* We define what addresses are owned by UART0, and whether they can be read and written *)

val UART0_addresses_def = Define `
  UART0_addresses =
    { x | 0xE000C000w <=+ x /\ x <+ 0xE000C034w } : word32 set`;


(* We define what value the core sees if it reads one of UART0's addresses *)

val mm_byte_reader_def = Define `
  mm_byte_reader (a:word32) (b:word8) = (a =+ b)`;

val mm_word_reader_def = Define `
  mm_word_reader (a:word32) (w:word32) =
    (a+0w =+ ( 7 ><  0) w) o
    (a+1w =+ (15 ><  8) w) o
    (a+2w =+ (23 >< 16) w) o
    (a+3w =+ (31 >< 24) w)`;

val UART0_read_def = Define `
  UART0_read (uart0:uart0_state) =
   (mm_byte_reader 0xE000C000w (uart0.U0RBR) o
    mm_word_reader 0xE000C00Cw (uart0.U0LCR) o
    mm_word_reader 0xE000C014w (uart0.U0LSR)) (\a. ARB)`;


(* We define the possible next states (some s2) after a clock tick (starting from s1) *)

val BYTE_WRITTEN_TO_MEM_def = Define `
  (BYTE_WRITTEN_TO_MEM a [] = ARB) /\
  (BYTE_WRITTEN_TO_MEM a ((MEM_READ w)::xs) = BYTE_WRITTEN_TO_MEM a xs) /\
  (BYTE_WRITTEN_TO_MEM a ((MEM_WRITE w v)::xs) = if a = w then v else BYTE_WRITTEN_TO_MEM a xs)`;

val _ = wordsLib.guess_lengths();
val WORD_WRITTEN_TO_MEM_def = Define `
  WORD_WRITTEN_TO_MEM a accesses =
    BYTE_WRITTEN_TO_MEM (a+3w) accesses @@
    BYTE_WRITTEN_TO_MEM (a+2w) accesses @@
    BYTE_WRITTEN_TO_MEM (a+1w) accesses @@
    BYTE_WRITTEN_TO_MEM (a+0w) accesses`;

val ADDR_SET_def = Define `
  (ADDR_SET [] = {}) /\
  (ADDR_SET ((MEM_READ a)::xs) = a INSERT ADDR_SET xs) /\
  (ADDR_SET ((MEM_WRITE a b)::xs) = a INSERT ADDR_SET xs)`;

val ALL_OR_NOTHING_def = Define `
  ALL_OR_NOTHING x a = (x INTER a = a) \/ (x INTER a = {})`;

val IS_MEM_READ_def = Define `
  (IS_MEM_READ (MEM_READ a) = T) /\ (IS_MEM_READ _ = F)`;

val IS_MEM_WRITE_def = Define `
  (IS_MEM_WRITE (MEM_WRITE a w) = T) /\ (IS_MEM_WRITE _ = F)`;

(* read-write enabled *)
val REG32_RW_NEXT_def = Define `
  REG32_RW_NEXT addr pre_value accesses post_value =
    let a = {addr; addr+1w; addr+2w; addr+3w} in
    let reads = ADDR_SET (FILTER IS_MEM_READ accesses) in
    let writes = ADDR_SET (FILTER IS_MEM_WRITE accesses) in
      ALL_OR_NOTHING reads a /\
      ALL_OR_NOTHING writes a /\
      (post_value = if addr IN writes
                    then WORD_WRITTEN_TO_MEM addr accesses
                    else pre_value)`;


(* read only version *)
val REG32_RO_NEXT_def = Define `
  REG32_RO_NEXT addr accesses =
    let a = {addr; addr+1w; addr+2w; addr+3w} in
    let reads = ADDR_SET (FILTER IS_MEM_READ accesses) in
    let writes = ADDR_SET (FILTER IS_MEM_WRITE accesses) in
      ALL_OR_NOTHING reads a /\
      (a INTER writes = {})`;


val UART0_NEXT_def = Define `
  UART0_NEXT current_time (accesses:memory_access list) (s1:uart0_state) (s2:uart0_state) =

    (* both before and after state must be consistent, i.e. logical components of
       each state must agree with physical components of resp. state. *)
    uart0_ok current_time s1 /\ uart0_ok (current_time+1) s2 /\

    (* if read happened then ... else ... *)
    (if MEM (MEM_READ 0xE000C000w) accesses then
       (s1.U0LSR ' 0 = T) /\ (* fail if UART0 was not ready for a read *)
       (s2.input_list = TL s1.input_list) (* pop one element off input list *)
       (* implicity let input_delay in s2 be any natural number *)
     else
       (* if no read happened then do nothing *)
       (s2.input_time = s1.input_time) /\
       (s2.input_list = s1.input_list)) /\

    (* if write happened then ... else ... *)
    (if ?w. MEM (MEM_WRITE 0xE000C000w w) accesses then
       (s1.U0LSR ' 5 = T) /\ (* fail if UART0 was not ready for a write *)
       (s2.output_list = w2w (BYTE_WRITTEN_TO_MEM 0xE000C000w accesses) :: s1.output_list) (* cons new output *)
       (* implicity let output_delay in s2 be any natural number *)
     else
       (* if no write happened then do nothing *)
       (s2.output_time = s1.output_time) /\
       (s2.output_list = s1.output_list)) /\

    (* the 32-bit memory-mapped registers *)
    REG32_RW_NEXT 0xE000C00Cw (s1.U0LCR) accesses (s2.U0LCR) /\
    REG32_RO_NEXT 0xE000C014w accesses`;




(* A lemma needed later on *)

val REG32_NEXT_NIL = prove(
  ``!x w1 w2. (REG32_RW_NEXT x w1 [] w2 = (w1 = w2)) /\
              (REG32_RO_NEXT x [] = T)``,
  SIMP_TAC std_ss [REG32_RW_NEXT_def,REG32_RO_NEXT_def,LET_DEF,FILTER,ADDR_SET_def,
     pred_setTheory.NOT_IN_EMPTY,ALL_OR_NOTHING_def,pred_setTheory.INTER_EMPTY]
  THEN METIS_TAC []);

val BIT_UPDATE_def = Define `
  BIT_UPDATE i b (w:'a word) = (FCP j. if i = j then b else w ' j):'a word`;

val APPLY_BIT_UPDATE_THM = store_thm("APPLY_BIT_UPDATE_THM",
  ``!i j b w.
      j < dimindex (:'a) ==>
      (BIT_UPDATE i b (w:'a word) ' j = if i = j then b else w ' j)``,
  SIMP_TAC std_ss [fcpTheory.CART_EQ,BIT_UPDATE_def,fcpTheory.FCP_BETA]);

val UART0_NEXT_EXISTS = store_thm("UART0_NEXT_EXISTS",
  ``!t s1. uart0_ok t s1 ==> ?s2. UART0_NEXT t [] s1 s2``,
  SIMP_TAC std_ss [UART0_NEXT_def,uart0_ok_def,MEM,REG32_NEXT_NIL]
  THEN REPEAT STRIP_TAC
  THEN EXISTS_TAC
  ``<| U0RBR := if s1.input_time <= t + 1 /\ s1.input_list <> [] then HD s1.input_list else ARB;
       U0THR := if s1.output_time <= t + 1 then ARB else HD s1.output_list;
       U0LCR := s1.U0LCR;
       U0LSR := BIT_UPDATE 0 (s1.input_time <= t + 1 /\ s1.input_list <> [])
               (BIT_UPDATE 5 (s1.output_time <= t + 1) s1.U0LSR);
       input_list  := s1.input_list;
       input_time  := s1.input_time;
       output_list := s1.output_list;
       output_time := s1.output_time |>``
  THEN SRW_TAC [] [APPLY_BIT_UPDATE_THM]);

val UART0_READ_def = Define `
  UART0_READ (uart0:uart0_state) =
    (uart0.input_list,uart0.input_time,uart0.output_list,uart0.output_time)`;


(* -- old part of script commented out, but might be used in the future



(* UART0 does nothing observable when left untouched,
   similarly reading LSR has no observable effect. *)

val UART0_NEXT_NIL = store_thm("UART0_NEXT_NIL",
  ``!t s1 s2.
      UART0_NEXT t [] s1 s2 =
      uart0_ok t s1 /\ uart0_ok (t+1) s2 /\ (UART0_READ s1 = UART0_READ s2)``,
  SIMP_TAC std_ss [UART0_READ_def,UART0_NEXT_def,MEM] THEN METIS_TAC []);

val UART0_NEXT_READ_LSR = store_thm("UART0_NEXT_READ_LSR",
  ``!t s1 s2.
      UART0_NEXT t [MEM_READ 0xE000C014w] s1 s2 =
      uart0_ok t s1 /\ uart0_ok (t+1) s2 /\ (UART0_READ s1 = UART0_READ s2)``,
  SIMP_TAC (std_ss++SIZES_ss) [UART0_READ_def,UART0_NEXT_def,MEM,
    memory_access_11,memory_access_distinct,n2w_11] THEN METIS_TAC []);

val UART0_NEXT_EXISTS = store_thm("UART0_NEXT_EXISTS",
  ``!t s1. uart0_ok t s1 ==>
           ?s2. UART0_NEXT t [] s1 s2 /\
                UART0_NEXT t [MEM_READ 0xE000C014w] s1 s2``,
  SIMP_TAC std_ss [UART0_NEXT_NIL,UART0_NEXT_READ_LSR,uart0_ok_def]
  THEN REPEAT STRIP_TAC
  THEN EXISTS_TAC
  ``<| U0RBR := if s1.input_time <= t + 1 /\ s1.input_list <> [] then HD s1.input_list else ARB;
       U0THR := if s1.output_time <= t + 1 then ARB else HD s1.output_list;
       U0LCR := s1.U0LCR;
       U0LSR := BIT_UPDATE 0 (s1.input_time <= t + 1 /\ s1.input_list <> [])
               (BIT_UPDATE 5 (s1.output_time <= t + 1) s1.U0LSR);
       input_list  := s1.input_list;
       input_time  := s1.input_time;
       output_list := s1.output_list;
       output_time := s1.output_time |>``
  THEN SRW_TAC [] [UART0_READ_def,APPLY_BIT_UPDATE_THM]);


(* UART successfully reads and writes *)

val UART0_READ = store_thm("UART0_READ",
  ``!t s1 w. uart0_ok t s1 /\ s1.U0LSR ' 0 ==>
             ?s2. UART0_NEXT t [MEM_READ 0xE000C000w] s1 s2``,
  SIMP_TAC std_ss [uart0_ok_def,UART0_NEXT_def,MEM,memory_access_11,
    memory_access_distinct,BYTE_WRITTEN_TO_MEM_def]
  THEN REPEAT STRIP_TAC
  THEN EXISTS_TAC
  ``<| U0RBR := ARB;
       U0THR := if s1.output_time <= t + 1 then ARB else HD s1.output_list;
       U0LCR := s1.U0LCR;
       U0LSR := BIT_UPDATE 0 F
               (BIT_UPDATE 5 (s1.output_time <= t + 1) s1.U0LSR);
       input_list  := TL s1.input_list;
       input_time  := t + 5;
       output_list := s1.output_list;
       output_time := s1.output_time |>``
  THEN SRW_TAC [] [UART0_READ_def,APPLY_BIT_UPDATE_THM]
  THEN FULL_SIMP_TAC std_ss []);

val UART0_WRITE = store_thm("UART0_WRITE",
  ``!t s1 w. uart0_ok t s1 /\ s1.U0LSR ' 5 ==>
             ?s2. UART0_NEXT t [MEM_WRITE 0xE000C000w w] s1 s2``,
  SIMP_TAC std_ss [uart0_ok_def,UART0_NEXT_def,MEM,memory_access_11,
    memory_access_distinct,BYTE_WRITTEN_TO_MEM_def]
  THEN REPEAT STRIP_TAC
  THEN EXISTS_TAC
  ``<| U0RBR := if s1.input_time <= t + 1 /\ s1.input_list <> [] then HD s1.input_list else ARB;
       U0THR := w2w (w:word8);
       U0LCR := s1.U0LCR;
       U0LSR := BIT_UPDATE 0 (s1.input_time <= t + 1 /\ s1.input_list <> [])
               (BIT_UPDATE 5 F s1.U0LSR);
       input_list  := s1.input_list;
       input_time  := s1.input_time;
       output_list := (w2w (w:word8)) :: s1.output_list;
       output_time := t + 5 |>``
  THEN SRW_TAC [] [UART0_READ_def,APPLY_BIT_UPDATE_THM]
  THEN FULL_SIMP_TAC std_ss []);

*)

val _ = export_theory();
