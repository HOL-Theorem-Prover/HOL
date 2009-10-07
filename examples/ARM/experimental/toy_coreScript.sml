
open HolKernel boolLib bossLib Parse;
open wordsTheory;

val _ = new_theory "toy_core";


(* -------------------------------------------------------------------------- *)
(*  Type definitions                                                          *)
(* -------------------------------------------------------------------------- *)

(* This theory defines a toy processor core which handles the 
   following instructions: *)

val _ = type_abbrev ("reg",``:word4``); 

val _ = Hol_datatype `instruction = 
    (* reg update *) iREG of reg => reg => reg => (word32 -> word32 -> word32)
  | (* compare *) iCMP of reg => reg => (word32 -> word32 -> bool)
  | (* load *) iLDR of reg => reg # word32
  | (* store *) iSTR of reg => reg # word32
  | (* conditional branch *) iBCC of word32
  | (* unconditional branch *) iB of word32`;

(* explanation:
     iREG 1w 2w 3w (\x y. x + y)    resembles ARM:  add r1,r2,r3
     iREG 1w 1w 1w (\x y. 45w)      resembles ARM:  mov r1,#45
     iREG 1w 2w 2w (\x y. x)        resembles ARM:  mov r1,r2
     iCMP 1w 2w (\x y. x = y)       resembles ARM:  cmp r1,r2
     iLDR 1w (2w,0w)                resembles ARM:  ldr r1,[r2]
     iLDR 1w (2w,40w)               resembles ARM:  ldr r1,[r2,#40]
     iSTR 1w (2w,40w)               resembles ARM:  str r1,[r2,#40]
     iBCC 40w           updates the program counter by 40w if status bit is set
*)

(* The state of the core consists of 16 registers, a Boolean bit, and,
   for ease of presentation the code. *)

val _ = type_abbrev ("core_state", 
  ``: (word4 -> word32) #     (* registers, including program counter (reg 15) *)
      bool #                  (* one status bit, similar to N, Z, C, V *) 
      (word32 -> instruction) (* code: mapping from addresses to instructions *) ``);

(* The memory is intuitively a mapping from word32 -> word32, the memory
   is kept separate from the state of the processor's core. *)

(* Instead of updating memory directly the core produces a list of memory 
   accesses. The type of memory access is: *)

val _ = Hol_datatype `memory_access = 
  MEM_READ of word32 | MEM_WRITE of word32 => word32`;

(* i.e. each instruction execution returns an output of type 
   memory_access list *)


(* -------------------------------------------------------------------------- *)
(*  Next-state function                                                       *)
(* -------------------------------------------------------------------------- *)

val INC_PC_def = Define `INC_PC offset r = (15w =+ r 15w + offset) r`;

val NO_MEMORY_ACCESS_def = Define `
  NO_MEMORY_ACCESS (s:core_state) = (s,[]:memory_access list)`;

val ATTACH_MEMORY_ACCESS_def = Define `
  ATTACH_MEMORY_ACCESS (s:core_state) (xs:memory_access list) = (s,xs)`;

(* The next state funtion returns a new core state and a list of memory 
   accesses. Note that no instruction updates the input memory m, instead
   the peripherals outside of the core are responsible for updating 'm'
   based on the list of memory accesses produced by NEXT. *)

val NEXT_INST_def = Define `
  (NEXT_INST (iB offset) (r,b,c) m = 
     let new_r = INC_PC offset r in
       NO_MEMORY_ACCESS (new_r,b,c)) /\
  (NEXT_INST (iBCC offset) (r,b,c) m = 
     let new_r = INC_PC (if b then offset else 4w) r in
       NO_MEMORY_ACCESS (new_r,b,c)) /\
  (NEXT_INST (iREG z x y f) (r,b,c) m = 
     let new_r = (z =+ (f (r x) (r y))) (INC_PC 4w r) in
       NO_MEMORY_ACCESS (new_r,b,c)) /\
  (NEXT_INST (iCMP x y g) (r,b,c) m = 
     let new_b = g (r x) (r y) in
       NO_MEMORY_ACCESS (INC_PC 4w r,new_b,c)) /\
  (NEXT_INST (iLDR x (y,offset)) (r,b,c) m = 
     let new_r = (x =+ m (r y + offset)) (INC_PC 4w r) in
       ATTACH_MEMORY_ACCESS (new_r,b,c) [MEM_READ (r y + offset)]) /\
  (NEXT_INST (iSTR x (y,offset)) (r,b,c) m = 
     let new_r = INC_PC 4w r in
       ATTACH_MEMORY_ACCESS (new_r,b,c) [MEM_WRITE (r y + offset) (r x)])`;

val NEXT_def = Define `
  NEXT (r,b,c) m = NEXT_INST (c (r 15w)) (r,b,c) m`;


val _ = export_theory();
