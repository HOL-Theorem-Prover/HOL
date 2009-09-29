
open HolKernel boolLib bossLib Parse;
open wordsTheory;

val _ = new_theory "toy_core2";


(* -------------------------------------------------------------------------- *)
(*  Type definitions                                                          *)
(* -------------------------------------------------------------------------- *)

(* This theroy defines a toy processor core which handles the 
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

(* The state of the core consists of 16 registers, a boolean bit, and,
   for ease of presentation, the code separate from the memory. *)

val _ = type_abbrev ("core_state", 
  ``: (word4 -> word32) #       (* registers, including program counter (reg 15) *)
      bool #                    (* one status bit, similar to N, Z, C, V *) 
      (word32 -> instruction) # (* code: mapping from addresses to instructions *) 
      (word32 -> word32 # bool # bool) (* memory, see below *)``);

(* The memory is intuitively a mapping from word32 -> word32, the memory
   is kept separate from the state of the processor's core. As far as NEXT 
   is concerned memory is a mapping of type:

     word32 -> word32 # bool # bool

   The two extra bool parts indicate whether there was a read or a
   write, repsectively, to this location. So for memory m and address a 

     m a = (5w,F,F),  if address a was neither read nor written
     m a = (5w,T,F),  if address a was read, but not written
     m a = (1w,F,T),  if address a was not read, 1w was written to it
     m a = (1w,T,T),  if address a was read, then 1w was written to it

   Initally m will always be such that: !a. ?w. m a = (w,F,F)
*)


(* -------------------------------------------------------------------------- *)
(*  Next-state function                                                       *)
(* -------------------------------------------------------------------------- *)

val INC_PC_def = Define `INC_PC offset r = (15w =+ r 15w + offset) r`;

(* MEM_READ tags the approriate memory location, and returns the data content *)

val MEM_READ_def = Define `
  MEM_READ a m = let (w,x,y) = m a in ((a =+ (w,T,y)) m, w)`;

(* MEM_WRITE tags and updates the content of the approriate memory location *)

val MEM_WRITE_def = Define `
  MEM_WRITE a v m = let (w,x,y) = m a in (a =+ (v,x,T)) m`;

(* The next state funtion returns a new core state. *)

val NEXT_INST_def = Define `
  (NEXT_INST (iB offset) ((r,b,c,m):core_state) = 
     let new_r = INC_PC offset r in
       ((new_r,b,c,m):core_state)) /\
  (NEXT_INST (iBCC offset) (r,b,c,m) = 
     let new_r = INC_PC (if b then offset else 4w) r in
       (new_r,b,c,m)) /\
  (NEXT_INST (iREG z x y f) (r,b,c,m) = 
     let new_r = (z =+ (f (r x) (r y))) (INC_PC 4w r) in
       (new_r,b,c,m)) /\
  (NEXT_INST (iCMP x y g) (r,b,c,m) = 
     let new_b = g (r x) (r y) in
     let new_r = INC_PC 4w r in
       (new_r,new_b,c,m)) /\
  (NEXT_INST (iLDR x (y,offset)) (r,b,c,m) = 
     let (new_m,w) = MEM_READ (r y + offset) m in
     let new_r = (x =+ w) (INC_PC 4w r) in
       (new_r,b,c,new_m)) /\
  (NEXT_INST (iSTR x (y,offset)) (r,b,c,m) = 
     let new_m = MEM_WRITE (r y + offset) (r x) m in
     let new_r = INC_PC 4w r in
       (new_r,b,c,new_m))`;

val NEXT_def = Define `
  NEXT (r,b,c,m) = NEXT_INST (c (r 15w)) (r,b,c,m)`;


val _ = export_theory();
