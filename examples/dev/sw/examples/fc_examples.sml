(*---------------------------------------------------------------------------*)
(*   Simple examples involving function calls                                *)
(*---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------*)
(*   This is the example 3 in the paper                                      *)
(*---------------------------------------------------------------------------*)

val def1 = Define `f1 (x:word32) = x + x + 1w`;

(*
- val spec = pp_compile def1;

|- !st.
          (\(regs,mem). (regs ' 11 = 100w) /\ (regs ' 13 = 100w)) st ==>
          (get_st
             (run_arm
                [((ADD,NONE,F),SOME (REG 0),[REG 0; REG 0],NONE);
                 ((ADD,NONE,F),SOME (REG 0),[REG 0; WCONST 1w],NONE)]
                ((0,0w,st),{}))<MR R0> =
           f1 (st<MR R0>)))

- extract_ir spec;

  Name              : f1
  Arguments         : r0
  Returns           : r0
  Body:
	[madd r0 r0 r0; madd r0 r0 #1w]

*)


val def2 = Define `f2 x = x * f1 x`;

(*
- init_sp := 100;
- val spec = pp_compile def2;

 |- !st.
      (\(regs,mem). (regs ' 11 = 100w) /\ (regs ' 13 = 100w)) st ==>
      (get_st
         (run_arm
            [((SUB,NONE,F),SOME (REG 13),[REG 13; WCONST 1w],NONE);
             ((STR,NONE,F),SOME (REG 0),[MEM (13,POS 0)],NONE);
             ((SUB,NONE,F),SOME (REG 13),[REG 13; WCONST 1w],NONE);
             ((MOV,NONE,F),SOME (REG 12),[REG 13],NONE);
             ((STMFD,NONE,F),SOME (WREG 13),
                [REG 0; REG 11; REG 12; REG 14; REG 15],NONE);
             ((SUB,NONE,F),SOME (REG 11),[REG 12; WCONST 1w],NONE);
             ((LDR,NONE,F),SOME (REG 0),[MEM (12,POS 1)],NONE);
             ((ADD,NONE,F),SOME (REG 12),[REG 12; WCONST 1w],NONE);
             ((ADD,NONE,F),SOME (REG 0),[REG 0; REG 0],NONE);
             ((ADD,NONE,F),SOME (REG 0),[REG 0; WCONST 1w],NONE);
             ((ADD,NONE,F),SOME (REG 13),[REG 11; WCONST 3w],NONE);
             ((STR,NONE,F),SOME (REG 0),[MEM (13,POS 0)],NONE);
             ((SUB,NONE,F),SOME (REG 13),[REG 13; WCONST 1w],NONE);
             ((LDR,NONE,F),SOME (REG 1),[MEM (13,POS 1)],NONE);
             ((ADD,NONE,F),SOME (REG 13),[REG 13; WCONST 1w],NONE);
             ((SUB,NONE,F),SOME (REG 13),[REG 11; WCONST 4w],NONE);
             ((LDMFD,NONE,F),SOME (WREG 13),
                 [REG 0; REG 11; REG 13; REG 15],NONE);
             ((MUL,NONE,F),SOME (REG 0),[REG 0; REG 1],NONE)]
            ((0,0w,st),{}))<MR R0> =
       f2 (st<MR R0>)))

- extract_ir spec;

  Name              : f2
  Arguments         : r0
  Returns           : r0
  Body:
  SC(
    SC(
      [msub sp sp #1w; mstr [sp] r0; msub sp sp #1w; mmov ip sp; mpush sp {r0,fp,ip,lr,pc}; msub fp ip #1w; mldr r0 [ip, #1]; madd ip ip #1w],
      SC(
        [madd r0 r0 r0; madd r0 r0 #1w],
        [madd sp fp #3w; mstr [sp] r0; msub sp sp #1w; mldr r1 [sp, #1]; madd sp sp #1w; msub sp fp #4w; mpop sp {r0,fp,sp,pc}])),
    [mmul r0 r0 r1])

- extract_arm spec;

  Name              : f2
  Arguments         : r0
  Returns           : r0
  Body:
    0:          sub     sp, sp, #1iw
    1:          str     r0, [sp]
    2:          sub     sp, sp, #1iw
    3:          mov     ip, sp
    4:          stmfd   sp!, {r0,fp,ip,lr,pc}
    5:          sub     fp, ip, #1iw
    6:          ldr     r0, [ip, #1]
    7:          add     ip, ip, #1iw
    8:          add     r0, r0, r0
    9:          add     r0, r0, #1iw
   10:          add     sp, fp, #3iw
   11:          str     r0, [sp]
   12:          sub     sp, sp, #1iw
   13:          ldr     r1, [sp, #1]
   14:          add     sp, sp, #1iw
   15:          sub     sp, fp, #4iw
   16:          ldmfd   sp!, {r0,fp,sp,pc}
   17:          mul     r0, r0, r1

*)
