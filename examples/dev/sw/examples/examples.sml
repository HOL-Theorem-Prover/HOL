(*---------------------------------------------------------------------------------*)
(*      Simple Examples                                                            *) 
(*      No precedure call is presented in these examples                           *)
(*---------------------------------------------------------------------------------*)

use "compiler";

use "mechReasoning";

(*---------------------------------------------------------------------------------*)
(*      Single Blocks                                                              *)
(*      The ShiftXor procedure appearing in TEA                                    *)
(*---------------------------------------------------------------------------------*)

val ShiftXor_def =
 Define
   `ShiftXor (x,s,k0,k1) = ((x << 4) + k0) # (x + s) # ((x >> 5) + k1)`;

(*
 pp_compile ShiftXor_def;

|- !st.
          get_st
            (run_arm
               [((LSL,NONE,F),SOME (REG 4),[REG 0; WCONST 4w],NONE);
                ((ADD,NONE,F),SOME (REG 2),[REG 4; REG 2],NONE);
                ((ADD,NONE,F),SOME (REG 1),[REG 0; REG 1],NONE);
                ((EOR,NONE,F),SOME (REG 1),[REG 2; REG 1],NONE);
                ((ASR,NONE,F),SOME (REG 0),[REG 0; WCONST 5w],NONE);
                ((ADD,NONE,F),SOME (REG 0),[REG 0; REG 3],NONE);
                ((EOR,NONE,F),SOME (REG 0),[REG 1; REG 0],NONE)]
               ((0,0w,st),{}))<MR R0> =
          ShiftXor (st<MR R0>,st<MR R1>,st<MR R2>,st<MR R3>))
*)

(*---------------------------------------------------------------------------------*)
(*      Single Conditional Jump                                                    *)
(*---------------------------------------------------------------------------------*)

val f1_def = Define `
    f1 (a,b) = if a = 1w then b else a + b`;

(*
 pp_compile f1_def;

|- !st.
          get_st
            (run_arm
               [((CMP,NONE,F),NONE,[REG 0; WCONST 1w],NONE);
                ((B,SOME EQ,F),NONE,[],SOME (POS 3));
                ((ADD,NONE,F),SOME (REG 1),[REG 0; REG 1],NONE);
                ((B,SOME AL,F),NONE,[],SOME (POS 1))]
               ((0,0w,st),{}))<MR R1> =
          f1 (st<MR R0>,st<MR R1>))

*)

(*---------------------------------------------------------------------------------*)
(*      Tail Recusive Functions                                                    *)
(*      Factorial Function. Form: SC (TR, BLK)                                     *) 
(*---------------------------------------------------------------------------------*)

val fact_def = Define `
   fact (x:DATA,a) = if x=0w then a else fact(x-1w,x*a)`;

val fact_thm = Q.store_thm (
   "fact_thm",
   `fact = (\(x,a).a) o (WHILE ($~ o (\(x,a).x = 0w)) (\(x,a).(x-1w,x*a)))`,
   SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD] THEN
   HO_MATCH_MP_TAC (fetch "-" "fact_ind") THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [fact_def, WHILE] THEN
   RW_TAC std_ss []
  );

(*
  val spec0 = get_spec fact_def;
  val spec1 = SIMP_RULE std_ss [GSYM fact_thm] spec0;
  val spec2 = f_correct spec1;

   |- !st.
         get_st
           (run_arm
              [((CMP,NONE,F),NONE,[REG 0; WCONST 0w],NONE);
               ((B,SOME EQ,F),NONE,[],SOME (POS 6));
               ((SUB,NONE,F),SOME (REG 3),[REG 0; WCONST 1w],NONE);
               ((MUL,NONE,F),SOME (REG 2),[REG 0; REG 1],NONE);
               ((MOV,NONE,F),SOME (REG 0),[REG 3],NONE);
               ((MOV,NONE,F),SOME (REG 1),[REG 2],NONE);
               ((B,SOME AL,F),NONE,[],SOME (NEG 6));
               ((MOV,NONE,F),SOME (REG 2),[REG 1],NONE)]
              ((0,0w,st),{}))<MR R2> =
         fact (st<MR R0>,st<MR R1>) 
*)

(*---------------------------------------------------------------------------------*)
(*      Sequential Compositions                                                    *)
(*      This example has the form SC (BLK, CJ)                                     *)
(*---------------------------------------------------------------------------------*)

val f2_def = Define `
    f2 (a,b) = let c = a + 1w in
               if a = 1w then c else c + b`;

(*
 pp_compile f2_def;

 |- !st.
          get_st
            (run_arm
               [((ADD,NONE,F),SOME (REG 2),[REG 0; WCONST 1w],NONE);
                ((CMP,NONE,F),NONE,[REG 0; WCONST 1w],NONE);
                ((B,SOME EQ,F),NONE,[],SOME (POS 3));
                ((ADD,NONE,F),SOME (REG 2),[REG 2; REG 1],NONE);
                ((B,SOME AL,F),NONE,[],SOME (POS 1))]
               ((0,0w,st),{}))<MR R2> =
          f2 (st<MR R0>,st<MR R1>))
*)




(* A more complicated SC example.  Form: SC (BLK, SC (CJ, BLK))         *)
(* The ANF conversion seems wrong ???                                   *)

val f3_def = Define `
    f3 (a,b) = let c = a + 1w in
               let d = if a = 1w then b else a + b in
               let e = c - d in
               e 
`;

(*
*)

