(*
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory combinTheory addressTheory;
open arm_compilerLib;

val _ = new_theory "decompiler_demo";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

(* 

INTRODUCTION

This file illustrates how the ARM decompiler from arm_compilerLib 
can be used in verification of examples pieces of code.

*)


(* example: factorial function --------- *)

val (def,th) = arm_decompiler "fac" `T` NONE ["r1"] [
"cmp   r1,#0",
"mulne r2,r1,r2",
"subne r1,r1,#1",
"bne   -12"]


(* example: mod 10 --------- *)

val termination_tac = SOME
 (WF_REL_TAC `measure w2n` \\ Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,n2w_11,w2n_n2w,
       LESS_MOD,ZERO_LT_dimword,addressTheory.word_arith_lemma2]
  \\ REPEAT STRIP_TAC \\ `n - 10 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC)

val (def,th) = arm_decompiler "mod10" `T` termination_tac [] [
"cmp   r1,#10",
"subcs r1,r1,#10",
"bcs   -8"]


(* example: simple division --------- *)

val termination_tac = SOME
 (WF_REL_TAC `measure (w2n o FST o SND)` \\ Cases_word \\ Cases_word
  \\ ASM_SIMP_TAC bool_ss [WORD_LO,n2w_11,w2n_n2w,LESS_MOD,ZERO_LT_dimword]
  \\ `n - n' < dimword (:32)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [addressTheory.word_arith_lemma2,w2n_n2w,LESS_MOD] 
  \\ DECIDE_TAC)

val (def,th) = arm_decompiler "div" `~(r2 = 0w)` termination_tac [] [
"cmp   r1,r2",
"addcs r0,r0,#1",
"subcs r1,r1,r2",
"bcs   -12"]


(* example: length of linked-list --------- *)

val llist_def = Define `
  (llist [] (a:word32,m:word32->word32) = (a = 0w)) /\
  (llist (x::xs) (a,m) = ~(a = 0w) /\ (x = m (a + 4w)) /\ llist xs (m a,m))`;

val llist_SELECT = prove(
  ``!xs a m. llist xs (a,m) ==> 
      ((@n. ?xs. llist xs (a,m) /\ (LENGTH xs = n)) = LENGTH xs)``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SELECT_UNIQUE \\ SIMP_TAC std_ss []
  \\ STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THENL [ALL_TAC,METIS_TAC []]
  \\ Q.PAT_ASSUM `LENGTH xs' = y` (fn th => REWRITE_TAC [GSYM th])    
  \\ Q.UNDISCH_TAC `llist xs (a,m)` \\ Q.UNDISCH_TAC `llist xs' (a,m)`
  \\ Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`xs'`,`ys`)
  \\ Induct_on `xs`
  THEN1 (Cases \\ SIMP_TAC bool_ss [llist_def])
  \\ STRIP_TAC \\ Cases \\ ASM_SIMP_TAC bool_ss [llist_def,LENGTH] \\ METIS_TAC []);

val termination_tac = SOME
 (WF_REL_TAC `measure (\(r0,r1,x,xs). @n. ?ys. llist ys (r1,xs) /\ (LENGTH ys = n))`
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC llist_SELECT
  \\ Cases_on `ys` 
  \\ FULL_SIMP_TAC bool_ss [llist_def]
  \\ IMP_RES_TAC llist_SELECT
  \\ FULL_SIMP_TAC bool_ss [LENGTH,WORD_ADD_0]
  \\ DECIDE_TAC);

val (def,th) = arm_decompiler "length" `?ys. llist ys (r1,xs)` termination_tac [] [
"cmp   r1,#0",
"ldrne r1,[r1]",
"addne r0,r0,#1",
"bne   -12"]

val length_spec = prove(
  ``!ys r0 r1 x xs. 
      llist ys (r1,xs) ==> (length(r0,r1,x,xs) = (r0 + n2w (LENGTH ys),0w))``,
  Induct \\ ONCE_REWRITE_TAC [def] \\ REPEAT STRIP_TAC
  \\ `(?ys. llist ys (r1,xs)) = T` by METIS_TAC [] \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [llist_def,WORD_ADD_0,LET_DEF,LENGTH]
  \\ REWRITE_TAC [RW1 [ADD_COMM] ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]);


(*

(* Evaluation of the following may take a few minutes. *)

val (def,th) = arm_decompiler "test" `T` NONE [] [
"e24cb004",
"e24dd03c",
"e50b0010",
"e50b1014",
"e50b2018",
"e50b301c",
"e51b3014",
"e3530000",
"1a000002",
"e51b3018",
"e50b3048",
"ea000013",
"e51b3014",
"e3530001",
"1a000002",
"e51b301c",
"e50b3048",
"ea00000d",
"e51b3014",
"e3530002",
"1a000002",
"e59b3004",
"e50b3048",
"ea000007",
"e51b3014",
"e3530003",
"1a000002",
"e59b3008",
"e50b3048",
"ea000001",
"e24b3044",
"e50b3048",
"e51b1010",
"e59f303c",
"e0c32391",
"e1a02143",
"e1a03fc1",
"e0632002",
"e1a03002",
"e1a03103",
"e0833002",
"e1a03083",
"e0633001",
"e1a02103",
"e51b3048",
"e0822003",
"e3a0300c",
"e5823000",
"e24bd00c"]

(*
   Notice that th holds a certificate that the function `test` is 
   executed by the code you gave it.
 
   You can get hold of the definition of test by: fetch "-" "test_def"
   
   The correct exeution of `test(...)` is only valid if `test_pre(...)`
   is true before the code is executed. You can get hold of the definition 
   of test_pre by typing: fetch "-" "test_pre_def"
 
   By the way in this case `test_pre(r1,r2,r3,r11,r13,x,xs)` makes a 
   condition on `x` which keeps track of which memory locations are 
   used by the program.
*)

*)

val _ = export_theory();

