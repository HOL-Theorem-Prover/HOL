
app load ["NormalTheory", "Normal", "basic"];
open HolKernel Parse boolLib bossLib;
open pairLib pairSyntax PairRules NormalTheory Normal basic;

use "regAlloc.sml";
open regAlloc;

(*---------------------------------------------------------------------------*)
(* Test case 1: The factorial function.                                      *)
(*---------------------------------------------------------------------------*)

val fact_def = Define
   `fact i = if i = 0 then 1 else i * fact (i - 1)`;

val def = SSA_RULE (SIMP_RULE std_ss [Once LET_THM] (normalize fact_def));

(*
 |- fact =
       (\v1.
          (if v1 = 0 then
             1
           else
             (let v2 = v1 - 1 in
              let v3 = fact v2 in
              let v4 = v1 * v3 in
                v4)))
*)

reg_alloc def;

(*
 |- fact =
       (\r0.
          (if r0 = 0 then
             1
           else
             (let r1 = r0 - 1 in
              let r1 = fact r1 in
              let r0 = r0 * r1 in
                r0))) : thm
*)


(*---------------------------------------------------------------------------*)
(* Test case 2: Simple functions for testing spilling.                       *)
(*---------------------------------------------------------------------------*)

numRegs := 2;

val def1 = Define
   `f1 = \(v1:word32,v2:word32). 
     let (v3,v4,v5) = (v1,v2,v1) in (v1,v3,v5)`;

val def2 = Define `
    f2 = \(v1,v2,v3:word32).
      let (v4,v5,v6) = f1(v1,v2) in
      (v5,v3)`;

val def3 = Define  `
    f3 = \(v1:word32,v2:word32).
     let v3 = v1 + v2 in
     let v4 = v1 - v3 in
     let v5 = v2 * v3 in
     (v1,v2,v3,v4,v5)`;

val def4 = Define  `
    f4 = \(v1:word32,v2:word32,v3:word32,v4:word32).
     let v5 = v3 + v4 in
     (v1,v2,v3,v4,v5)`;

val def5 = Define  `
    f5 = \(v1:word32,v2:word32).
     let v3 = v1 + v2 in
     let v4 = v2 - v3 in
     (v1,v2,v3,v4)`;

val def6 = Define  `
    f6 = \(v1:word32,v2:word32,v3:word32).
     let (v3,v4) = f2 (v1,v2,v3) in
     let (v5,v6,v7) = (v1,v3,v4) in
     let (v8,v9,v10) = (v2,v2,v1) in
     v5`;

val def7 = Define  `
    f7 = \(v1:word32).
     let (v3,v4) = f2 (v1,v1,v1) in
     let (v5,v6,v7) = (v1,v1,v3) in
     let (v8,v9,v10) = (v1,v1,v1) in
     v1`;

(*
reg_alloc def;
*)
