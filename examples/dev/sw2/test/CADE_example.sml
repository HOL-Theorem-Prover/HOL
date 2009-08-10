(*
use "prelim";
*)

(*---------------------------------------------------------------------------*)
(* This example demonstrates how the compiler works step by step.            *)
(* It is the one given in the CADE-21 paper.                                 *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Source programs.                                                          *)
(*---------------------------------------------------------------------------*)

val fact_def = Define
   `fact i = if i = 0 then 1 else i * fact (i - 1)`;

val f1_def = Define
   `f1 (k0,k1,k2)  =
        let y = k2 + 100 in
        let g = (\(x,y). y - (x * k0)) in
        let z = if fact 3 < 10 /\ y + 2 * k1 > k0 then g (k1, k2)
                else y
        in
        z * y`;

(*****************************************************************************)
(* Front End                                                                 *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Normalization and optimization of the normal forms.                       *)
(*---------------------------------------------------------------------------*)

val lem1 = SSA_RULE (SIMP_RULE std_ss [Once LET_THM] (normalize fact_def));

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

val lem2 = SSA_RULE (normalize f1_def);

(*
|- f1 =
       (\(v1,v2,v3).
          (let v4 = v3 + 100 in
           let v5 (v13,v14) =
                 (let v15 = v1 * v13 in let v16 = v14 - v15 in v16)
           in
           let v6 = fact 3 in
           let v7 =
                 (if 10 <= v6 then
                    v4
                  else
                    (let v9 = 2 * v2 in
                     let v10 = v9 + v4 in
                     let v11 =
                           (if v10 <= v1 then
                              v4
                            else
                              (let v12 = v5 (v2,v3) in v12))
                     in
                       v11))
           in
           let v8 = v4 * v7 in
             v8))
*)

val env = [lem1];
val th1 = SSA_RULE (optimize_norm env lem2);
(*
 |- f1 =
       (\(v1,v2,v3).
          (let v4 = v3 + 100 in
           let v5 (v11,v12) =
                 (let v13 = v1 * v11 in let v14 = v12 - v13 in v14)
           in
           let v6 = 2 * v2 in
           let v7 = v4 + v6 in
           let v8 = (if v7 <= v1 then v4 else (let v10 = v5 (v2,v3) in v10))
           in
           let v9 = v4 * v8 in
             v9))

*)

(*---------------------------------------------------------------------------*)
(* Closure Conversion and subsequent optimization                            *)
(*---------------------------------------------------------------------------*)

val th2 = closure_convert th1;
(*
 |- f1 =
       (\(v1,v2,v3).
          (let v4 =
                 fun
                   (\v11 (v12,v13).
                      (let v14 = v11 * v12 in let v15 = v13 - v14 in v15))
           in
           let v5 = v3 + 100 in
           let v6 = 2 * v2 in
           let v7 = v5 + v6 in
           let v8 =
                 (if v7 <= v1 then v5 else (let v10 = v4 v1 (v2,v3) in v10))
           in
           let v9 = v5 * v8 in
             v9))
*)

val th3 = SSA_RULE (optimize_norm []
                     (SIMP_RULE std_ss [Once LET_THM, NormalTheory.fun_def] th2));

(*
 |- f1 =
       (\(v1,v2,v3).
          (let v4 = v3 + 100 in
           let v5 = 2 * v2 in
           let v6 = v4 + v5 in
           let v7 =
                 (if v6 <= v1 then
                    v4
                  else
                    (let v9 = v1 * v2 in let v10 = v3 - v9 in v10))
           in
           let v8 = v4 * v7 in
             v8))
*)

(*---------------------------------------------------------------------------*)
(* Register Allocation                                                       *)
(*---------------------------------------------------------------------------*)

regAlloc.numRegs := 3;             (* this causes the spilling to occur *)
val th4 = reg_alloc th3;

(*
    |- f1 =
       (\(r0,r1,r2).
          (let m1 = r0 in
           let r0 = r2 + 100 in
           let m2 = r0 in
           let r0 = 2 * r1 in
           let m3 = r1 in
           let r1 = m2 in
           let r0 = r1 + r0 in
           let r1 = m1 in
           let r0 =
                 (if r0 <= r1 then
                    (let r0 = m2 in r0)
                  else
                    (let r0 = m3 in
                     let r0 = r1 * r0 in
                     let r0 = r2 - r0 in
                       r0))
           in
           let r1 = m2 in
           let r0 = r1 * r0 in
             r0)) : thm
*)

regAlloc.numRegs := 5;        (* no spilling is needed *)
val th5 = reg_alloc th3;

(*
  |- f1 =
       (\(r0,r1,r2).
          (let r3 = r2 + 100 in
           let r4 = 2 * r1 in
           let r4 = r3 + r4 in
           let r0 =
                 (if r4 <= r0 then
                    r3
                  else
                    (let r0 = r0 * r1 in let r0 = r2 - r0 in r0))
           in
           let r0 = r3 * r0 in
             r0)) : thm
*)

(*****************************************************************************)
(* Front End                                                                 *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Generating code in Structured Assembly Language (SAL)                     *)
(*---------------------------------------------------------------------------*)

(* First try the one without spilling *)

val sal_1 = certified_gen th5;
printSAL (#code sal_1);

(*
 val sal_1 =
    {code = ... (see below )
     thm =
       |- Reduce
            (L 1,
             ASG (L 1) r3 (r2 + 100) (L 3) |++|
             (ASG (L 3) r4 (2 * r1) (L 4) |++|
              (ASG (L 4) r4 (r3 + r4) (L 5) |++|
               (IFGOTO (L 5) (\r0. r4 <= r0) (L 7) (L 8) |++|
                ASG (L 7) r0 r3 (L 6) |++|
                (ASG (L 8) r0 (r0 * r1) (L 9) |++|
                 ASG (L 9) r0 (r2 - r0) (L 6)) |++|
                ASG (L 6) r0 (r3 * r0) (L 2)))),L 2)
            ((let r3 = r2 + 100 in
              let r4 = 2 * r1 in
              let r4 = r3 + r4 in
              let r0 = (if r4 <= r0 then r3 else (let r0 = r0 * r1 in r2 - r0))
              in
                r3 * r0),r0)} : {code : term, thm : thm}

    l1:   r3 := r2 + 100  (goto l3)
    l3:   r4 := 2 * r1  (goto l4)
    l4:   r4 := r3 + r4  (goto l5)
    l5:   ifgoto r4 <= r0 l7 l8
    l7:   r0 := r3  (goto l6)
    l8:   r0 := r0 * r1  (goto l9)
    l9:   r0 := r2 - r0  (goto l6)
    l6:   r0 := r3 * r0  (goto l2)
*)

(*  Then try the spilling one *)

val sal_2 = certified_gen th4;
printSAL (#code sal_2);

(*
> val sal_2 =
    {code = ...
     thm =
       |- Reduce
            (L 1,
             ASG (L 1) m1 r0 (L 3) |++|
             (ASG (L 3) r0 (r2 + 100) (L 4) |++|
              (ASG (L 4) m2 r0 (L 5) |++|
               (ASG (L 5) r0 (2 * r1) (L 6) |++|
                (ASG (L 6) m3 r1 (L 7) |++|
                 (ASG (L 7) r1 m2 (L 8) |++|
                  (ASG (L 8) r0 (r1 + r0) (L 9) |++|
                   (ASG (L 9) r1 m1 (L 10) |++|
                    (IFGOTO (L 10) (\r1. r0 <= r1) (L 12) (L 13) |++|
                     ASG (L 12) r0 m2 (L 11) |++|
                     (ASG (L 13) r0 m3 (L 15) |++|
                      (ASG (L 15) r0 (r1 * r0) (L 16) |++|
                       ASG (L 16) r0 (r2 - r0) (L 11))) |++|
                     (ASG (L 11) r1 m2 (L 18) |++|
                      ASG (L 18) r0 (r1 * r0) (L 2)))))))))),L 2)
            ((let m1 = r0 in
              let r0 = r2 + 100 in
              let m2 = r0 in
              let r0 = 2 * r1 in
              let m3 = r1 in
              let r1 = m2 in
              let r0 = r1 + r0 in
              let r1 = m1 in
              let r0 =
                    (if r0 <= r1 then
                       m2
                     else
                       (let r0 = m3 in let r0 = r1 * r0 in r2 - r0))
              in
              let r1 = m2 in
                r1 * r0),r0)} : {code : term, thm : thm}

    l1:   m1 := r0  (goto l3)
    l3:   r0 := r2 + 100  (goto l4)
    l4:   m2 := r0  (goto l5)
    l5:   r0 := 2 * r1  (goto l6)
    l6:   m3 := r1  (goto l7)
    l7:   r1 := m2  (goto l8)
    l8:   r0 := r1 + r0  (goto l9)
    l9:   r1 := m1  (goto l10)
    l10:  ifgoto r0 <= r1 l12 l13
    l12:  r0 := m2  (goto l11)
    l13:  r0 := m3  (goto l15)
    l15:  r0 := r1 * r0  (goto l16)
    l16:  r0 := r2 - r0  (goto l11)
    l11:  r1 := m2  (goto l18)
    l18:  r0 := r1 * r0  (goto l2)

*)
