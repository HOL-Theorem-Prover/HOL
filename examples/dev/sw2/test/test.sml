use "prelim";

(* --------------------------------------------------------------------------*)
(*	Test the pre-processing and normalization     	                     *)
(* --------------------------------------------------------------------------*)

val f1_def = Define 
   `f1 (x,s,k0,k1) = (x + k0) * (x + s) * (x + k1)`;

val f2_def = 
 Define
   `f2 ((y,z),(k0,k1,k2,k3),sum)  = 
	let sum1 = sum + 100 in
	let v1 = if y > z \/ y + 2 * k0 > z then y + f1 (z, sum1 * 4, k0, k1) 
          else z + f1 (y, sum1, k2 - y, k3)
        in
	v1 + sum1`;

(*
val th1 = normalize f2_def;

 |- f2 ((y,z),(k0,k1,k2,k3),sum) =
       (let sum1 = sum + 100 in
        let x = 4 * sum1 in
        let y1 = f1 (z,x,k0,k1) in
        let x = y + y1 in
        let z =
              (if y <= z then
                 (let x1 = 2 * k0 in
                  let p = x1 + y in
                  let z =
                        (if p <= z then
                           (let x = k2 - y in
                            let y1 = f1 (y,sum1,x,k3) in
                            let y = z + y1 in
                              y)
                         else
                           x)
                  in
                    z)
               else
                 x)
        in
        let y = sum1 + z in
          y)
*)

(*---------------------------------------------------------------------------*)
(* Test the simplications on normal forms                                    *)
(* The SSA form transformation                                               *)
(*---------------------------------------------------------------------------*)

(*
val th2 = SSA_RULE th1;
 |- f2 =
       (\((v1,v2),(v3,v4,v5,v6),v7).
          (let v8 = v7 + 100 in
           let v9 = 4 * v8 in
           let v10 = f1 (v2,v9,v3,v4) in
           let v11 = v1 + v10 in
           let v12 =
                 (if v1 <= v2 then
                    (let v14 = 2 * v3 in
                     let v15 = v14 + v1 in
                     let v16 =
                           (if v15 <= v2 then
                              (let v17 = v5 - v1 in
                               let v18 = f1 (v1,v8,v17,v6) in
                               let v19 = v2 + v18 in
                                 v19)
                            else
                              v11)
                     in
                       v16)
                  else
                    v11)
           in
           let v13 = v8 + v12 in
             v13))
*)

(*---------------------------------------------------------------------------*)
(* Optimization on Normal Forms:                                             *)
(*   1. SSA forms                                                            *)
(*   2. Inline expansion                                                     *)
(*   3. Simplification of let-expressions (atom_let, flatten_let, useless_let*)
(*   4. Constant folding                                                     *)
(*   5. Beta-reduction (a special case of constant folding)                  *)
(*---------------------------------------------------------------------------*)

(* Inline expansion of anonymous functions                                   *)

val f3_def = Define
   `f3 (k0,k1,k2,k3)  =
        let k4 = k0 + 100 in
        let k5 = (\(x,y). let k6 = x + k1 in k2 * k6) in
        let k7 = k5 (k3,k2) in
        let k8 = k5 in
        let k9 = k8 (k7,k4) in
         k9`;

(* 
- inline.expand_anonymous f3_def;
> val it =
    |- !k0 k1 k2 k3.
         f3 (k0,k1,k2,k3) =
         (let k4 = k0 + 100 in
          let k7 = (let k6 = k3 + k1 in k2 * k6) in
          let k9 = (let k6 = k7 + k1 in k2 * k6) in
            k9) : thm
*)    

(* Inline expansion of named functions stored in env                         *)

val g1_def = Define `g1 (k0,k1) = let k2 = k0 + k1 in k2 * 15`;

(* factorial function *)

val g2_def = Define `
    g2 k0 = 
    if k0 = 0 then 1 else 
      let k1 = k0 - 1 in 
      let k2 = g2 k1 in
      k0 * k2`;

val g3_def = Define `
    g3 (k0,k1,k2) = 
       let k3 = g1 (k0, k1) in 
       let k4 = k2 * k0 in
       let k5 = g2 2 in
       k5 - k4`;

val env = [g1_def, g2_def];

(*
- inline.expand_named env g3_def;
> val it =
    |- !k0 k1 k2.
         g3 (k0,k1,k2) =
         (let k3 = (let k2 = k0 + k1 in k2 * 15) in
          let k4 = k2 * k0 in
          let k5 =
                (if 2 = 0 then
                   1
                 else
                   (let k1 = 2 - 1 in
                    let k2 =
                          (if k1 = 0 then
                             1
                           else
                             (let k11 = k1 - 1 in
                              let k2 =
                                    (if k11 = 0 then
                                       1
                                     else
                                       (let k1 = k11 - 1 in
                                        let k2 =
                                              (if k1 = 0 then
                                                 1
                                               else
                                                 (let k11 = k1 - 1 in
                                                  let k2 = g2 k11 in
                                                    k1 * k2))
                                        in
                                          k11 * k2))
                              in
                                k1 * k2))
                    in
                      2 * k2))
          in
            k5 - k4) : thm
*)

(* Optimization on Normal Forms, including inline expansion and 
   other optimizations *)

(*
- optimize_norm env g3_def;
> val it =
    |- g3 =
       (\(v1,v2,v3).
          (let k2 = v1 + v2 in
           let v4 = 15 * k2 in
           let v5 = v1 * v3 in
             2 - v5)) : thm
*)

(*---------------------------------------------------------------------------*)
(* Closure Conversion                                                        *)
(*---------------------------------------------------------------------------*)

val f4_def = Define `
   f4 (k0,k1,k2,k3) =
     let k5 = (\x. let k6 = x + k1 in k2 * k6) in
     let k7 = k5 k3 in
     k7`;

(*
- closure.close_one_by_one f4_def;
> val it =
    |- f4 =
       (\(k0,k1,k2,k3).
          (let k5 = fun (\k2 k1 x. (let k6 = x + k1 in k2 * k6)) in
           let k7 = k5 k2 k1 k3 in
             k7)) : thm
*)

val f5_def = Define
   `f5 (k0,k1,k2,k3)  =
        let k4 = k0 + 100 in
        let k5 = (\x. let k6 = x + k1 in k2 * k6) in
        let k7 = if k4 > k1 then 
           let k8 = (\(x,y). let k9 = x * k1 in y - k0) in k8 (k3,k4) 
           else k0 in  
        let k8 = k5 k7 in
        k8`;
(*
- closure.close_all f5_def;
  f5 =
       (\(k0,k1,k2,k3).
          (let k4 = k0 + 100 in
           let k5 = fun (\(k1,k2) x. (let k6 = x + k1 in k2 * k6)) in
           let k7 =
                 (if k4 > k1 then
                    (let k8 =
                           fun (\(k1,k0) (x,y). (let k9 = x * k1 in y - k0))
                     in
                       k8 (k1,k0) (k3,k4))
                  else
                    k0)
           in
           let k8 = k5 (k1,k2) k7 in
             k8))

- closure.closure_convert f5_def;   (* there is a bug in top-leveling *)
 |- f5 =
       (\(v1,v2,v3,v4).
          (let v5 = fun (\(v15,v16) v17. (let v18 = v17 + v15 in v16 * v18))
           in
           let v6 = v1 + 100 in
           let v7 =
                 fun
                   (\(v10,v11) (v12,v13).
                      (let v14 = v12 * v10 in v13 - v11))
           in
           let v8 = (if v6 > v2 then v7 (v2,v1) (v4,v6) else v1) in
           let v9 = v5 (v2,v3) v8 in
             v9)) : thm
*)


(*---------------------------------------------------------------------------*)
(* Register Allocation                                                       *)
(*---------------------------------------------------------------------------*)

val f6_def = Define
   `f6 =
       \(k0,k1,k2,k3).
        let k4 = k0 - 100 in
        let k5 = k4 + k2 in
        let k6 = if k4 > k1 then k0 * k3
           else let k7 = k0 + k1 in k7 * 2 in
        let k8 = k5 + k6 in
        k8`;
(*

(* the case of insufficent registers that are available *)

- regAlloc.regL;
> val it = ref [``r0``, ``r1``, ``r2``, ``r3``]
- regAlloc.reg_alloc f6_def;
 |- f6 =
       (\(r0,r1,r2,r3).
          (let m1 = r1 in
           let r1 = r0 - 100 in
           let r2 = r1 + r2 in
           let m2 = r2 in
           let r2 = m1 in
           let r0 =
                 (if r1 > r2 then r0 * r3 else (let r0 = r0 + r2 in r0 * 2))
           in
           let r1 = m2 in
           let r0 = r1 + r0 in
             r0)) : thm


(*  the case of enough registers that are available *)

- regAlloc.regL := regAlloc.allregs;
-  !regAlloc.regL;
    [``r0``, ``r1``, ``r2``, ``r3``, ``r4``, ``r5``, ``r6``, ``r7``, ``r8``]

- regAlloc.reg_alloc f6_def;
 |- f6 =
       (\(r0,r1,r2,r3).
          (let r4 = r0 - 100 in
           let r2 = r4 + r2 in
           let r0 =
                 (if r4 > r1 then r0 * r3 else (let r0 = r0 + r1 in r0 * 2))
           in
           let r0 = r2 + r0 in
             r0)) : thm

*)

