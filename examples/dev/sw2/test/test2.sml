use "prelim";

(*---------------------------------------------------------------------------*)
(* Front End                                                                 *)
(*---------------------------------------------------------------------------*)

val fact_def = Define
   `fact i = if i = 0 then 1
	else i * fact (i - 1)`;

val f1_def = Define
   `f1 (k0,k1,k2)  =
        let y = k2 + 100 in
        let g = (\(x,y). y - (x * k0)) in 
        let z = if fact 3 < 10 /\ y + 2 * k1 > k0 then g (k1, k2)
		else y
        in
        z * y`;

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
(* Closure Conversion                                                        *)
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

val th3 = SSA_RULE (optimize_norm [] (SIMP_RULE std_ss [Once LET_THM, fun_def] th2));

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

regL := [``r0:num``, ``r1:num``, ``r2:num``];
val th4 = reg_alloc th3;

(*

 |- f1 =
       (\(r0,r1,r2).
          (let m1 = r2 in
           let m2 = r0 in
           let r0 = m1 in
           let r0 = r0 + 100 in
           let m3 = r0 in
           let r0 = 2 * r1 in
           let r2 = m3 in
           let r0 = r2 + r0 in
           let r2 = m2 in
           let r0 =
                 (if r0 <= r2 then
                    (let r0 = m3 in r0)
                  else
                    (let r0 = r2 * r1 in
                     let r1 = m1 in
                     let r0 = r1 - r0 in
                       r0))
           in
           let r1 = m3 in
           let r0 = r1 * r0 in
             r0))
*)

regL := [``r0:num``, ``r1:num``, ``r2:num``, ``r3:num``, ``r4:num``];
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
             r0))
*)

