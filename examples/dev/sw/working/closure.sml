open HolKernel Parse boolLib bossLib numLib arithmeticTheory pairTheory;

(*----------------------------------------------------------------------------*)
(*  Higher Order Functions                                                    *)
(*----------------------------------------------------------------------------*)

val twice_def = Define `
  twice (f : num -> num, i) = f (f i)`;

val main_def  = Define `
  main (y,z) =
    let g1 x = x + y in
    let g2 x = x + 2 in
    (twice(g1,z),twice(g2,z))`;


(*----------------------------------------------------------------------------*)
(* Closure Conversion                                                         *)
(*----------------------------------------------------------------------------*)

val _ = Hol_datatype `
    clos = G1 of num 
         | G2
    `;

val g1'_def = Define `
    g1' (x,y) = x + y`;

val g2'_def = Define `
    g2' x = x + 2`;

val dispatch_def = Define `
    dispatch (c:clos, i:num) =
      case c of 
         G1 y -> g1'(i,y) ||
         G2   -> g2' i
    `;

val twice1_def = Define `
  twice1 (f : clos, i) = dispatch (f, dispatch(f,i))`;

val main1_def  = Define `
  main1 (y,z) =
    let g1:clos = G1 y in
    let g2:clos = G2 in
    (twice1(g1,z),twice1(g2,z))`;

(*----------------------------------------------------------------------------*)
(*  Equivalence                                                               *)
(*----------------------------------------------------------------------------*)

val Thm1 = Q.store_thm (
  "Thm1",
  `main1 = main`,
   SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD] THEN
   RW_TAC std_ss [main1_def, main_def, LET_THM, twice1_def, twice_def, dispatch_def] THEN
   RW_TAC std_ss [g1'_def, g2'_def]
  );


