(* --------------------------------------------------------------------*)
(* Simple examples for SAL code generation.                            *)
(* A more complicated example can be found in the "CADE_example.sml"   *)
(* --------------------------------------------------------------------*)

use "prelim";

(* --------------------------------------------------------------------*)
(* Source FILs.                                                        *)
(* --------------------------------------------------------------------*)

val f1_def = Define `
    f1 = \x. let y = x + (1w:word32) in let z = x - y in z`;

   certified_gen f1_def;

val f2_def = Define `
    f2 = \x. if x = (0w:word32) then x
             else let y = x * x in y`;

val f3_def = Define `
    f3 = \x. if x = (0:num) then 
                  let z = x - x in z
             else 
                  let y = x * x in y`;

(* --------------------------------------------------------------------*)
(* Results.                                                            *)
(* --------------------------------------------------------------------*)

   val result1 = certified_gen f1_def; 
   printSAL (#code result1);

(*
   val result1 =
    {code = ``ASG (L 1) y (x + 1w) (L 3) |++| ASG (L 3) z (x - y) (L 2)``,
     thm =
       |- Reduce
            (L 1,ASG (L 1) y (x + 1w) (L 3) |++| ASG (L 3) z (x - y) (L 2),L 2)
            ((let y = x + 1w in let z = x - y in z),z)} :
    {code : term, thm : thm}

    l1:   y := x + 1w  (goto l3)
    l3:   z := x - y  (goto l4)
*)


   val result2 = certified_gen f2_def;
   printSAL (#code result2);

(*
 val result2 =
    {code =
       ``IFGOTO (L 1) (\x. x = 0w) (L 7) (L 8) |++| NOP |++|
         (ASG (L 8) y (x * x) (L 9) |++| ASG (L 9) x y (L 2))``,
     thm =
       |- Reduce
            (L 1,
             IFGOTO (L 1) (\x. x = 0w) (L 7) (L 8) |++| NOP |++|
             (ASG (L 8) y (x * x) (L 9) |++| ASG (L 9) x y (L 2)),L 2)
            ((if x = 0w then x else (let y = x * x in y)),x)} :
  {code : term, thm : thm}

    l1:   ifgoto x = 0w l4 l5
    l5:   y := x * x  (goto l6)
    l6:   x := y  (goto l3)
*)

   val result3 = certified_gen f3_def;
   printSAL (#code result3);

(*
 val result3 =
    {code =
       ``IFGOTO (L 1) (\x. x = 0) (L 8) (L 9) |++|
         (ASG (L 8) z (x - x) (L 10) |++| ASG (L 10) x z (L 2)) |++|
         (ASG (L 9) y (x * x) (L 11) |++| ASG (L 11) x y (L 2))``,
     thm =
       |- Reduce
            (L 1,
             IFGOTO (L 1) (\x. x = 0) (L 8) (L 9) |++|
             (ASG (L 8) z (x - x) (L 10) |++| ASG (L 10) x z (L 2)) |++|
             (ASG (L 9) y (x * x) (L 11) |++| ASG (L 11) x y (L 2)),L 2)
            ((if x = 0 then (let z = x - x in z) else (let y = x * x in y)),x)}
     : {code : term, thm : thm}

    l1:   ifgoto x = 0 l8 l9
    l8:   z := x - x  (goto l10)
    l10:  x := z  (goto l2)
    l9:   y := x * x  (goto l11)
    l11:  x := y  (goto l2)

*)
