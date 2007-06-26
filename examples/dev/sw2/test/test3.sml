use "prelim";

val f1_def = Define `f1 x = let y = x + 1 in let z = x - y in z`;


val f2_def = Define `
    f2 x = 
      if x = 0 then x 
      else let y = x * x in y`;

(* 
   certified_gen f1_def; 

    |- Reduce
         (L 1, ASG (L 1) y (x + 1) (L 3) |+ 
               ASG (L 3) z (x - y) (L 4),
          L 4)
         ((let y = x + 1 in let z = x - y in z),z) : thm


   certified_gen f2_def;  (* dies *)

*)
