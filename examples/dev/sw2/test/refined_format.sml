(* --------------------------------------------------------------------*)
(* Simple examples for the conversion to the format the ARM backend    *)
(* can deal with.                                                      *)
(* --------------------------------------------------------------------*)

use "compiler";

(* --------------------------------------------------------------------*)
(* Test the parallel move.                                             *)
(* --------------------------------------------------------------------*)

val (src1,dst1) = (``(r2:word32,r3:word32,r4:word32,r1:word32)``,
                   ``(r1:word32,r2:word32,r3:word32,r4:word32)``
                  )
val m1 = parallel_move dst1 src1 dst1;

prove(mk_eq(m1, src1),
 SIMP_TAC bool_ss [LET_THM, NormalTheory.ATOM_ID]
 )

(*
 |- (let r0 = atom r1 in
     let r1 = atom r2 in
     let r2 = atom r3 in
     let r3 = atom r4 in
     let r4 = atom r0 in
     (r1,r2,r3,r4)) =
     (r2,r3,r4,r1) : thm
*)

val (src2,dst2) = (``(r0:word32,r1:word32,r2:word32,r3:word32)``,
                   ``(r1:word32,r2:word32,r3:word32,r4:word32)``
                  )
val m2 = parallel_move dst2 src2 dst2;

prove(mk_eq(m2, src2),
 SIMP_TAC bool_ss [LET_THM, NormalTheory.ATOM_ID]
 )

(*
 |- (let r5 = atom r1 in
        let r1 = atom r0 in
        let r0 = atom r2 in
        let r2 = atom r5 in
        let r5 = atom r3 in
        let r3 = atom r0 in
        let r4 = atom r5 in
          (r1,r2,r3,r4)) =
       (r0,r1,r2,r3) : thm
*)

val (src3,dst3) = (``(m0:word32,m1:word32,m2:word32,m3:word32)``,
                   ``(m1:word32,m2:word32,m4:word32,m0:word32)``
                  )
val m3 = parallel_move dst3 src3 dst3;

prove(mk_eq(m3, src3),
 SIMP_TAC bool_ss [LET_THM, NormalTheory.ATOM_ID]
 )

(*
|- (let r0 = atom m1 in
        let r1 = atom m0 in
        let m1 = atom r1 in
        let r1 = atom m2 in
        let m2 = atom r0 in
        let m4 = atom r1 in
        let r0 = atom m3 in
        let m0 = atom r0 in
          (m1,m2,m4,m0)) =
       (m0,m1,m2,m3) : thm
*)

(* --------------------------------------------------------------------*)
(* Test the refined register allocator.                                *)
(* --------------------------------------------------------------------*)

(*
val def0 = Define `
  f0 x = if x = 0w:word32 then x
         else f0 (x - 1w)`;
*)
  

val def1 = Define `
    f1 (x,y) = if x = (0w:word32) then y
               else f1 (x - 1w, x * y)`;

(* 
val def1' = (reg_alloc o SSA_RULE o normalize) def1;
|- f1 =
       (\(r0,r1).
          (if r0 = 0w then
             r1
           else
             (let r2 = r0 - 1w in
              let r0 = r0 * r1 in
              let r3 = r0 in
              let r0 = r2 in
              let r1 = r3 in
                f1 (r0,r1)))) : thm
*)


val def2 = Define `
   f2 (k0:word32,(k1:word32,k2:word32),k3:word32) = 
     if k0 = 0w then
       (k2,k3)
     else if k0 < 5w then
         f2 (k0 - 1w, (k3 - k2, k2 * k1), k0)
     else
         f2 (k0 - 1w, (k0,k1), k3 - k0)`;

(* 
val def2' = (reg_alloc o SSA_RULE o normalize) def2;

    |- f2 =
       (\(r0,(r1,r2),r3).
          (if r0 = 0w then
             (r2,r3)
           else
             (if r0 < 5w then
                (let r4 = r0 - 1w in
                 let r3 = r3 - r2 in
                 let r1 = r2 * r1 in
                 let r5 = r0 in
                 let r0 = r4 in
                 let r4 = r1 in
                 let r1 = r3 in
                 let r2 = r4 in
                 let r3 = r5 in
                   f2 (r0,(r1,r2),r3))
              else
                (let r2 = r0 - 1w in
                 let r3 = r3 - r0 in
                 let r4 = r0 in
                 let r0 = r2 in
                 let r5 = r1 in
                 let r1 = r4 in
                 let r2 = r5 in
                   f2 (r0,(r1,r2),r3))))) : thm

*)


(* --------------------------------------------------------------------*)
(* Refine the format of virtual instructions for the ARM machine.      *)
(* --------------------------------------------------------------------*)

val binop1_def = Define `
  binop1(x:word32,y) =
    let z0 = 40w + y in
    let z1 = 10w - z0 in
    let z2 = 510w + x * z1 in
    let z3 = x !! 300w && y ?? z2 in
    let z4 = (z3 + z2) >>> 3 in
    (z1,z2,z3,z4)
  `;

(*
normalize binop1_def;
 |- binop1 (x,y) =
       (let z0 = y + 40w in
        let z1 = rsb z0 10w in
        let x1 = 510w in
        let y1 = x * z1 in
        let z2 = x1 + y1 in
        let x1 = 300w in
        let x1 = x1 && y in
        let y = x1 ?? z2 in
        let z3 = x !! y in
        let x = z3 + z2 in
        let z4 = x >>> 3 in
          (z1,z2,z3,z4)) : thm
*)

val mult_def = Define `
  mult(x:word32,y) =
    let z1 = x * y in
    let z2 = x * 10w in
    let z3 = 100w * x in
    let z4 = 500w * 6w in
    (z1,z2,z3,z4)
  `;

(*
normalize mult_def;
 |- mult (x,y) =
       (let z1 = x * y in
        let y = 10w in
        let z2 = x * y in
        let x1 = 100w in
        let z3 = x1 * x in
        let x = 500w in
        let y = 6w in
        let z4 = x * y in
          (z1,z2,z3,z4)) : thm

*)

val g1_def = Define `
  g1 (x:word32) = 
   if x > 1w /\ x < 10w then
     x + 1w
   else if 20w >+ x \/ x <=+ x then
     x + 4w
   else 
     x
   `;

(*
normalize g1_def;

|- g1 x =
       (let x1 = x + 4w in
          (if x <= 1w then
             (if x <+ 20w then x1 else (if x <=+ x then x1 else x))
           else
             (if x < 10w then
                (let x = x + 1w in x)
              else
                (if x <+ 20w then x1 else (if x <=+ x then x1 else x))))) : thm

*)

(* --------------------------------------------------------------------*)
(* Refine the format of conditional statments.                         *)
(* --------------------------------------------------------------------*)

val g1_def = Define `
  g1 (r0:word32) =
   let r1 = if r0 > 1w then r0 + 1w else r0 in
   let r2 = r1 - 2w in
   (r1,r2)
   `;

val g2_def = Define `
  g2 (x:word32) =
   let ((y,z),i) = if x > 1w then ((x + 1w, x), x) else ((x, x+1w), x) in
   let z = z - 2w in
   (y,z, i)
   `;
