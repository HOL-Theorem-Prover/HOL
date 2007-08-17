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

val g1_def = Define `
  g1 (x:word32) = 
   let x = x * 3w in
   let y = x + 270w in
   let z = 70w:word32 << 8 in
     (x,y,z)`;

(*
val g1' = (reg_alloc o SSA_RULE o normalize) g1_def;
...

*)
