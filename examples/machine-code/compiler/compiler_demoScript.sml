
open HolKernel boolLib bossLib Parse;
open tailrecTheory tailrecLib compilerLib codegen_x86Lib;

val _ = new_theory "compiler_demo";



(* basic loop: mod 10 *)

val (th1,th2,th3) = compile_all `` 
  mod10 (r1:word32) = 
    if r1 <+ 10w then r1 else let r1 = r1 - 10w in mod10 r1``;

(* comparisions *)

val (th1,th2,th3) = compile "ppc" `` 
  test_cmp (r1:word32,r2:word32) = 
    if r1 < r2 then let r2 = 5w:word32 in (r1,r2) else (r1,r2)``;

(* large constants *)

val (th1,th2,th3) = compile_all `` 
  large_constants (r1:word32,r2:word32) = 
    if r1 = 0w then let r2 = 5w:word32 in (r1,r2) else
      let r1 = r1 + r2 in
      let r2 = 60000w:word32 in
      let r2 = 2360000w:word32 in
        large_constants (r1,r2)``;

(* memory reads *)

val (th1,th2,th3) = compile_all `` 
  read_loop (r1:word32,r2:word32,dm:word32 set,m) = 
    if r1 = 0w then (r1,r2,dm,m) else
      let r1 = m r1 in 
      let r2 = m r2 in
        read_loop (r1,r2,dm,m)``;

(* memory writes *)

val (th1,th2,th3) = compile_all `` 
  copy_loop (r1:word32,r2:word32,dg:word32 set,g) = 
    if r1 = 0w then (r1,r2,dg,g) else
      let r1 = g r1 in 
      let r2 = g r2 in
      let g = (r2 =+ r1) g in
        copy_loop (r1,r2,dg,g)``;

(* byte accesses *)

val (th1,th2,th3) = compile_all `` 
  copy_byte_loop (r1:word32,r2:word32,dg:word32 set,g:word32->word8) = 
    if r1 = 0w then (r1,r2,dg,g) else
      let r1 = w2w (g r1) in 
      let r2 = w2w (g r2) in
      let g = (r2 =+ w2w r1) g in
        copy_byte_loop (r1,r2,dg,g)``;

(* shared-tails *)

val (th1,th2,th3) = compile_all `` 
  shared_tails1 (r1:word32,r2:word32) = 
    if r1 = 0w then 
      let r2 = 23w:word32 in 
      let r1 = 4w:word32 in
        (r1,r2) 
    else
      let r2 = 56w:word32 in 
      let r1 = 4w in
        (r1,r2)``;

(* removal of dead code *)

val (th1,th2,th3) = compile_all `` 
  dead_code1 (r1:word32,r2:word32) = 
    let r2 = 45w:word32 in 
    if r1 <+ 3w then 
      let r2 = r1 + 67w in
      let r2 = r1 in (r1,r2)
    else  
      let r2 = r1 + 6w in (r1,r2)``;

(* subroutines *)

val (th1,th2,th3) = compile_all `` 
  call_mod10 (r1:word32,r2:word32,r3) = 
    let r1 = r1 + r2 in 
    let r1 = r1 + r3 in 
    let r1 = mod10 r1 in
      r1``;

(* addition *)

val (th1,th2,th3) = compile_all `` 
  addition (r1:word32,r2:word32) = 
    let r1 = r2 + r1 in
    let r2 = r1 + r2 in
    let r3 = r1 + 8w in
    let r4 = r2 + 45w in
    let r5 = r2 + r3 in
      (r1,r2,r3,r4,r5)``;

val _ = export_theory();

