
open HolKernel boolLib bossLib Parse;
open tailrecTheory tailrecLib compilerLib;

val _ = new_theory "compiler_demo";



(* basic loop: mod 10 *)

val (th1,th2,th3) = compile "x86" `` 
  mod10 (r1:word32) = 
    if r1 <+ 10w then r1 else let r1 = r1 - 10w in mod10 r1``;

(* comparisions *)

val (th1,th2,th3) = compile "ppc" `` 
  test_cmp (r1:word32,r2:word32) = 
    if r1 < r2 then let r2 = 5w:word32 in (r1,r2) else (r1,r2)``;

(* large constants *)

val (th1,th2,th3) = compile "ppc" `` 
  large_constants (r1:word32,r2:word32) = 
    if r1 = 0w then let r2 = 5w:word32 in (r1,r2) else
      let r1 = r1 + r2 in
      let r2 = 60000w:word32 in
      let r2 = 2360000w:word32 in
        large_constants (r1,r2)``;

(* memory reads *)

val (th1,th2,th3) = compile "x86" `` 
  read_loop (r1:word32,r2:word32,dm:word32 set,m) = 
    if r1 = 0w then (r1,r2,dm,m) else
      let r1 = m r1 in 
      let r2 = m r2 in
        read_loop (r1,r2,dm,m)``;

(* memory writes *)

val (th1,th2,th3) = compile "x86" `` 
  copy_loop (r1:word32,r2:word32,df:word32 set,f) = 
    if r1 = 0w then (r1,r2,df,f) else
      let r1 = f r1 in 
      let r2 = f r2 in
      let f = (r2 =+ r1) f in
        copy_loop (r1,r2,df,f)``;

(* shared-tails *)

val (th1,th2,th3) = compile "x86" `` 
  shared_tails (r1:word32,r2:word32) = 
    if r1 = 0w then 
      let r2 = 23w:word32 in 
      let r1 = 4w:word32 in
        (r1,r2) 
    else
      let r2 = 56w:word32 in 
      let r1 = 4w in
        (r1,r2)``;

(* removal of dead code *)

val (th1,th2,th3) = compile "x86" `` 
  dead_code (r1:word32,r2:word32) = 
    let r2 = 45w:word32 in 
    if r1 <+ 3w then 
      let r2 = r1 + 67w in
      let r2 = r1 in (r1,r2)
    else  
      let r2 = r1 + 6w in (r1,r2)``;

(* subroutines *)

val (th1,th2,th3) = compile "x86" `` 
  call_mod10 (r1:word32,r2:word32,r3) = 
    let r1 = r1 + r2 in 
    let r1 = r1 + r3 in 
    let r1 = mod10 r1 in
      r1``;

val _ = export_theory();

