
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
  copy_byte_loop (r3:word32,r4:word32,dg:word32 set,g:word32->word8) = 
    if r3 = 0w then (r3,r4,dg,g) else
      let r3 = w2w (g r3) in 
      let r4 = w2w (g r4) in
      let g = (r4 =+ w2w r3) g in
        copy_byte_loop (r3,r4,dg,g)``;

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

(* string operations *)

val _ = codegen_x86Lib.set_x86_regs 
  [(3,"eax"),(4,"ecx"),(5,"edx"),(6,"ebx"),(7,"edi"),(8,"esi"),(9,"ebp")]

val (thms,arm_str_rev_def,arm_str_rev_pre_def) = compile_all ``
  arm_string_rev(r3:word32,r6,r7,df:word32 set,f:word32->word8) = 
    if r3 = 0w then (r7,df,f) else
      let r4 = (w2w (f r6)):word32 in
      let r5 = (w2w (f r7)):word32 in
      let f = (r6 =+ w2w r5) f in
      let f = (r7 =+ w2w r4) f in
      let r6 = r6 - 1w in
      let r7 = r7 + 1w in
      let r3 = r3 - 1w in
        arm_string_rev(r3,r6,r7,df,f)``


val _ = export_theory();

