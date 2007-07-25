(*
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;
open arm_compilerLib;

val _ = optimise_code := true;
val _ = abbrev_code := false;

val _ = new_theory "arm_compiler_demo";

(* 

INTRODUCTION

This file illustrates, through examples, how the ARM compiler from 
arm_progLib can be used. The compiler's top-level function is 

  arm_progLib.arm_compile (def:thm) (ind:thm) (as_proc:bool)

Here def is a definition, ind is the induction rule produced by Define
and as_proc is a boolean flag indicating whether def should be compiled as 
a procedure or not.

In order to keep the presentation consice we define test_compile and
test_compile_proc: 

*)

fun find_ind_thm def = let
  val tm = (fst o dest_eq o concl o SPEC_ALL) def
  val name = (fst o dest_const) ((fst o dest_comb) tm handle e => tm)
  in fetch "-" (name^"_ind") handle e => TRUTH end;

fun test_compile' as_proc q = let
  val def = Define q
  val ind = find_ind_thm def
  val (th,strs) = arm_compile def ind as_proc
 (* val _ = map print (["\n\n\n"] @ strs @ ["\n\n\n"]) *)
  in (def,ind,th) end;

fun test_compile q = test_compile' false q;
fun test_compile_proc q = test_compile' true q;

(* 

The compiler expects def to be a function where variables have names 
r0,r1,r2,...,r12 or m0,m1,m2 .... The variable names tells the compiler 
how to assign physical resources to each logical variable, e.g.

  r1  - becomes register 1
  m5  - becomes memory location at address stack pointer + 5 

The functions it accepts must conform to the following grammar.
Let r range over register names (r0,r1,r2,etc), m range over 
memory locations (m0,m1,m2,etc), i over natural numbers and 
w over 8-bit word constants.

  p    ::=  let r = exp in p  
         |  let m = r in p  
         |  if g then p else p  
         |  (v,v,...,v)

  v    ::=  r  |  m
  g    ::=  ~ g  |  r cmp mode  |  r && mode = 0w
  cmp  ::=  =  |  <  |  <+  |  <=  |  <=+
  exp  ::=  m  |  mode  |  ~ mode  |  r op mode  |  r * r
  op   ::=  + | - | && | ?? | !!
  mode ::=  w  |  r  |  r << i  |  r >> i  |  r >>> i 

Notice that one cannot have:

  let r0 = (if r1 < r2 then 5w else r6) in P

This needs to be expanded out as follows:

  if r1 < r2 then
    let r0 = 5w in P
  else
    let r0 = r6 in P

A naive compilation would duplicate the code for P. We optimise
"common code tails" and that way, to a large extent, avoid duplication 
of code (See section of shared-tails for more).

*)
 

(* TEST: constant functions *)

val (load_const_def,_,load_const_arm) = test_compile `
  load_const : word32 # word32 # word32 =
    let r0 = 0w in
    let r1 = 45w in
    let r2 = ~r1 in
      (r0,r1,r2)`;

(* Each let-expression is compiled into one ARM instruction or 
   procedure call. The code for load_const above becomes: 
  
     mov r0, #0
     mov r1, #45
     mvn r2, r1
*)


(* TEST: nonrecursive functions *)

val (garble_def,_,garble_arm) = test_compile `
  garble (r2:word32,r3:word32,r4:word32) =
    let r1 = r2 + r3 in
    let r2 = r1 - r3 << 5 in
    let r3 = r2 * r3 in
    let r1 = r1 + 4w in
    let r2 = r3 && r2 >>> 30 in
    let r2 = r2 << 16 in
    let r2 = ~(r2 >>> 2) in
    let r3 = r2 !! r1 in
    let r2 = r3 ?? 55w in
      (r2,r3)`;

(* Input and output are tuples. For garble_def we expect input in
   register 2, 3 and 4; and produce output into registers 2 and 3. *)


(* TEST: recursive functions *)

val (mul32_def,mul32_ind,mul32_arm) = test_compile `
  mul32 (r0:word32,r1:word32,r2:word32) =
    if r0 = 0w then (r0,r1,r2) else 
      let r2 = r1 + r2 in
      let r0 = r0 - 1w in
        mul32 (r0,r1,r2)`;

val (fac32_def,fac32_ind,fac32_arm) = test_compile `
  fac32 (r0:word32,r1:word32) =
    if r0 = 0w then r1 else 
      let r1 = r0 * r1 in
      let r0 = r0 - 1w in
        fac32 (r0,r1)`;

(* Looping functions are required to be tail-recursive and
   the recurive calls need to be identical to the left-hand side of 
   the definition of the function, i.e. 
     
     f (r1,r2) = let .... in f (r2,r3)

   is not allowed, since (r1,r2) is not syntactically the same as (r2,r3). *)


(* TEST: functions with multiple recursive calls *)

val (recg_def,recg_ind,recg_arm) = test_compile `
  recg (r0:word32,r1:word32) = 
    if r0 = 0w then 
     r1 
    else if r0 = 2w then 
     (let r2 = r0 && r1 in r1) 
    else if r0 = r1 then
     (let r2 = 5w:word32 in
      let r3 = ~r2 in
      let r1 = r0 * r1 in
      let r0 = r0 - 1w in
        recg(r0,r1))
    else 
     (let r1 = r0 * r1 in
      let r3 = ~r1 in
      let r0 = r0 - 1w in
        recg(r0,r1))`;


(* TEST: negative guard in if-then-else *)

val (neg_test_def,_,neg_test_arm) = test_compile `
  neg_test (r0:word32,r1:word32) = 
    let r1 = r0 + r1 in
    if ~(r0 = 0w) then 
      let r1 = r0 + r1 in
        r1
    else
      let r1 = r1 + 4w in
        r1`;


(* TEST: various guards *)

val (guard_test_def,_,guard_test_arm) = test_compile `
  guard_test (r0:word32,r1:word32,r2:word32,r3:word32) = 
    if 5w <= r2         then let r0 = r1 + 2w in r0 else
    if r0 <+ 3w         then let r0 = r1 + 3w in r0 else r0`;

val (guard_test_def,_,guard_test_arm) = test_compile `
  guard_test (r0:word32,r1:word32,r2:word32,r3:word32) = 
    if r0 <= r2         then let r0 = r1 + 2w in r0 else
    if r0 <+ 3w         then let r0 = r1 + 3w in r0 else
    if ~(r0 < 3w)       then let r0 = r1 + 5w in r0 else
    if r0 <+ r3 << 2    then let r0 = r1 + 6w in r0 else
    if r3 << 2 <+ r3    then let r0 = r1 + 7w in r0 else
    if ~(r3 >> 2 <+ r3) then let r0 = r1 + 8w in r0 else r0`;

val (guard_loop_def,guard_loop_ind,guard_loop_arm) = test_compile `
  guard_loop (r0:word32) = 
    if r0 = 0w then r0 else
      if r0 < 3w then 
        let r0 = r0 - 1w in guard_loop(r0)
      else 
        let r0 = r0 - 1w in guard_loop(r0)`

(* Notice that one of the branches in same_guard_def is unreachable.
   The compiler will be unable to prove the unreachable path and drops it.
   Hence the message from the compiler                                     *)

val (same_guard_def,_,same_guard_arm) = test_compile `
  same_guard (r0:word32,r1:word32,r2:word32,r3:word32) = 
    if r0 < 3w then let r0 = r1 + 1w in r0 else
    if r0 < 3w then let r0 = r1 + 3w in r0 else r0`;


(* TEST: conditional execution *)

(* Here the compiler does not introduce a branch instead it executes 
   the addition conditionally. *)

val (reg_min_def,_,reg_min_arm) = test_compile `
  reg_min (r0:word32,r1:word32) =
    if r0 < r1 then 
      let r1 = r1 + r0 in r1 
    else 
      r1`;


(* TEST: if-then-else shared tail elim *)

(* In order to avoid duplication of code the compiler can pull out
   tails that are shared across if-then-else branches. *)

val (shared_tail_def,_,shared_tail_arm) = test_compile `
  shared_tail (r0:word32,r1:word32,r2:word32) =
    if r1 < r2 then 
      let r1 = r2 in
      let r0 = r1 + 5w in
      let r2 = r0 + r1 in
        r2
    else 
      let r0 = r1 + 5w in
      let r2 = r0 + r1 in
        r2`;

val (shared_tail2_def,_,shared_tail2_arm) = test_compile `
  shared_tail2 (r0:word32,r1:word32,r2:word32) =
    if r1 < r2 then
      if r2 < r0 then 
        let r1 = r2 + 1w in
        let r0 = r1 - 5w in
        let r0 = r0 - 5w in
          r0
      else 
        let r1 = r2 + 2w in
        let r0 = r1 - 5w in
        let r0 = r0 - 5w in
          r0
    else 
      if r2 < 5w then 
        let r1 = r2 + 3w in
        let r0 = r1 - 5w in
        let r0 = r0 - 5w in
          r0
      else 
        let r1 = r2 + 4w in
        let r0 = r1 - 5w in
        let r0 = r0 - 5w in
          r0`;


(* TEST: if-the-else shared front can be pulled out *)

(* In some cases the front can be pulled out as illustrated 
   by the following code. The comparison instruction comes first
   in the compiled code, then the move and the addition and at 
   the end subtraction is done conditionally. *)

val (shared_front_def,_,shared_front_arm) = test_compile `
  shared_front (r0:word32,r1:word32,r2:word32) =
    if r1 < r2 then 
      let r1 = 5w in
      let r2 = r1 + r2 in
        r2
    else 
      let r1 = 5w in
      let r2 = r1 + r2 in
      let r2 = r2 - 4w in  
        r2`;


(* TEST: memory accesses *)

(* Memory accesses to the stack are done using variables names
   m0,m1,m2 etc. Memory locations cannot be refered to in 
   expressions, e.g. 

     let m1 = m2 + 5w in ... 
 
   is not allowed, since there is no ARM instruction for 
   addition of memory locations. Instead:
 
     let r0 = m2 in
     let m1 = r0 + 5w in ... 
 
*)

val (mem_swap_def,_,mem_swap_arm) = test_compile `
  mem_swap (m0:word32,m1:word32) =
    let r0 = m0 in  
    let r1 = m1 in
    let m0 = r1 in
    let m1 = r0 in
      (m0,m1)`;

val (mem_as_temp_def,_,mem_as_temp_arm) = test_compile `
  mem_as_temp (r0:word32,r1:word32,r2:word32) =
    let m1 = r0 in  
    let r1 = r1 + r2 in
    let m2 = r1 in
    let r2 = r1 + r2 in
    let m3 = r2 in
      m3`;


(* TEST: procedure in-lining *)

(* The compiler keeps track of previously compiled code. In order to 
   flush its memory call: 

     reset_compiled() 
*)

val _ = reset_compiled();

val (fac32_acc_def,fac32_acc_ind,fac32_acc_arm) = test_compile `
  fac32_acc (r0:word32,r1:word32) =
    if r0 = 0w then r1 else 
      let r1 = r0 * r1 in
      let r0 = r0 - 1w in
        fac32_acc (r0,r1)`;

val (fac32_def,_,fac32_arm) = test_compile `
  fac32 (r0:word32) =
    let r1 = 1w in
    let r1 = fac32_acc (r0,r1) in
    let r0 = r1 in
      r0`;

(* fac32 contains an instance of fac32_acc. Make sure that the
   call to fac32_acc uses the variable names with which fac32_acc 
   was defined, e.g. calling it using 

     let r1 = fac32_acc (r3,r4) in
     
   is not allowed since (r3,r4) is not syntactically equal to (r0,r1)
   which was used in the definition of fac32_acc; similarly 

     let r9 = fac32_acc (r0,r1) in
     
   is also malformed since the result of fac32_acc is stored in r0, 
   not in r9.
*)

(* 
-- for some reason fac_add_def makes Holmake fail, but it's fine here.

val (fac_add_def,_,fac_add_arm) = test_compile `
  fac_add (r0:word32,r2:word32) =
    let r0 = fac32(r0) in
    let r0 = r0 + r2 in
      r0`;
*)

(* Note that the compilation of fac_add would rightly fail, if r2 was 
   replaced by r1 in the definition of fac_add, since r1 is used 
   when fac32 executes. *)



(* TEST: procedure calls *)

val _ = reset_compiled();

(* If we compile fac32_acc as a procedure then calls to it will be 
   executed using the ARM instruction for procedure calls, i.e.
   the BL instruction (branch-and-link). *)

val (fac32_acc_def,fac32_acc_ind,fac32_acc_arm) = test_compile_proc `
  fac32_acc (r0:word32,r1:word32) =
    if r0 = 0w then r1 else 
      let r1 = r0 * r1 in
      let r0 = r0 - 1w in
        fac32_acc (r0,r1)`;

val (fac32_def,_,fac32_arm) = test_compile `
  fac32 (r0:word32) =
    let r1 = 1w in
    let r1 = fac32_acc (r0:word32,r1:word32) in
    let r0 = r1 in
      r0`;

(* Note: At present, it is only possible to do subroutine calls to a 
   depth of one, since the link-register (register 14) gets garbled 
   if a subroutine call is made inside a subroutine. Arbitrary 
   depth procedure calls will soon be implemented. *)


(* TEST: Joe's ECC definitions *)

(* The code becomes very large (thousands of lines) in the following 
   examples since we use procedure in-lineing through out.
   Hence, in order to cope we switch on "code abbrevaition". *)

val _ = abbrev_code := true;


val _ = reset_compiled();

val (load_751_def,_,load_751_arm) = test_compile `
  load_751 = 
    let r10 = 2w:word32 in
    let r10 = r10 << 8 in
    let r10 = r10 + 239w in r10`;

val (field_neg_def,_,field_neg_arm) = test_compile `
  field_neg (r1:word32) =
    if r1 = 0w then r1 else 
      let r10 = load_751 in
      let r1 = r10 - r1 in r1`;

val (field_add_def,_,field_add_arm) = test_compile `
  field_add (r0:word32,r1:word32) =
    let r10 = load_751 in
    let r0 = r1 + r0 in
      if r0 < r10 then r0 else 
        let r0 = r0 - r10 in 
          r0`;

val (field_sub_def,_,field_sub_arm) = test_compile `
  field_sub (r0,r1) =
    let r1 = field_neg r1 in 
    let r0 = field_add (r0,r1) in 
      r0`;

val (field_mult_aux_def,field_mult_aux_ind,field_mult_aux_arm) = test_compile `
  field_mult_aux (r2:word32,r3:word32,r4:word32) =
    if r3 = 0w then r4 else
      if r3 && 1w = 0w then 
          let r3 = r3 >>> 1 in 
          let r0 = r2 in
          let r1 = r2 in
          let r0 = field_add (r0,r1) in
          let r2 = r0 in
            field_mult_aux (r2:word32,r3:word32,r4:word32)
        else
          let r3 = r3 >>> 1 in 
          let r0 = r4 in
          let r1 = r2 in
          let r0 = field_add (r0,r1) in
          let r4 = r0 in
          let r0 = r2 in
          let r1 = r2 in
          let r0 = field_add (r0,r1) in
          let r2 = r0 in
            field_mult_aux (r2:word32,r3:word32,r4:word32)`;

val (field_mult_def,_,field_mult_arm) = test_compile `
  field_mult (r2,r3) = 
    let r4 = 0w in
    let r4 = field_mult_aux (r2,r3,r4) in
      r4`;

val (field_exp_aux_def,field_exp_aux_ind,field_exp_aux_arm) = test_compile `
  field_exp_aux (r5:word32,r6:word32,r7:word32) =
    if r6 = 0w then r7 else
      if r6 && 1w = 0w then 
          let r6 = r6 >>> 1 in 
          let r2 = r5 in
          let r3 = r5 in
          let r4 = field_mult (r2,r3) in
          let r5 = r4 in
            field_exp_aux (r5:word32,r6:word32,r7:word32)
        else
          let r6 = r6 >>> 1 in 
          let r2 = r7 in
          let r3 = r5 in
          let r4 = field_mult (r2,r3) in
          let r7 = r4 in
          let r2 = r5 in
          let r3 = r5 in
          let r4 = field_mult (r2,r3) in
          let r5 = r4 in
            field_exp_aux (r5:word32,r6:word32,r7:word32)`;

val (field_exp_def,_,field_exp_arm) = test_compile `
  field_exp (r5,r6) = 
    let r7 = 1w in
    let r7 = field_exp_aux (r5,r6,r7) in
      r7`;

val (field_inv_def,_,field_inv_arm) = test_compile `
  field_inv r5 = 
    let r6 = 2w:word32 in
    let r6 = r6 << 8 in
    let r6 = r6 + 237w in 
    let r7 = field_exp (r5,r6) in
      r7`;

val (field_div_def,_,field_div_arm) = test_compile `
  field_div (r8,r9) = 
    let r5 = r9 in
    let r7 = field_inv r5 in
    let r2 = r8 in
    let r3 = r7 in
    let r4 = field_mult(r2,r3) in
      r4`;
  
val (both_zero_def,_,both_zero_arm) = test_compile `
  both_zero (r1:word32,r2:word32) =
    if r1 = 0w then 
      if r2 = 0w then 
        let r0 = 1w:word32 in (r0,r1,r2)
      else 
        let r0 = 0w in (r0,r1,r2)
    else
      let r0 = 0w in (r0,r1,r2)`;

val (both_eq_def,_,both_eq_arm) = test_compile `
  both_eq (r1:word32,r2:word32,r3:word32,r4:word32) =
    if r1 = r3 then 
      if r2 = r4 then 
        let r0 = 1w:word32 in (r0,r1,r2,r3,r4)
      else 
        let r0 = 0w in (r0,r1,r2,r3,r4)
    else
      let r0 = 0w in (r0,r1,r2,r3,r4)`;

val (curve_neg_def,_,curve_neg_arm) = test_compile `
  curve_neg (r1:word32,r2:word32) =
    let (r0,r1,r2) = both_zero(r1,r2) in
      if r0 = 0w then 
        (r1,r2) 
      else
        let r8 = r1 in
        let r9 = r2 in
        let r2 = 0w in
        let r3 = r8 in
        let r4 = field_mult(r2,r3) in
        let r1 = r9 in
        let r1 = field_neg r1 in
        let r0 = r1 in
        let r1 = r4 in
        let r0 = field_sub(r0,r1) in
        let r1 = 1w in
        let r0 = field_sub(r0,r1) in
        let r2 = r0 in
        let r1 = r8 in
          (r1,r2)`;

val (curve_double_def,_,curve_double_arm) = test_compile `
  curve_double (r1,r2) =
    let (r0,r1,r2) = both_zero(r1,r2) in
    if r0 = 0w then (r1,r2) else
    let m1 = r1 in (* x1 *)
    let m2 = r2 in (* y1 *)
    let r2 = 2w in
    let r3 = r2 in
    let r4 = field_mult(r2,r3) in
    let r5 = r4 in
    let r2 = 0w in
    let r3 = m1 in
    let r4 = field_mult(r2,r3) in
    let r0 = r5 in      
    let r1 = r4 in      
    let r0 = field_add(r0,r1) in
    let r1 = 1w in      
    let r0 = field_add(r0,r1) in
    if r0 = 0w then 
      let r1 = 1w in
      let r2 = 0w in
        (r1,r2)
    else
    let r11 = r0 in (* d *)
    let r5 = m1 in
    let r6 = 2w in
    let r7 = field_exp(r5,r6) in
    let r2 = 3w in
    let r3 = r7 in    
    let r4 = field_mult(r2,r3) in
    let r8 = r4 in
    let r2 = 2w in
    let r3 = 0w in    
    let r4 = field_mult(r2,r3) in
    let r3 = m1 in
    let r2 = r4 in
    let r4 = field_mult(r2,r3) in
    let r0 = r8 in
    let r1 = r4 in
    let r0 = field_add(r0,r1) in
    let r10 = load_751 in
    let r1 = r10 - 1w in
    let r0 = field_add(r0,r1) in
    let r9 = r0 in
    let r3 = m2 in
    let r2 = 0w in
    let r4 = field_mult(r2,r3) in
    let r0 = r9 in
    let r1 = r4 in
    let r0 = field_sub(r0,r1) in
    let r8 = r0 in    
    let r9 = r11 in    
    let r4 = field_div(r8,r9) in
    let r12 = r4 in (* l *)
    let r5 = m1 in
    let r6 = 3w in
    let r7 = field_exp(r5,r6) in
    let r1 = r7 in
    let r1 = field_neg r1 in
    let r7 = r1 in
    let r10 = load_751 in
    let r3 = m1 in
    let r2 = r10 - 1w in    
    let r4 = field_mult(r2,r3) in
    let r0 = r7 in
    let r1 = r4 in
    let r0 = field_add(r0,r1) in
    let r7 = r0 in
    let r2 = 2w in
    let r3 = 0w in
    let r4 = field_mult(r2,r3) in
    let r0 = r7 in
    let r1 = r4 in
    let r0 = field_add(r0,r1) in
    let r9 = r0 in
    let r3 = m2 in
    let r2 = 1w in    
    let r4 = field_mult(r2,r3) in
    let r0 = r9 in
    let r1 = r4 in
    let r0 = field_sub(r0,r1) in
    let r8 = r0 in
    let r9 = r11 in
    let r4 = field_div(r8,r9) in
    let r11 = r4 in (* m *)
    let r5 = r12 in
    let r6 = 2w in    
    let r7 = field_exp(r5,r6) in
    let r2 = 0w in
    let r3 = r12 in    
    let r4 = field_mult(r2,r3) in
    let r0 = r7 in 
    let r1 = r4 in 
    let r0 = field_add(r0,r1) in
    let r1 = 0w in 
    let r0 = field_sub(r0,r1) in
    let r7 = r0 in
    let r3 = m1 in    
    let r2 = 2w in
    let r4 = field_mult(r2,r3) in
    let r0 = r7 in
    let r1 = r4 in
    let r0 = field_sub(r0,r1) in
    let r9 = r0 in (* x *)
    let r0 = r12 in 
    let r1 = 0w in 
    let r0 = field_add(r0,r1) in
    let r1 = r0 in
    let r1 = field_neg r1 in
    let r2 = r1 in    
    let r3 = r9 in    
    let r4 = field_mult(r2,r3) in
    let r0 = r4 in
    let r1 = r11 in 
    let r0 = field_sub(r0,r1) in
    let r1 = 1w in 
    let r0 = field_sub(r0,r1) in
    let r2 = r0 in (* y *)
    let r1 = r9 in (* x *)
      (r1,r2)`;

val (curve_add_def,_,curve_add_arm) = test_compile `
  curve_add (r1,r2,r3,r4) =
    let (r0,r1,r2,r3,r4) = both_eq(r1,r2,r3,r4) in
    if r0 = 0w then 
      let (r1,r2) = curve_double (r1,r2) in
        (r1,r2)
    else      
    let (r0,r1,r2) = both_zero(r1,r2) in
    if r0 = 0w then 
      let r1 = r3 in
      let r2 = r4 in
        (r1,r2) 
    else 
    let m1 = r1 in (* x1 *)
    let m2 = r2 in (* y1 *)
    let m3 = r3 in (* x2 *)
    let m4 = r4 in (* y2 *)
    let r1 = r3 in
    let r2 = r4 in
    let (r0,r1,r2) = both_zero(r1,r2) in
    if r0 = 0w then 
      let r1 = m1 in
      let r2 = m2 in
        (r1,r2) 
    else        
    let r0 = m1 in
    if r0 = r1 then
      let r1 = 0w in
      let r2 = 0w in
        (r1,r2)
    else
    let r0 = m3 in
    let r1 = m1 in
    let r0 = field_sub(r0,r1) in
    let r11 = r0 in (* d *)
    let r0 = m4 in
    let r1 = m2 in
    let r0 = field_sub(r0,r1) in
    let r8 = r0 in
    let r9 = r11 in
    let r4 = field_div(r8,r9) in
    let r12 = r4 in (* l *)      
    let r2 = m2 in    
    let r3 = m3 in    
    let r4 = field_mult(r2,r3) in
    let r9 = r4 in
    let r2 = m4 in    
    let r3 = m1 in    
    let r4 = field_mult(r2,r3) in
    let r0 = r9 in
    let r1 = r4 in
    let r0 = field_sub(r0,r1) in
    let r8 = r0 in
    let r9 = r11 in
    let r4 = field_div(r8,r9) in
    let r11 = r4 in (* m *)
    let r2 = 0w in
    let r3 = r12 in 
    let r4 = field_mult(r2,r3) in
    let r9 = r4 in
    let r5 = r12 in
    let r6 = 2w in
    let r7 = field_exp(r5,r6) in
    let r0 = r7 in
    let r1 = r9 in
    let r0 = field_add(r0,r1) in
    let r1 = 0w in
    let r0 = field_sub(r0,r1) in
    let r1 = m1 in
    let r0 = field_sub(r0,r1) in
    let r1 = m3 in
    let r0 = field_sub(r0,r1) in
    let r9 = r0 in (* x *)
    let r0 = r12 in
    let r1 = 0w in
    let r0 = field_add(r0,r1) in
    let r1 = r0 in
    let r1 = field_neg r1 in
    let r2 = r1 in
    let r3 = r9 in
    let r4 = field_mult(r2,r3) in
    let r0 = r4 in
    let r1 = r11 in
    let r0 = field_sub(r0,r1) in
    let r1 = 1w in
    let r0 = field_sub(r0,r1) in (* y *)
    let r1 = r9 in
    let r2 = r0 in
      (r1,r2)`;

val (curve_mult_aux_def,curve_mult_aux_ind,curve_mult_aux_arm) = test_compile `
  curve_mult_aux (m5:word32,m6:word32,m7:word32,m8:word32,m9:word32) =
    let r0 = m7 in
    if r0 = 0w then (m8,m9) else
      if r0 && 1w = 0w then 
          let r0 = r0 >>> 1 in 
          let r1 = m5 in
          let r2 = m6 in
          let m7 = r0 in
          let (r1,r2) = curve_double (r1,r2) in
          let m5 = r1 in
          let m6 = r2 in
            curve_mult_aux (m5,m6,m7,m8,m9)
        else
          let r0 = r0 >>> 1 in 
          let r1 = m5 in
          let r2 = m6 in
          let r3 = m8 in
          let r4 = m9 in
          let m7 = r0 in
          let (r1,r2) = curve_add (r1,r2,r3,r4) in
          let m8 = r1 in
          let m9 = r2 in
          let r1 = m5 in
          let r2 = m6 in
          let (r1,r2) = curve_double (r1,r2) in
          let m5 = r1 in
          let m6 = r2 in
            curve_mult_aux (m5,m6,m7,m8,m9)`;

val (curve_mult_def,_,curve_mult_arm) = test_compile `
  curve_mult (r1:word32,r2:word32,r3:word32) =
    let r0 = 0w in
    let m5 = r1 in
    let m6 = r2 in
    let m7 = r3 in
    let m8 = r0 in
    let m9 = r0 in
    let (m8,m9) = curve_mult_aux (m5,m6,m7,m8,m9) in
    let r1 = m8 in
    let r2 = m9 in
      (r1,r2)`

(*








(* ----------------- *)

val _ = reset_compiled();
val _ = abbrev_code := true;

val (load_751_def,_,load_751_arm) = test_compile `
  load_751 = 
    let r10 = 2w:word32 in
    let r10 = r10 << 8 in
    let r10 = r10 + 239w in r10`;

val (field_neg_def,_,field_neg_arm) = test_compile `
  field_neg (r1:word32,r10:word32) =
    if r1 = 0w then (r1,r10) else 
      let r1 = r10 - r1 in (r1,r10)`;

val (field_add_def,_,field_add_arm) = test_compile `
  field_add (r0:word32,r1:word32,r10:word32) =
    let r0 = r1 + r0 in
      if r0 < r10 then (r0,r10) else 
        let r0 = r0 - r10 in 
          (r0,r10)`;

val (field_sub_def,_,field_sub_arm) = test_compile `
  field_sub (r0:word32,r1:word32,r10:word32) =
    let (r1,r10) = field_neg (r1,r10) in 
    let (r0,r10) = field_add (r0,r1,r10) in 
      (r0,r10)`;

val (field_mult_aux_def,field_mult_aux_ind,field_mult_aux_arm) = test_compile `
  field_mult_aux5 (r2:word32,r3:word32,r4:word32,r10:word32) =
    if r3 = 0w then (r4,r10) else
      if r3 && 1w = 0w then 
          let r3 = r3 >>> 1 in 
          let r0 = r2 in
          let r1 = r2 in
          let (r0,r10) = field_add (r0,r1,r10) in
          let r2 = r0 in
            field_mult_aux5 (r2,r3,r4,r10)
        else
          let r3 = r3 >>> 1 in 
          let r0 = r4 in
          let r1 = r2 in
          let (r0,r10) = field_add (r0,r1,r10) in
          let r4 = r0 in
          let r0 = r2 in
          let r1 = r2 in
          let (r0,r10) = field_add (r0,r1,r10) in
          let r2 = r0 in
            field_mult_aux5 (r2,r3,r4,r10)`;

val (field_mult_def,_,field_mult_arm) = test_compile `
  field_mult (r2,r3,r10) = 
    let r4 = 0w in
    let (r4,r10) = field_mult_aux5 (r2,r3,r4,r10) in
      (r4,r10)`;

val (field_exp_aux_def,field_exp_aux_ind,field_exp_aux_arm) = test_compile `
  field_exp_aux (r5:word32,r6:word32,r7:word32,r10) =
    if r6 = 0w then (r7,r10) else
      if r6 && 1w = 0w then 
          let r6 = r6 >>> 1 in 
          let r2 = r5 in
          let r3 = r5 in
          let (r4,r10) = field_mult (r2,r3,r10) in
          let r5 = r4 in
            field_exp_aux (r5,r6,r7,r10)
        else
          let r6 = r6 >>> 1 in 
          let r2 = r7 in
          let r3 = r5 in
          let (r4,r10) = field_mult (r2,r3,r10) in
          let r7 = r4 in
          let r2 = r5 in
          let r3 = r5 in
          let (r4,r10) = field_mult (r2,r3,r10) in
          let r5 = r4 in
            field_exp_aux (r5,r6,r7,r10)`;

val (field_exp_def,_,field_exp_arm) = test_compile `
  field_exp (r5,r6,r10) = 
    let r7 = 1w in
    let (r7,r10) = field_exp_aux (r5,r6,r7,r10) in
      (r7,r10)`;

val (field_inv_def,_,field_inv_arm) = test_compile `
  field_inv (r5,r10) = 
    let r6 = 2w:word32 in
    let r6 = r6 << 8 in
    let r6 = r6 + 237w in 
    let (r7,r10) = field_exp (r5,r6,r10) in
      (r7,r10)`;

val (field_div_def,_,field_div_arm) = test_compile `
  field_div (r8,r9,r10) = 
    let r5 = r9 in
    let (r7,r10) = field_inv (r5,r10) in
    let r2 = r8 in
    let r3 = r7 in
    let (r4,r10) = field_mult(r2,r3,r10) in
      (r4,r10)`;

*)

val _ = export_theory();

