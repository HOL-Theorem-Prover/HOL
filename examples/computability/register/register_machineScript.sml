open HolKernel Parse boolLib bossLib finite_mapTheory

open recursivefnsTheory
open prnlistTheory
open primrecfnsTheory
open listTheory
open arithmeticTheory
open numpairTheory
open pred_setTheory

val _ = new_theory "register_machine";


val _ = Datatype `instruction = Inc num | Dec num | JZ num num bool`;

val _ = Datatype `RegMachine = <| insts : instruction list; regs : num |-> num; pc : num |>`;

val is_halted_def = Define`is_halted rm <=> LENGTH rm.insts <= rm.pc `;



val reg_val_def = Define`reg_val regs n = case FLOOKUP regs n of NONE => 0n | SOME x => x `;

val upd_reg_def = Define`upd_reg f n regs = regs |+ (n,f (reg_val regs n))`;

val step_def = Define`
  step rm = if is_halted rm then rm
            else case EL rm.pc rm.insts of
              Inc n => rm with <|regs updated_by upd_reg SUC n;pc updated_by SUC |>
           |  Dec n => rm with <|regs updated_by upd_reg PRE n;pc updated_by SUC |>
           | JZ n i b => if reg_val rm.regs n = 0 then rm with
                           <|pc := (if b then rm.pc + i else rm.pc-i);
                             regs updated_by upd_reg (λx. x) n|>
                         else rm with pc updated_by SUC`

val run_reg_def = Define`run_reg t reg = FUNPOW step t reg`

val init_regs_def = Define`(init_regs k [] = FEMPTY) ∧
                           (init_regs k (h::t) = (init_regs (k+1) t) |+ (k,h))`
val _ = export_rewrites["init_regs_def"]

val initial_reg_def = Define`
initial_reg inst input_list = <|insts:= inst;
                  regs :=init_regs 2 input_list; pc := 0 |>`

val reg_fun_def = Define`
reg_fun inst input = let reg0 =  initial_reg inst input in
                       OPTION_MAP (λt. (run_reg t reg0)) (OLEAST n. is_halted (run_reg n reg0))`

val FUNPOW_TWO = Q.store_thm("FUNPOW_TWO",
`FUNPOW f 2 a = f (f a)`,
`FUNPOW f 2 a = FUNPOW f (SUC (SUC 0)) a` by fs[] >> rw[FUNPOW_SUC])

val FUNPOW_THREE = Q.store_thm("FUNPOW_THREE",
`FUNPOW f 3 a = f (f (f a))`,
`FUNPOW f 3 a = FUNPOW f (SUC (SUC (SUC 0))) a` by fs[] >> rw[FUNPOW_SUC])

val Jump_def = Define`Jump i = JZ 0 i T`

val Clear_def = Define`Clear n = [JZ n 3 T;Dec n;JZ 0 2 F]`
(*
val Clear_corr = Q.store_thm("Clear_corr",
`(rm.insts = pre ++ (Clear n) ++ suff) ∧ (rm.pc = LENGTH pre)
   ==> ∃k. run_reg k rm = rm with <| pc := LENGTH pre + 3; regs := rm.regs |+(n,0) |>`,
Induct_on `reg_val rm.regs n` >> rw[]
  >- (`reg_val rm.regs n = 0` by simp[] >> fs[] >> qexists_tac `SUC 0` >>
      simp[run_reg_def,step_def,is_halted_def,Clear_def,rich_listTheory.EL_APPEND1,
           rich_listTheory.EL_APPEND2] >> simp[theorem"RegMachine_component_equality",upd_reg_def])
  >- (Q.REFINE_EXISTS_TAC `SUC (SUC (SUC k))` >> simp[run_reg_def,step_def,is_halted_def]>>
                          simp[FUNPOW,step_def,is_halted_def,LESS_EQ_ADD] ) )

val Copy_def = Define`
Copy n m =[JZ n 5 T; Dec n; Inc m; Inc 1; JZ 0 4 F; JZ 1 4 T; Dec 1; Inc n; JZ 0 3 F]`

val _ = overload_on ("zerof", ``K 0 : num list -> num``)

val init_reg_dom_less = Q.store_thm("init_reg_dom_less",
`∀ a b c. (a<b) ==> (¬(a ∈ FDOM (init_regs b c)))`,
Induct_on `c` >> fs[init_regs_def] )

val succ_inst_def = Define`succ_inst =  [Inc 2]`

val succ_reg_corr = Q.store_thm("succ_reg_corr",
`∀ args. (run_reg 2 (initial_reg succ_inst args)).regs ' 2 = succ args`,
strip_tac >> Cases_on `args` >>
          fs[run_reg_def,step_def,succ_inst_def,initial_reg_def,init_regs_def] >>
          rw[FUNPOW_TWO]
          >- (`¬ (is_halted (<|insts := [Inc 2]; regs := FEMPTY; pc := 0|>))`
by fs[is_halted_def] >> simp[step_def] >> rw[is_halted_def] >> simp[upd_reg_def,FLOOKUP_DEF])
          >- (simp[step_def,is_halted_def,upd_reg_def,FLOOKUP_DEF]))


val zerof_inst_def = Define`zerof_inst = Clear 2`

val zerof_reg_corr = Q.store_thm("zerof_reg_corr",
`∀ args. if args = [] then (run_reg 2 (initial_reg zerof_inst args)).regs ' 2 = zerof args
         else (run_reg (3 * HD args) (initial_reg zerof_inst args)).regs ' 2 = zerof args`,
strip_tac >> rw[]
  >- (simp[run_reg_def,initial_reg_def,zerof_inst_def,step_def,is_halted_def,FUNPOW_TWO,Clear_def,reg_val_def,upd_reg_def])
   >- (Cases_on `args` >> rw[] >> simp[run_reg_def,initial_reg_def,zerof_inst_def,Clear_def]>>
                Induct_on `h` >>rw[] >>simp[MULT_SUC] >> rw[FUNPOW_ADD,FUNPOW_THREE] >>
                simp[is_halted_def,step_def,Clear_def,reg_val_def,upd_reg_def,FLOOKUP_DEF]>>
       `¬(0 in FDOM (init_regs 3 t))` by fs[] >>        ) )


val proj_inst_def = Define`proj_inst i = Copy (i+2) 2`

val Cn_inst_def = Define`Cn_inst = []`

val Pr_inst_def = Define`Pr_inst = []`

val min_inst_def = Define`min_inst = [JZ ]`

EVAL ``(run_reg 11 (initial_reg (proj_inst 4) [1;2;3;4])).regs ' 2``;
EVAL ``proj 4 [1;2;3;4]``;

val proj_reg_corr = Q.store_thm("proj_reg_corr",
`∀ args i. (i < LENGTH args) ==>
          ( (run_reg (11*LENGTH args) (initial_reg (proj_inst i) args)).regs ' 2 = proj i args)`,
 rpt strip_tac >> simp[run_reg_def,proj_def,initial_reg_def,proj_inst_def,Copy_def] >>  )

val Cn_reg_corr = Q.store_thm("Cn_reg_corr",
`∀ args. OPTION_MAP ((reg_fun Cn_inst args).regs 2) = Cn [nlist_of args]`,
                                )

val Pr_reg_corr = Q.store_thm("Pr_reg_corr",
`∀ args. OPTION_MAP ((reg_fun Pr_inst args).regs 2) = Pr [nlist_of args]`,
                                )

val min_reg_corr = Q.store_thm("min_reg_corr",
`∀ args. OPTION_MAP ((reg_fun min_inst args).regs 2) = min [nlist_of args]`,
                                )



val reg_sim_pr_thm = Q.store_thm("reg_sim_pr_thm",
`∀f. ∃inst. (∀ args. OPTION_MAP ((reg_fun inst args).regs 2) = f args)`,
)

(*
We want to define the following extra instructions
Jump (z) = jump to instruction z = JZ(r0,z) for an r0 that contains 0
Clear (r) = set r to zero
Copy(ri,rj) = copy ri into rj
ADD(ri,rj,rk) = add ri and rj and put it in rk
Mult(ri,rj,rk) = multiply ri and rj and put it in rk

Zero ~ Clear
Suc ~ Inc
Identity ~
Composition ~ Concatination of instruction?
Primitive recursion?
mu operator ~ described well in bools/wiki

*)


(*
Then we need to show Turing Machine can simulate the original 3 instruction set
*)

*)

val _ = export_theory();
