
open HolKernel Parse boolLib bossLib BasicProvers;

val _ = new_theory "GraphLang";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory wordsLib pairTheory listTheory relationTheory;
open pred_setTheory arithmeticTheory combinTheory;
open arm_decompTheory set_sepTheory progTheory addressTheory;
open m0_decompTheory riscv_progTheory arm8_progTheory;
open arm_decompLib arm8_decompLib m0_decompLib;

val op by = BasicProvers.byA

val RW1 = ONCE_REWRITE_RULE;
val RW = REWRITE_RULE;

Datatype:
  variable =
    VarNone
  | VarNat num
  | VarWord8 word8
  | VarWord ('a word)
  | VarMem ('a word -> word8)
  | VarDom ('a word set)
  | VarBool bool
End

(* States are a mapping from names to the variable type, which is
   a union of the available names. *)

val _ = type_abbrev("state",``:string -> 'a variable``);

(* Accessors for grabbing variables by name and expected type. *)

val var_acc_def = zDefine `
  var_acc nm (f:'a state) = f nm`;

val var_nat_def = zDefine `
  var_nat nm st = case var_acc nm st of VarNat n => n | _ => 0`;

val var_word8_def = zDefine `
  var_word8 nm st = case var_acc nm st of VarWord8 w => w | _ => 0w`;

val var_word_def = zDefine `
  var_word nm st = case var_acc nm st of VarWord w => w | _ => 0w`;

val var_mem_def = zDefine `
  var_mem nm st = case var_acc nm st of VarMem m => m | _ => (\x. 0w)`;

val var_dom_def = zDefine `
  var_dom nm st = case var_acc nm st of VarDom d => d | _ => {}`;

val var_bool_def = zDefine `
  var_bool nm st = case var_acc nm st of VarBool b => b | _ => F`;

(* The variable updator. *)

val var_upd_def = zDefine `
  var_upd nm v f = ((nm =+ v) f)`;

val _ = zDefine `
  default_state = (\x. VarNone)`;

(* The type of nodes. *)

val _ = Datatype `next_node = NextNode num | Ret | Err`;

val _ = Datatype `node =
    Basic next_node ((string # ('a state -> 'a variable)) list)
  | Cond next_node next_node ('a state -> bool)
  | Call next_node string (('a state -> 'a variable) list) (string list)`;

val _ = zDefine `
  Skip nn = Cond nn nn (\x. T)`;

(* The type for a total graph function, including list of inputs, list
   of outputs, graph, and entry point. *)

val _ = Datatype `graph_function =
  GraphFunction (string list) (string list) (num -> 'a node option) num`;

(* The definition of execution of a single node. *)

val fold_def = zDefine `
  (fold f [] s = s) /\
  (fold f (x::xs) s = fold f xs (f x s))`;

val save_vals_def = zDefine `
  save_vals vars vals st =
    fold (\(var, val). var_upd var val) (ZIP (vars,vals)) st`;

val init_vars_def = zDefine `
  init_vars vars accs st =
    save_vals vars (MAP (\i. i st) accs) default_state`;

val return_vars_def = zDefine `
  return_vars inner outer inner_st =
    save_vals outer (MAP (\v. var_acc v inner_st) inner)`;

val upd_vars_def = zDefine `
  upd_vars upds st =
    save_vals (MAP FST upds) (MAP (\(nm, vf). vf st) upds) st`;

val _ = type_abbrev("stack",``:(next_node # 'a state # string) list``);

val upd_stack_def = zDefine `
  (upd_stack nn stf (x :: xs) = (nn, stf (FST (SND x)), SND (SND x)) :: xs) /\
  (upd_stack nn stf [] = []:'a stack)`;

val exec_node_def = zDefine `
  (exec_node Gamma st (Basic cont upds) stack =
    {upd_stack cont (K (upd_vars upds st)) stack}) /\
  (exec_node Gamma st (Cond left right cond) stack =
    {upd_stack (if cond st then left else right) I stack}) /\
  (exec_node Gamma st (Call cont fname inputs outputs) stack =
    case Gamma fname of NONE => {upd_stack Err I stack}
      | SOME (GraphFunction inps outps graph1 ep) =>
          {(NextNode ep, init_vars inps inputs st, fname) :: stack})`;

val exec_node_return_def = zDefine `
  (exec_node_return _ _ (Basic _ _) stack = {}) /\
  (exec_node_return _ _ (Cond _ _ _) stack = {}) /\
  (exec_node_return Gamma st (Call cont fname inputs outputs) stack =
     case Gamma fname of NONE => {}
       | SOME (GraphFunction inps outps graph ep) =>
            {upd_stack cont (return_vars outps outputs st) stack})`;

(* The single-step relation on graph states. *)

val exec_graph_step_def = zDefine `
  exec_graph_step Gamma stack stack' =
    case stack of
      (NextNode nn, st, fname) :: _ =>
        (case Gamma fname of | NONE => F
         | SOME (GraphFunction _ _ graph _) =>
        (case graph nn of NONE => (stack' = upd_stack Err I stack)
           | SOME node => stack' IN exec_node Gamma st node stack))
    | (Ret, st, _) :: (NextNode nn, _, fname) :: _ =>
        (case Gamma fname of | NONE => F
         | SOME (GraphFunction _ _ graph _) =>
        (case graph nn of NONE => (stack' = upd_stack Err I stack)
           | SOME node => stack' IN exec_node_return Gamma st node (TL stack)))
    | [] => F
    | [_] => F
    | _ => stack' = upd_stack Err I (TL stack)`

(* Multi-step relations. *)

val _ = zDefine `
  exec_graph Gamma = RTC (exec_graph_step Gamma)`;

val exec_graph_n_def = zDefine `
  exec_graph_n Gamma n = NRC (exec_graph_step Gamma) n`;


(* more abstract representation of graph *)

val _ = type_abbrev("update",``:(string # ('a state -> 'a variable)) list``)
val _ = type_abbrev("assert",``:'a state->bool``)

val _ = Datatype `
  jump = Jump ('a word) | Return`

val _ = Datatype `
  next = IF ('a assert) next next (* if ... then ... else ... *)
       | ASM ('a assert option) ('a update) ('a jump)
       | CALL ('a assert option) ('a update) string ('a jump)`;

val _ = Datatype `
  inst = Inst ('a word) ('a assert) ('a next) (* name, inv, what happens *)`

val _ = Datatype `
  func = Func string ('a word) ('a inst list) (* name, entry point, insts *)`;

(* execution *)

val get_assert_def = Define `
  (get_assert NONE = \x.T) /\
  (get_assert (SOME a) = a)`;

val apply_update_def = Define `
  (apply_update [] s = s) /\
  (apply_update ((x,y)::xs) s = (x =+ y s) (apply_update xs s))`;

val check_jump_def = Define `
  (check_jump (Jump p) s w = (w = p)) /\
  (check_jump Return s w = (var_word "ret" s = w))`;

val check_ret_def = Define `
  (check_ret (Jump p) s t = (var_word "ret" t = p)) /\
  (check_ret Return s t = (var_word "ret" t = var_word "ret" s))`;

val exec_next_def = Define `
  (exec_next locs (IF guard n1 n2) s t w call =
     if guard s then exec_next locs n1 s t w call
                else exec_next locs n2 s t w call) /\
  (exec_next locs (ASM assert update jmp) s t w call =
     get_assert assert s /\
     (apply_update update s = t) /\
     check_jump jmp t w /\ (call = NONE)) /\
  (exec_next locs (CALL assert update name jmp) s t w call =
     get_assert assert s /\
     (apply_update update s = t) /\
     locs name <> NONE /\
     check_jump (Jump (THE (locs name))) t w /\
     check_ret jmp s t /\ (call = SOME name))`

(* representation in ARM SPEC *)

val arm_STATE_CPSR_def = Define `
  arm_STATE_CPSR s =
    arm_CPSR_N (var_bool "n" s) *
    arm_CPSR_Z (var_bool "z" s) *
    arm_CPSR_C (var_bool "c" s) *
    arm_CPSR_V (var_bool "v" s)`;

val arm_STATE_REGS_def = Define `
  arm_STATE_REGS s =
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 0w) (var_word "r0" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 1w) (var_word "r1" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 2w) (var_word "r2" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 3w) (var_word "r3" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 4w) (var_word "r4" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 5w) (var_word "r5" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 6w) (var_word "r6" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 7w) (var_word "r7" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 8w) (var_word "r8" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 9w) (var_word "r9" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 10w) (var_word "r10" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 11w) (var_word "r11" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 12w) (var_word "r12" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 13w) (var_word "r13" s) *
    arm_REG (R_mode (w2w (var_word8 "mode" s)) 14w) (var_word "r14" s)`;

val arm_STACK_MEMORY_def = Define `
  arm_STACK_MEMORY = arm_MEMORY`;

val arm_STATE_def = Define `
  arm_STATE s =
    arm_STATE_REGS s * arm_STATE_CPSR s *
    arm_OK (w2w (var_word8 "mode" s)) *
    arm_MEMORY (var_dom "dom" s) (var_mem "mem" s) *
    arm_STACK_MEMORY (var_dom "dom_stack" s) (var_mem "stack" s)`;

val arm_STATE_thm = save_thm("arm_STATE_thm",
  arm_STATE_def
  |> REWRITE_RULE [arm_STATE_CPSR_def,arm_STATE_REGS_def,STAR_ASSOC]
  |> SPEC_ALL);

(* representation in ARM8 SPEC *)

val arm8_PSTATE_NZCV_def = Define `
  arm8_PSTATE_NZCV s =
    arm8_PSTATE_N (var_bool "n" s) *
    arm8_PSTATE_Z (var_bool "z" s) *
    arm8_PSTATE_C (var_bool "c" s) *
    arm8_PSTATE_V (var_bool "v" s)`;

val arm8_STATE_REGS_def = Define `
  arm8_STATE_REGS s =
    arm8_REG  0w (var_word  "r0" s) *
    arm8_REG  1w (var_word  "r1" s) *
    arm8_REG  2w (var_word  "r2" s) *
    arm8_REG  3w (var_word  "r3" s) *
    arm8_REG  4w (var_word  "r4" s) *
    arm8_REG  5w (var_word  "r5" s) *
    arm8_REG  6w (var_word  "r6" s) *
    arm8_REG  7w (var_word  "r7" s) *
    arm8_REG  8w (var_word  "r8" s) *
    arm8_REG  9w (var_word  "r9" s) *
    arm8_REG 10w (var_word "r10" s) *
    arm8_REG 11w (var_word "r11" s) *
    arm8_REG 12w (var_word "r12" s) *
    arm8_REG 13w (var_word "r13" s) *
    arm8_REG 14w (var_word "r14" s) *
    arm8_REG 15w (var_word "r15" s) *
    arm8_REG 16w (var_word "r16" s) *
    arm8_REG 17w (var_word "r17" s) *
    arm8_REG 18w (var_word "r18" s) *
    arm8_REG 19w (var_word "r19" s) *
    arm8_REG 20w (var_word "r20" s) *
    arm8_REG 21w (var_word "r21" s) *
    arm8_REG 22w (var_word "r22" s) *
    arm8_REG 23w (var_word "r23" s) *
    arm8_REG 24w (var_word "r24" s) *
    arm8_REG 25w (var_word "r25" s) *
    arm8_REG 26w (var_word "r26" s) *
    arm8_REG 27w (var_word "r27" s) *
    arm8_REG 28w (var_word "r28" s) *
    arm8_REG 29w (var_word "r29" s) *
    arm8_REG 30w (var_word "r30" s) *
    arm8_REG 31w (var_word "r31" s) *
    arm8_SP_EL0 (var_word "sp" s)`;

val arm8_STACK_MEMORY_def = Define `
  arm8_STACK_MEMORY = arm8_MEMORY`;

val arm8_STATE_def = Define `
  arm8_STATE s =
    arm8_STATE_REGS s * arm8_PSTATE_NZCV s *
    arm8_MEMORY (var_dom "dom" s) (var_mem "mem" s) *
    arm8_STACK_MEMORY (var_dom "dom_stack" s) (var_mem "stack" s)`;

val arm8_STATE_thm = save_thm("arm8_STATE_thm",
  arm8_STATE_def
  |> REWRITE_RULE [arm8_PSTATE_NZCV_def,arm8_STATE_REGS_def,STAR_ASSOC]
  |> SPEC_ALL);

(* representation in M0 SPEC *)

val m0_STATE_PSR_def = Define `
  m0_STATE_PSR s =
    m0_PSR_N (var_bool "n" s) *
    m0_PSR_Z (var_bool "z" s) *
    m0_PSR_C (var_bool "c" s) *
    m0_PSR_V (var_bool "v" s)`;

val m0_STATE_REGS_def = Define `
  m0_STATE_REGS s =
    m0_REG RName_0 (var_word "r0" s) *
    m0_REG RName_1 (var_word "r1" s) *
    m0_REG RName_2 (var_word "r2" s) *
    m0_REG RName_3 (var_word "r3" s) *
    m0_REG RName_4 (var_word "r4" s) *
    m0_REG RName_5 (var_word "r5" s) *
    m0_REG RName_6 (var_word "r6" s) *
    m0_REG RName_7 (var_word "r7" s) *
    m0_REG RName_8 (var_word "r8" s) *
    m0_REG RName_9 (var_word "r9" s) *
    m0_REG RName_10 (var_word "r10" s) *
    m0_REG RName_11 (var_word "r11" s) *
    m0_REG RName_12 (var_word "r12" s) *
    m0_REG RName_SP_main (var_word "r13" s) *
    m0_REG RName_LR (var_word "r14" s)`;

val m0_STACK_MEMORY_def = Define `
  m0_STACK_MEMORY = m0_MEMORY`;

val m0_STATE_def = Define `
  m0_STATE s =
    m0_STATE_REGS s * m0_STATE_PSR s *
    m0_CurrentMode Mode_Thread *
    m0_MEMORY (var_dom "dom" s) (var_mem "mem" s) *
    m0_STACK_MEMORY (var_dom "dom_stack" s) (var_mem "stack" s) *
    m0_COUNT (var_nat "clock" s)`;

val m0_STATE_thm = save_thm("m0_STATE_thm",
  m0_STATE_def
  |> REWRITE_RULE [m0_STATE_PSR_def,m0_STATE_REGS_def,STAR_ASSOC]
  |> SPEC_ALL);

(* representation in RISCV-V SPEC *)

val riscv_STATE_REGS_def = Define `
  riscv_STATE_REGS s =
    riscv_REG 0w (var_word "r0" s) *
    riscv_REG 1w (var_word "r1" s) *
    riscv_REG 2w (var_word "r2" s) *
    riscv_REG 3w (var_word "r3" s) *
    riscv_REG 4w (var_word "r4" s) *
    riscv_REG 5w (var_word "r5" s) *
    riscv_REG 6w (var_word "r6" s) *
    riscv_REG 7w (var_word "r7" s) *
    riscv_REG 8w (var_word "r8" s) *
    riscv_REG 9w (var_word "r9" s) *
    riscv_REG 10w (var_word "r10" s) *
    riscv_REG 11w (var_word "r11" s) *
    riscv_REG 12w (var_word "r12" s) *
    riscv_REG 13w (var_word "r13" s) *
    riscv_REG 14w (var_word "r14" s) *
    riscv_REG 15w (var_word "r15" s) *
    riscv_REG 16w (var_word "r16" s) *
    riscv_REG 17w (var_word "r17" s) *
    riscv_REG 18w (var_word "r18" s) *
    riscv_REG 19w (var_word "r19" s) *
    riscv_REG 20w (var_word "r20" s) *
    riscv_REG 21w (var_word "r21" s) *
    riscv_REG 22w (var_word "r22" s) *
    riscv_REG 23w (var_word "r23" s) *
    riscv_REG 24w (var_word "r24" s) *
    riscv_REG 25w (var_word "r25" s) *
    riscv_REG 26w (var_word "r26" s) *
    riscv_REG 27w (var_word "r27" s) *
    riscv_REG 28w (var_word "r28" s) *
    riscv_REG 29w (var_word "r29" s) *
    riscv_REG 30w (var_word "r30" s) *
    riscv_REG 31w (var_word "r31" s)`;

val riscv_STACK_MEMORY_def = Define `
  riscv_STACK_MEMORY = riscv_MEMORY`;

val riscv_STATE_def = Define `
  riscv_STATE s =
    riscv_STATE_REGS s * ~riscv_RV64I *
    riscv_MEMORY (var_dom "dom" s) (var_mem "mem" s) *
    riscv_STACK_MEMORY (var_dom "dom_stack" s) (var_mem "stack" s)`;

val riscv_STATE_thm = save_thm("riscv_STATE_thm",
  riscv_STATE_def
  |> REWRITE_RULE [riscv_STATE_REGS_def,STAR_ASSOC]
  |> SPEC_ALL);

(* misc *)

val var_update_thm = store_thm("var_update_thm",
  ``(var_dom n ((n1 =+ x) s) =
      if n = n1 then (case x of VarDom y => y | _ => EMPTY) else
        var_dom n s) /\
    (var_nat n ((n1 =+ x) s) =
      if n = n1 then (case x of VarNat y => y | _ => 0) else
        var_nat n s) /\
    (var_word8 n ((n1 =+ x) s) =
      if n = n1 then (case x of VarWord8 y => y | _ => 0w) else
        var_word8 n s) /\
    (var_word n ((n1 =+ x) s) =
      if n = n1 then (case x of VarWord y => y | _ => 0w) else
        var_word n s) /\
    (var_mem n ((n1 =+ x) s) =
      if n = n1 then (case x of VarMem y => y | _ => \x. 0w) else
        var_mem n s) /\
    (var_bool n ((n1 =+ x) s) =
      if n = n1 then (case x of VarBool y => y | _ => F) else
        var_bool n s)``,
  SRW_TAC [] [var_dom_def,var_mem_def,var_bool_def,var_nat_def,
     var_word8_def,var_word_def,var_acc_def,APPLY_UPDATE_THM]);

val all_names_def = Define `
  all_names =
    ["r0"; "r1"; "r2"; "r3"; "r4"; "r5"; "r6"; "r7"; "r8"; "r9";
     "r10"; "r11"; "r12"; "r13"; "r14"; "r15"; "r16"; "r17"; "r18"; "r19";
     "r20"; "r21"; "r22"; "r23"; "r24"; "r25"; "r26"; "r27"; "r28"; "r29";
     "r30"; "r31"; "sp"; "mode"; "n"; "z"; "c"; "v";
     "mem"; "dom"; "stack"; "dom_stack"; "clock"]`;

val ret_and_all_names_def = Define `
  ret_and_all_names = "ret"::all_names ++ ["ret_addr_input"]`;

val all_names_ignore_def = Define `
  all_names_ignore = all_names ++ ["ret_addr_input_ignore"]`;

val all_names_with_input_def = Define `
  all_names_with_input = all_names ++ ["ret_addr_input"]`;

val LIST_SUBSET_def = Define `
  LIST_SUBSET xs ys = EVERY (\x. MEM x ys) xs`;

val upd_ok_def = Define `
  upd_ok u = ALL_DISTINCT (MAP FST u) /\
             LIST_SUBSET (MAP FST u) all_names`;

val jump_ok_def = Define `
  (jump_ok (Jump p) = EVEN (w2n p)) /\
  (jump_ok Return = T)`;

val next_ok_def = Define `
  (next_ok (ASM s u l) = upd_ok u /\ jump_ok l) /\
  (next_ok (IF b n1 n2) = next_ok n1 /\ next_ok n2) /\
  (next_ok (CALL a u n j) =
     (MAP FST u = ret_and_all_names) /\ jump_ok j /\
     !st. check_ret j st (apply_update u st))`

val IMPL_INST_def = Define `
  IMPL_INST code locs (Inst (n:'a word) assert next) =
    next_ok next /\ EVEN (w2n n) /\
    !s t call w.
      assert s /\ exec_next locs next s t w call ==>
      let (c,m,x,p) = code in SPEC m (x s * p n) c (x t * p w)`;

val a_tools  = ``(ARM_MODEL,arm_STATE,arm_PC)``
val a8_tools = ``(ARM8_MODEL,arm8_STATE,arm8_pc)``
val m_tools  = ``(M0_MODEL,m0_STATE,m0_PC)``
val r_tools  = ``(RISCV_MODEL,riscv_STATE,riscv_PC)``

val ARM_def = Define `ARM (c:((word32 # word32) set)) = (c,^a_tools)`;
val ARM8_def = Define `ARM8 (c:((word64 # word32) set)) = (c,^a8_tools)`;
val M0_def = Define `M0 (c:(word32 # (word16 + word32)) set) = (c,^m_tools)`;
val RISCV_def = Define `RISCV (c:(word64 # (word8 list)) set) = (c,^r_tools)`;

val _ = ``IMPL_INST (ARM _)``;
val _ = ``IMPL_INST (ARM8 _)``;
val _ = ``IMPL_INST (M0 _)``;
val _ = ``IMPL_INST (RISCV _)``;

val IMPL_INST_IF = store_thm("IMPL_INST_IF",
  ``IMPL_INST code locs (Inst pc1 assert1 next1) /\
    IMPL_INST code locs (Inst pc1 assert2 next2) ==>
    (!s. assert1 s ==> assert2 s) ==>
    !guard. IMPL_INST code locs (Inst pc1 assert1 (IF guard next1 next2))``,
  SIMP_TAC std_ss [IMPL_INST_def,exec_next_def,next_ok_def] \\ METIS_TAC []);

val IMPL_INST_IF_ALT = store_thm("IMPL_INST_IF_ALT",
  ``IMPL_INST code locs (Inst pc1 assert1 next1) /\
    IMPL_INST code locs (Inst pc1 assert2 next2) ==>
    !guard. IMPL_INST code locs
       (Inst pc1 (\s. if guard s then assert1 s else assert2 s)
          (IF guard next1 next2))``,
  SIMP_TAC std_ss [IMPL_INST_def,exec_next_def,next_ok_def] \\ METIS_TAC []);

val IMPL_INST_SIMP_IF = store_thm("IMPL_INST_SIMP_IF",
  ``IMPL_INST code locs
      (Inst pc assert (IF guard (ASM (SOME s1) up1 j1)
                                (ASM (SOME s2) up2 j2))) <=>
    IMPL_INST code locs
      (Inst pc assert (IF guard (ASM (SOME (\s. guard s ==> s1 s)) up1 j1)
                                (ASM (SOME (\s. ~guard s ==> s2 s)) up2 j2)))``,
  SIMP_TAC std_ss [IMPL_INST_def,exec_next_def,get_assert_def,next_ok_def]);

val IMPL_INST_IF_RW = store_thm("IMPL_INST_IF_RW",
  ``(IMPL_INST code locs
      (Inst pc assert (IF guard (ASM (SOME (\s. T)) up1 j1) next)) <=>
     IMPL_INST code locs
      (Inst pc assert (IF guard (ASM NONE up1 j1) next))) /\
    (IMPL_INST code locs
      (Inst pc assert (IF guard next (ASM (SOME (\s. T)) up1 j1))) <=>
     IMPL_INST code locs
      (Inst pc assert (IF guard next (ASM NONE up1 j1))))``,
  SIMP_TAC std_ss [IMPL_INST_def,exec_next_def,get_assert_def,next_ok_def]);

val IMPL_INST_IF_SPLIT = store_thm("IMPL_INST_IF_SPLIT",
  ``IMPL_INST c locs (Inst n b (IF g (ASM x u (Jump j)) next)) <=>
    IMPL_INST c locs (Inst n (\s. b s /\ g s) (ASM x u (Jump j))) /\
    IMPL_INST c locs (Inst n (\s. b s /\ ~(g s)) next)``,
  SIMP_TAC std_ss [IMPL_INST_def,check_jump_def,exec_next_def,next_ok_def]
  \\ METIS_TAC []);

val IMPL_INST_IF_SIMP1 = store_thm("IMPL_INST_IF_SIMP1",
  ``IMPL_INST c locs (Inst n (K T) (IF g next1 next2)) ==>
    !a. (!s. a s ==> g s) ==> IMPL_INST c locs (Inst n a next1)``,
  SIMP_TAC std_ss [IMPL_INST_def,check_jump_def,exec_next_def,next_ok_def]
  \\ METIS_TAC []);

val IMPL_INST_IF_SIMP2 = store_thm("IMPL_INST_IF_SIMP2",
  ``IMPL_INST c locs (Inst n (K T) (IF g next1 next2)) ==>
    !a. (!s. a s ==> ($~ o g) s) ==> IMPL_INST c locs (Inst n a next2)``,
  SIMP_TAC std_ss [IMPL_INST_def,check_jump_def,exec_next_def,next_ok_def]
  \\ METIS_TAC []);

val IMPL_INST_SET_ASSUM = store_thm("IMPL_INST_SET_ASSUM",
  ``IMPL_INST c locs (Inst n (K T) next) ==>
    !a. IMPL_INST c locs (Inst n a next)``,
  SIMP_TAC std_ss [IMPL_INST_def,check_jump_def,exec_next_def]
  \\ METIS_TAC []);

val IMPL_INST_IF_COMPOSE1 = store_thm("IMPL_INST_IF_COMPOSE1",
  ``IMPL_INST c locs (Inst n b (IF g (ASM pre u1 (Jump w)) next)) /\
    IMPL_INST c locs (Inst w g (ASM NONE [] (Jump j))) ==>
    (!s. g s ==> g (apply_update u1 s)) ==>
    IMPL_INST c locs (Inst n b (IF g (ASM pre u1 (Jump j)) next))``,
  PairCases_on `c`
  \\ rename [`(c,m,c6,c7)`]
  \\ SIMP_TAC (srw_ss()) [IMPL_INST_def,check_jump_def,exec_next_def,next_ok_def]
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `g s`)
  \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Q.PAT_ASSUM `!s t cc. bbb` (MP_TAC o Q.SPECL [`s`,`t`,`call`,`w'`])
          \\ FULL_SIMP_TAC std_ss [] \\ NO_TAC)
  \\ rpt BasicProvers.TOP_CASE_TAC \\ rpt var_eq_tac \\ fs []
  \\ MATCH_MP_TAC (progTheory.SPEC_COMPOSE
                   |> Q.SPECL [`x`,`p`,`c`,`m`,`c`,`q`]
                   |> SIMP_RULE std_ss [UNION_IDEMPOT] |> GEN_ALL)
  \\ fs []
  \\ first_x_assum (qspecl_then [`s`,`apply_update u1 s`] mp_tac)
  \\ fs [] \\ strip_tac
  \\ FULL_SIMP_TAC std_ss [get_assert_def,apply_update_def] \\ METIS_TAC []);

val IMPL_INST_IF_COMPOSE2 = store_thm("IMPL_INST_IF_COMPOSE2",
  ``IMPL_INST c locs (Inst n b (IF g next (ASM pre u1 (Jump w)))) /\
    IMPL_INST c locs (Inst w ($~ o g) (ASM NONE [] (Jump j))) ==>
    (!s. g (apply_update u1 s) <=> g s) ==>
    IMPL_INST c locs (Inst n b (IF g next (ASM pre u1 (Jump j))))``,
  PairCases_on `c`
  \\ rename [`(c,m,c6,c7)`]
  \\ SIMP_TAC (srw_ss()) [IMPL_INST_def,check_jump_def,exec_next_def,next_ok_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `g s`
  \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Q.PAT_ASSUM `!s t cc. bbb` (MP_TAC o Q.SPECL [`s`,`t`,`call`,`w'`])
          \\ FULL_SIMP_TAC std_ss [] \\ NO_TAC)
  \\ rpt BasicProvers.TOP_CASE_TAC \\ rpt var_eq_tac \\ fs []
  \\ MATCH_MP_TAC (progTheory.SPEC_COMPOSE
                   |> Q.SPECL [`x`,`p`,`c`,`m`,`c`,`q`]
                   |> SIMP_RULE std_ss [UNION_IDEMPOT] |> GEN_ALL)
  \\ fs []
  \\ first_x_assum (qspecl_then [`s`,`apply_update u1 s`] mp_tac)
  \\ fs [] \\ strip_tac
  \\ FULL_SIMP_TAC std_ss [get_assert_def,apply_update_def] \\ METIS_TAC []);

val LESS_EQ_APPEND = store_thm("LESS_EQ_APPEND",
  ``!xs n. n <= LENGTH xs ==> ?ys zs. (xs = ys ++ zs) /\ (LENGTH ys = n)``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [LENGTH,APPEND]);

val EL_LENGTH_APPEND = store_thm("EL_LENGTH_APPEND",
  ``!n xs ys. (EL (LENGTH xs) (xs ++ ys) = EL 0 ys) /\
              (EL (LENGTH xs + n) (xs ++ ys) = EL n ys)``,
  REPEAT STRIP_TAC \\ `LENGTH xs <= LENGTH xs + n` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2]);

val DROP_LENGTH_ADD_APPEND = store_thm("DROP_LENGTH_ADD_APPEND",
  ``!xs n ys. DROP (LENGTH xs + n) (xs ++ ys) = DROP n ys``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [LENGTH,ADD_CLAUSES]);

val LUPDATE_LENGTH_ADD_APPEND = store_thm("LUPDATE_LENGTH_ADD_APPEND",
  ``!xs x n ys. (LUPDATE x (LENGTH xs) (xs ++ ys) = xs ++ LUPDATE x 0 ys) /\
                (LUPDATE x (LENGTH xs + n) (xs ++ ys) = xs ++ LUPDATE x n ys)``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [LENGTH,ADD_CLAUSES,LUPDATE_def]);

val EL_LENGTH_REVERSE_APPEND = store_thm("EL_LENGTH_REVERSE_APPEND",
  ``(EL (LENGTH xs + n) (REVERSE xs ++ ys) = EL n ys) /\
    (EL (LENGTH xs) (REVERSE xs ++ ys) = EL 0 ys)``,
  ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [EL_LENGTH_APPEND]);

val arm_STATE_all_names = store_thm("arm_STATE_all_names",
  ``EVERY (\n. s1 n = s2 n) all_names ==>
    (arm_STATE s1 = arm_STATE s2)``,
  SIMP_TAC std_ss [arm_STATE_thm,EVERY_DEF,all_names_def,
    var_word8_def,var_dom_def,var_mem_def,var_nat_def,
    var_word_def,STAR_ASSOC,var_acc_def,var_bool_def]);

val arm8_STATE_all_names = store_thm("arm8_STATE_all_names",
  ``EVERY (\n. s1 n = s2 n) all_names ==>
    (arm8_STATE s1 = arm8_STATE s2)``,
  SIMP_TAC std_ss [arm8_STATE_thm,EVERY_DEF,all_names_def,
    var_word8_def,var_dom_def,var_mem_def,var_nat_def,
    var_word_def,STAR_ASSOC,var_acc_def,var_bool_def]);

val m0_STATE_all_names = store_thm("m0_STATE_all_names",
  ``EVERY (\n. s1 n = s2 n) all_names ==>
    (m0_STATE s1 = m0_STATE s2)``,
  SIMP_TAC std_ss [m0_STATE_thm,EVERY_DEF,all_names_def,
    var_word8_def,var_dom_def,var_mem_def,var_nat_def,
    var_word_def,STAR_ASSOC,var_acc_def,var_bool_def]);

val riscv_STATE_all_names = store_thm("riscv_STATE_all_names",
  ``EVERY (\n. s1 n = s2 n) all_names ==>
    (riscv_STATE s1 = riscv_STATE s2)``,
  SIMP_TAC std_ss [riscv_STATE_thm,EVERY_DEF,all_names_def,
    var_word8_def,var_dom_def,var_mem_def,var_nat_def,
    var_word_def,STAR_ASSOC,var_acc_def,var_bool_def]);

(* translation from my graph lang to Tom's *)

val get_jump_def = Define `
  (get_jump (Jump j) = NextNode (w2n j)) /\
  (get_jump Return = Ret)`;

val next_trans_def = Define `
  (next_trans n t (ASM NONE upd jump) =
    (t,
     [(n,Basic (get_jump jump) upd)])) /\
  (next_trans n t (ASM (SOME a) upd jump) =
    (t+2,
     [(n,Cond (NextNode t) Err a);
      (t,Basic (get_jump jump) upd)])) /\
  (next_trans n t (IF guard n1 n2) =
     let (t1,xs) = next_trans t (t+4) n1 in
     let (t2,ys) = next_trans (t+2) t1 n2 in
       (t2,[(n,Cond (NextNode t) (NextNode (t+2)) guard)] ++ xs ++ ys)) /\
  (next_trans n t (CALL a upd name r) =
    (t+2,
     [(n,Cond (NextNode t) Err (get_assert a));
      (t,Call (get_jump r) name (MAP SND upd) all_names_ignore)]))`

val inst_trans_def = Define `
  inst_trans t (Inst l _ next) = next_trans (w2n l) t next`;

val list_inst_trans_def = Define `
  (list_inst_trans t [] = []) /\
  (list_inst_trans t (x::xs) =
     let (t1,ys) = inst_trans t x in
       ys ++ list_inst_trans t1 xs)`;

val graph_def = zDefine `
  (graph [] = K NONE) /\
  (graph ((x,y)::xs) = (x =+ SOME y) (graph xs))`;

val func_trans_def = zDefine `
  func_trans (Func name entry l) =
    (name,GraphFunction ret_and_all_names all_names_with_input
            (graph (list_inst_trans 1 l)) (w2n entry))`;

val list_func_trans_def = zDefine `
  list_func_trans fs = graph (MAP func_trans fs)`;

(* condition decompiler has to prove *)

val inst_loc_def = Define `
  inst_loc (Inst loc _ _) = w2n loc`;

val fs_locs_def = Define `
  (fs_locs [] = K NONE) /\
  (fs_locs ((Func name entry l)::xs) = (name =+ SOME entry) (fs_locs xs))`;

val func_ok_def = Define `
  func_ok code names (Func name entry l) =
    ALL_DISTINCT (MAP inst_loc l) /\ EVEN (w2n entry) /\
    !i assert next.
      MEM (Inst i assert next) l ==>
      IMPL_INST code names (Inst i assert next) /\ (assert = K T)`;

val funcs_ok_def = Define `
  funcs_ok code fs = EVERY (func_ok code (fs_locs fs)) fs`;

(* proving a simulation result *)

val find_inst_def = Define `
  (find_inst n [] = NONE) /\
  (find_inst n ((Inst l asrt next)::xs) =
     if l = n then SOME (Inst l asrt next) else find_inst n xs)`;

val find_func_def = Define `
  (find_func n [] = NONE) /\
  (find_func n ((Func name entry insts)::xs) =
     if n = name then SOME (Func name entry insts) else find_func n xs)`;

val good_stack_tail_def = Define `
  (good_stack_tail fs ([]:'a stack) = T) /\
  (good_stack_tail fs [x] = T) /\
  (good_stack_tail fs ((l1,s1,n1)::(l2,s2,n2)::xs) =
     good_stack_tail fs ((l2,s2,n2)::xs) /\
     ?n x1 x2 g x3 ret y1 y2 y3.
       (l2 = NextNode n) /\
       (list_func_trans fs n2 = SOME (GraphFunction x1 x2 g x3)) /\
       (g n = SOME (Call ret y1 y2 y3)) /\
       (case ret of
        | NextNode i => (var_word "ret" s1 = n2w i) /\ EVEN i
        | Ret => (var_word "ret" s1 = var_word "ret" s2)
        | Err => F))`

val good_stack_def = Define `
  good_stack fs stack =
    good_stack_tail fs stack /\
    (case FST (HD stack) of
     | Err => F
     | NextNode n => EVEN n
     | Ret => T)`;

val NRC_Err = prove(
  ``!n s st name s2.
      NRC (exec_graph_step Gamma) n ((Err,st,name)::s) s2 ==>
      ~(good_stack fs s2)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [good_stack_def,NRC,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ Q.PAT_ASSUM `exec_graph_step Gamma ((Err,st,name)::s) z` MP_TAC
  \\ SIMP_TAC (srw_ss()) [exec_graph_step_def,upd_stack_def]
  \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ PairCases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [upd_stack_def]
  \\ METIS_TAC []);

val list_func_trans_EQ_SOME_IMP = prove(
  ``!fs.
      (list_func_trans fs name = SOME (GraphFunction x1 x2 graph1 x3)) ==>
      ?entry l. (find_func name fs = SOME (Func name entry l)) /\
                (x1 = ret_and_all_names) /\ (x2 = all_names_with_input) /\
                (x3 = w2n entry) /\
                (graph1 = graph (list_inst_trans 1 l)) /\
                (fs_locs fs name = SOME (n2w x3))``,
  Induct \\ FULL_SIMP_TAC std_ss [list_func_trans_def,MAP,graph_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [func_trans_def,graph_def,fs_locs_def]
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,find_func_def]
  \\ STRIP_TAC \\ Cases_on `s = name` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [RW1[MULT_COMM]MULT_DIV,n2w_w2n]);

val odd_nums_def = Define `
  (odd_nums k 0 = []) /\
  (odd_nums k (SUC n) = (k:num) :: odd_nums (k+2) n)`;

val odd_nums_ADD = prove(
  ``!m n k. odd_nums k (m + n) = odd_nums k m ++ odd_nums (k + 2 * m) n``,
  Induct \\ FULL_SIMP_TAC std_ss [odd_nums_def,APPEND,ADD_CLAUSES,
    MULT_CLAUSES,ADD_ASSOC]);

val next_trans_IMP = prove(
  ``!nn n k k1 xs.
      ODD k /\ (next_trans n k nn = (k1,xs)) ==>
      ?y ys. (xs = (n,y)::ys) /\ EVERY (ODD o FST) ys /\ ODD k1 /\
            PERM (MAP FST xs) (n :: odd_nums k (LENGTH (TL xs))) /\
            (k1 = k + 2 * (LENGTH (TL xs)))``,
  REVERSE Induct
  \\ SIMP_TAC (srw_ss()) [next_trans_def,LET_DEF,CONS_11,EVERY_DEF,ODD_ADD]
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  THEN1 (Cases
         \\ EVAL_TAC \\ SIMP_TAC (srw_ss()) [] \\ EVAL_TAC \\ SRW_TAC [] []
         \\ FULL_SIMP_TAC std_ss [ODD_ADD])
  \\ REPEAT STRIP_TAC
  \\ Cases_on `next_trans k (k + 4) nn` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `next_trans (k + 2) q nn'` \\ FULL_SIMP_TAC std_ss []
  \\ `ODD (k + 4) /\ ODD (k + 2)` by FULL_SIMP_TAC (srw_ss()) [ODD_ADD]
  \\ RES_TAC \\ RES_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bb` (K ALL_TAC))  \\ REVERSE (SRW_TAC [] [])
  \\ FULL_SIMP_TAC std_ss [odd_nums_def,CONS_11]
  \\ FULL_SIMP_TAC std_ss [sortingTheory.PERM_CONS_IFF,MAP,TL]
  THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [ADD_CLAUSES,odd_nums_def]
  \\ MATCH_MP_TAC sortingTheory.APPEND_PERM_SYM
  \\ FULL_SIMP_TAC std_ss [sortingTheory.PERM_CONS_IFF,MAP,TL,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
  \\ MATCH_MP_TAC sortingTheory.APPEND_PERM_SYM
  \\ FULL_SIMP_TAC std_ss [odd_nums_ADD]
  \\ MATCH_MP_TAC sortingTheory.PERM_CONG
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]);

val next_trans_lemma = prove(
  ``!nn n k k1 xs.
      ODD k /\ (next_trans n k nn = (k1,xs)) ==>
      ?y ys. (xs = (n,y)::ys) /\ EVERY (ODD o FST) ys /\ ODD k1``,
  METIS_TAC [next_trans_IMP]);

val graph_APPEND_ODD = prove(
  ``!ys.
      EVERY (ODD o FST) ys ==>
      (graph (ys ++ xs) (2 * m) = graph xs (2 * m))``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,FORALL_PROD,EVERY_DEF,graph_def,
       APPLY_UPDATE_THM]
  \\ SRW_TAC [] [] \\ IMP_RES_TAC EVEN_ODD_EXISTS
  \\ Q.MATCH_ASSUM_RENAME_TAC `2 * m = SUC (2 * n)`
  \\ `(2 * m) MOD 2 = (SUC (2 * n)) MOD 2` by METIS_TAC []
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ FULL_SIMP_TAC (srw_ss()) [MOD_MULT,ADD1]
  \\ ONCE_REWRITE_TAC [DECIDE ``m * 2 = m * 2 + 0:num``]
  \\ FULL_SIMP_TAC (srw_ss()) [MOD_MULT,ADD1]);

val graph_list_inst_trans_EQ_SOME_IMP = prove(
  ``!l k n x.
      ODD k /\ EVEN n /\ n < dimword (:'a) /\
      (graph (list_inst_trans k l) n = SOME x) ==>
      ?a t. find_inst ((n2w n) :'a word) l = SOME (Inst (n2w n) a t)``,
  Induct \\ FULL_SIMP_TAC std_ss [list_inst_trans_def,graph_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [inst_trans_def,find_inst_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `next_trans (w2n c) k n`
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC next_trans_lemma
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [APPEND,graph_def,APPLY_UPDATE_THM]
  \\ Cases_on `c` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.MATCH_ASSUM_RENAME_TAC `n1 ≠ n2 MOD dimword (:'a)`
  \\ IMP_RES_TAC (EVEN_ODD_EXISTS |> SPEC_ALL |> CONJUNCT1)
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ Q.EXISTS_TAC `q` \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 3 (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss [graph_APPEND_ODD]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val MEM_IMP_graph_SOME = prove(
  ``!nodes i x.
      MEM (i,x) nodes /\ ALL_DISTINCT (MAP FST nodes) ==>
      (graph nodes i = SOME x)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [FORALL_PROD,MEM_MAP,graph_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `p_1 = i` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]);

val exec_graph_step_NOT_ZERO = prove(
  ``!s2. NRC (exec_graph_step (list_func_trans fs)) n
      ((NextNode k,st,name)::t) s2 /\ ODD k /\ good_stack fs s2 ==> n <> 0``,
  Cases_on `n`
  \\ FULL_SIMP_TAC (srw_ss()) [ADD1,NRC,good_stack_def,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [EVEN_ODD]
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss []);

val ZIP_MAP_MAP = prove(
  ``!xs f g. ZIP (MAP f xs, MAP g xs) = MAP (\x. (f x, g x)) xs``,
  Induct \\ SRW_TAC [] []);

val NOT_MEM_IMP_fold_var_upd_ALT = prove(
  ``!l st x y.
      ~(MEM x (MAP FST l)) ==>
      (fold (\(var,val). var_upd var val) l ((x =+ y) st) =
       (x =+ y) (fold (\(var,val). var_upd var val) l st))``,
  Induct \\ SRW_TAC [] [fold_def,var_upd_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [fold_def,var_upd_def]
  \\ `((q =+ r) ((x =+ y) st)) = ((x =+ y) ((q =+ r) st))`
        by METIS_TAC [UPDATE_COMMUTES] \\ METIS_TAC []);

val NOT_MEM_IMP_fold_var_upd = prove(
  ``!l st x y.
      ~(MEM x (MAP FST l)) ==>
      (fold (\(var,val). var_upd var val) (MAP (\(p1,p2). (p1,p2 st1)) l)
         ((x =+ y st1) st) =
       (x =+ y st1)
          (fold (\(var,val). var_upd var val) (MAP (\(p1,p2). (p1,p2 st1)) l) st))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC NOT_MEM_IMP_fold_var_upd_ALT
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,FORALL_PROD]);

val NOT_MEM_IMP_fold_var_upd_HO = prove(
  ``!l st x y.
      ~(MEM x (MAP FST l)) ==>
      (fold (\(var,val). var_upd var (val t)) l ((x =+ y t) st) =
       (x =+ y t) (fold (\(var,val). var_upd var (val t)) l st))``,
  Induct \\ SRW_TAC [] [fold_def,var_upd_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [fold_def,var_upd_def]
  \\ `((q =+ r t) ((x =+ y t) st)) = ((x =+ y t) ((q =+ r t) st))`
        by METIS_TAC [UPDATE_COMMUTES] \\ METIS_TAC []);

val upd_vars_thm = prove(
  ``!l st. upd_ok l ==> (upd_vars l st = apply_update l st)``,
  SIMP_TAC std_ss [upd_vars_def,save_vals_def,ZIP_MAP_MAP,LAMBDA_PROD]
  \\ Induct
  \\ FULL_SIMP_TAC std_ss [apply_update_def,FORALL_PROD,MAP,fold_def,var_upd_def]
  \\ FULL_SIMP_TAC std_ss [upd_ok_def,ALL_DISTINCT,MAP]
  \\ FULL_SIMP_TAC std_ss [NOT_MEM_IMP_fold_var_upd]
  \\ REPEAT STRIP_TAC \\ AP_TERM_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [LIST_SUBSET_def,EVERY_DEF]);

val fold_MAP = prove(
  ``!xs f g s. fold f (MAP g xs) s = fold (f o g) xs s``,
  Induct \\ SRW_TAC [] [fold_def,MAP]);

val fold_EQ_apply_update = prove(
  ``!l s1 s2 n.
      ALL_DISTINCT (MAP FST l) /\ MEM n (MAP FST l) ==>
      (fold (\x. var_upd (FST x) (SND x st)) l s1 n =
       apply_update l st n)``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,MAP,ALL_DISTINCT]
  \\ Cases \\ FULL_SIMP_TAC std_ss [fold_def,var_upd_def,LAMBDA_PROD]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [NOT_MEM_IMP_fold_var_upd_HO,apply_update_def]
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val upd_ok_IMP_var_word_ret = prove(
  ``!l. upd_ok l ==>
        (var_word "ret" (apply_update l st) = var_word "ret" st)``,
  Induct \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [apply_update_def,upd_ok_def,MAP,LIST_SUBSET_def,
       EVERY_DEF,ALL_DISTINCT,var_word_def,var_acc_def,
       APPLY_UPDATE_THM]
  \\ `~MEM "ret" all_names` by ALL_TAC
  THEN1 (SIMP_TAC std_ss [all_names_def] \\ EVAL_TAC)
  \\ SRW_TAC [] []);

val good_stack_tail_UPDATE = prove(
  ``good_stack_tail fs ((i,st,name)::t) /\ upd_ok l ==>
    good_stack_tail fs ((i,apply_update l st,name)::t)``,
  Cases_on `t` \\ FULL_SIMP_TAC std_ss [good_stack_tail_def]
  \\ PairCases_on `h` \\ FULL_SIMP_TAC std_ss [good_stack_tail_def]
  \\ Cases_on `upd_ok l` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC upd_ok_IMP_var_word_ret \\ FULL_SIMP_TAC std_ss []);

val good_stack_tail_STEP = prove(
  ``good_stack_tail fs ((i,st,name)::t) ==>
    !k. good_stack_tail fs ((k,st,name)::t)``,
  Cases_on `t` \\ FULL_SIMP_TAC std_ss [good_stack_tail_def]
  \\ PairCases_on `h` \\ FULL_SIMP_TAC std_ss [good_stack_tail_def]);

val var_word_fold_IGNORE = prove(
  ``!t s st.
      ~(MEM x (MAP FST t)) ==>
      (var_word x
        (fold (\(var,val). var_upd var val) (MAP (\x. (FST x,SND x st)) t) s) =
       var_word x s)``,
  Induct \\ FULL_SIMP_TAC std_ss [MAP,fold_def,MEM,MAP]
  \\ FULL_SIMP_TAC std_ss [var_word_def,var_upd_def,var_acc_def,
       APPLY_UPDATE_THM]);

val save_vals_lemma = prove(
  ``(MAP FST l = ("ret"::all_names ++ ["ret_addr_input"])) ==>
    (var_word "ret" (save_vals ("ret"::all_names ++ ["ret_addr_input"])
      (MAP (\i. i st) (MAP SND l)) s) =
     var_word "ret" (apply_update l st))``,
  Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [MAP,save_vals_def,fold_def]
  \\ FULL_SIMP_TAC std_ss [var_upd_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [MAP_MAP_o,o_DEF,ZIP_MAP_MAP]
  \\ `~(MEM "ret" (MAP FST t))` by ALL_TAC
  THEN1 (POP_ASSUM (ASSUME_TAC o GSYM)
         \\ FULL_SIMP_TAC std_ss [all_names_def] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [var_word_fold_IGNORE] \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [apply_update_def,var_word_def,var_acc_def,
       APPLY_UPDATE_THM]);

val find_func_IMP_EVEN = prove(
  ``!fs s s entry l.
      EVERY (func_ok code jjj) fs /\
      (find_func s fs = SOME (Func s entry l)) ==>
      EVEN (w2n entry)``,
  Induct \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC std_ss [find_func_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `s' = s`
  \\ FULL_SIMP_TAC (srw_ss()) [funcs_ok_def,func_ok_def,fs_locs_def]
  \\ RES_TAC) |> SPEC_ALL |> Q.INST [`jjj`|->`fs_locs fs`]
  |> SIMP_RULE std_ss [GSYM funcs_ok_def];

val find_inst_IMP_LIST_SUBSET = prove(
  ``!l k1.
      i < dimword (:'a) /\ ALL_DISTINCT (MAP inst_loc l) /\ ODD k1 /\
      (find_inst (n2w i) l = SOME (Inst ((n2w i) :'a word) a next)) ==>
      ?k2. ODD k2 /\
        (LIST_SUBSET (SND (next_trans i k2 next)) (list_inst_trans k1 l))``,
  Induct \\ FULL_SIMP_TAC std_ss [find_inst_def] \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [find_inst_def,inst_loc_def,MAP,ALL_DISTINCT]
  \\ Cases_on `c = n2w i` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `k1`
    \\ FULL_SIMP_TAC (srw_ss()) [LIST_SUBSET_def,EVERY_MEM,list_inst_trans_def,
         inst_trans_def,w2n_n2w] \\ Cases_on `next_trans i k1 next`
    \\ FULL_SIMP_TAC std_ss [LET_DEF,MEM_APPEND])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LIST_SUBSET_def,EVERY_MEM,list_inst_trans_def,
         inst_trans_def,w2n_n2w]
  \\ Cases_on `next_trans (w2n (c:'a word)) k1 n`
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,LET_DEF]
  \\ `ODD q` by IMP_RES_TAC next_trans_IMP
  \\ METIS_TAC []) |> Q.SPECL [`l`,`1`] |> SIMP_RULE std_ss [];

val NOT_MEM_odd_nums = prove(
  ``!l k n. ODD k /\ EVEN n ==> ~(MEM n (odd_nums k l))``,
  Induct \\ FULL_SIMP_TAC std_ss [odd_nums_def,MEM]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ODD_EVEN]
  \\ FULL_SIMP_TAC std_ss [ODD_EVEN]
  \\ `~(EVEN (k+2))` by FULL_SIMP_TAC std_ss [EVEN_ADD]
  \\ RES_TAC);

val MEM_odd_nums = prove(
  ``!l k i. MEM k (odd_nums i l) ==> i <= k``,
  Induct \\ FULL_SIMP_TAC std_ss [odd_nums_def,MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

val ALL_DISTINCT_odd_nums = prove(
  ``!l k. ALL_DISTINCT (odd_nums k l)``,
  Induct \\ FULL_SIMP_TAC std_ss [odd_nums_def,ALL_DISTINCT]
  \\ POP_ASSUM (K ALL_TAC) \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC MEM_odd_nums \\ DECIDE_TAC);

val EVEN_ODD_MEM_list_inst_trans = prove(
  ``!l k.
      EVERY (\i. EVEN (inst_loc i)) l /\
      MEM e (MAP FST (list_inst_trans k l)) /\ ODD k ==>
      if EVEN e then MEM e (MAP inst_loc l) else k <= e``,
  Induct \\ FULL_SIMP_TAC std_ss [list_inst_trans_def,MAP,MEM]
  \\ REPEAT STRIP_TAC \\ Cases_on `inst_trans k h` \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,MEM,MAP_APPEND,inst_trans_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,inst_loc_def]
  \\ Q.MATCH_ASSUM_RENAME_TAC `next_trans (w2n c) k nn = (k1,xs)`
  \\ MP_TAC (next_trans_IMP |> Q.SPECL [`nn`,`w2n (c:'a word)`] |> SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM,MAP,inst_loc_def,TL]
  THEN1 (Q.PAT_ASSUM `xs = yyy` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [TL,HD,MAP,sortingTheory.PERM_CONS_IFF]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP]
    \\ Cases_on `y'` \\ FULL_SIMP_TAC std_ss []
    \\ `ODD q` by (RES_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ ASM_SIMP_TAC std_ss [EVEN_ODD]
    \\ IMP_RES_TAC sortingTheory.PERM_MEM_EQ
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ RES_TAC \\ IMP_RES_TAC MEM_odd_nums)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [ODD_ADD,ODD_EVEN,EVEN_DOUBLE]
  \\ RES_TAC \\ Cases_on `EVEN e` \\ FULL_SIMP_TAC std_ss []
  \\ DECIDE_TAC)

val EVEN_MEM_list_inst_trans = prove(
  ``EVERY (\i. EVEN (inst_loc i)) l /\
    MEM e (MAP FST (list_inst_trans k l)) /\ EVEN e /\ ODD k ==>
    MEM e (MAP inst_loc l)``,
  METIS_TAC [EVEN_ODD_MEM_list_inst_trans])

val ODD_MEM_list_inst_trans = prove(
  ``EVERY (\i. EVEN (inst_loc i)) l /\
    MEM e (MAP FST (list_inst_trans k l)) /\ ODD e /\ ODD k ==>
    k <= e``,
  METIS_TAC [EVEN_ODD_MEM_list_inst_trans,EVEN_ODD])

val ODD_MEM_odd_nums = prove(
  ``!l k i. MEM k (odd_nums i l) /\ ODD i ==> ODD k /\ k < i + 2 * l``,
  Induct \\ FULL_SIMP_TAC std_ss [odd_nums_def,MEM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [ODD_ADD]
  \\ RES_TAC \\ DECIDE_TAC);

val ALL_DISTINCT_list_inst_trans = prove(
  ``!l k. EVERY (\i. EVEN (inst_loc i)) l /\
          ODD k /\ ALL_DISTINCT (MAP inst_loc l) ==>
          ALL_DISTINCT (MAP FST (list_inst_trans k l))``,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [list_inst_trans_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `inst_trans k h`
  \\ FULL_SIMP_TAC std_ss [MAP_APPEND,ALL_DISTINCT_APPEND,MAP,ALL_DISTINCT]
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,inst_loc_def]
  \\ FULL_SIMP_TAC std_ss [inst_trans_def]
  \\ `ODD q` by IMP_RES_TAC next_trans_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC (next_trans_IMP |> Q.SPECL [`n`,`w2n (c:'a word)`,`k`,`q`,`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 (IMP_RES_TAC sortingTheory.ALL_DISTINCT_PERM
    \\ FULL_SIMP_TAC std_ss [TL,ALL_DISTINCT,ALL_DISTINCT_odd_nums]
    \\ MATCH_MP_TAC NOT_MEM_odd_nums
    \\ FULL_SIMP_TAC std_ss [EVEN_DOUBLE])
  \\ IMP_RES_TAC sortingTheory.PERM_MEM_EQ
  \\ FULL_SIMP_TAC std_ss [inst_loc_def,TL,MEM]
  \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ Q.PAT_ASSUM `~bbb` MP_TAC
  \\ SIMP_TAC std_ss [] THEN1
   (MATCH_MP_TAC (EVEN_MEM_list_inst_trans |> GEN_ALL)
    \\ Q.LIST_EXISTS_TAC [`(k + 2 * LENGTH ys)`]
    \\ FULL_SIMP_TAC std_ss [EVEN_DOUBLE])
  \\ IMP_RES_TAC ODD_MEM_odd_nums
  \\ IMP_RES_TAC ODD_MEM_list_inst_trans
  \\ `F` by DECIDE_TAC);

val find_func_IMP_MEM = prove(
  ``!xs x y. (find_func x xs = SOME y) ==> MEM y xs``,
  Induct \\ FULL_SIMP_TAC std_ss [find_func_def] \\ Cases
  \\ SRW_TAC [] [find_func_def] \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val find_inst_IMP_MEM = prove(
  ``!xs x y. (find_inst x xs = SOME y) ==> MEM y xs``,
  Induct \\ FULL_SIMP_TAC std_ss [find_inst_def] \\ Cases
  \\ SRW_TAC [] [find_inst_def] \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val graph_SOME_IMP = prove(
  ``!xs n y. (graph xs n = SOME y) ==> MEM (n,y) xs``,
  Induct \\ FULL_SIMP_TAC std_ss [graph_def,FORALL_PROD,
       APPLY_UPDATE_THM,MEM] \\ SRW_TAC [] []);

val graph_APPEND = prove(
  ``!xs ys x.
      graph (xs ++ ys) x =
        case graph xs x of
        | NONE => graph ys x
        | y => y``,
  Induct \\ FULL_SIMP_TAC std_ss [graph_def,APPEND,
    FORALL_PROD,APPLY_UPDATE_THM] \\ SRW_TAC [] []);

val list_inst_trans_IMP_LESS = prove(
  ``!l k n x.
      (graph (list_inst_trans k (l:'a inst list)) n = SOME x) /\
      EVEN n /\ ODD k ==>
      n < dimword (:'a)``,
  Induct \\ FULL_SIMP_TAC std_ss [graph_def,FORALL_PROD,
       APPLY_UPDATE_THM,MEM,list_inst_trans_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `inst_trans k h`
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [inst_trans_def]
  \\ `ODD q` by IMP_RES_TAC next_trans_IMP
  \\ FULL_SIMP_TAC std_ss [graph_APPEND]
  \\ Cases_on `graph r n` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC graph_SOME_IMP
  \\ IMP_RES_TAC next_trans_IMP
  \\ FULL_SIMP_TAC std_ss [MEM]
  \\ `w2n c < dimword(:'a)` by METIS_TAC [w2n_lt]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [EVERY_MEM,FORALL_PROD]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [EVEN_ODD]);

val good_stack_tail_return_vars = prove(
  ``good_stack_tail fs ((ret,st1,name1)::t) ==>
    good_stack_tail fs ((ret,return_vars all_names_with_input
                               all_names_ignore st st1,name1)::t)``,
  Cases_on `t` \\ FULL_SIMP_TAC std_ss [good_stack_tail_def]
  \\ PairCases_on `h` \\ FULL_SIMP_TAC std_ss [good_stack_tail_def]
  \\ `var_word "ret" (return_vars all_names_with_input all_names_ignore st st1) =
      var_word "ret" st1` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [var_word_def,var_acc_def,return_vars_def,
           save_vals_def,fold_def,var_upd_def,all_names_def] \\ EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [var_word_def,var_acc_def,return_vars_def,
           save_vals_def,fold_def,var_upd_def] \\ EVAL_TAC)

val func_ok_EXPEND_CODE = store_thm("func_ok_EXPEND_CODE",
  ``func_ok code locs f ==>
    !c. (case (code,c) of
         | ((c1,x1), (c2,x2)) => (c1 SUBSET c2 /\ (x1 = x2))) ==>
        func_ok c locs f``,
  Cases_on `f` \\ SIMP_TAC std_ss [func_ok_def,IMPL_INST_def]
  \\ PairCases_on `code` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ PairCases_on `c'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SPEC_SUBSET_CODE
  \\ every_case_tac \\ fs []
  \\ metis_tac [SPEC_SUBSET_CODE]);

val return_vars_SAME = prove(
  ``!n. MEM n all_names ==>
        (st n = return_vars all_names_with_input all_names_ignore st st1 n)``,
  FULL_SIMP_TAC std_ss [GSYM EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [all_names_def,EVERY_DEF,return_vars_def]
  \\ FULL_SIMP_TAC std_ss [var_word_def,var_acc_def,return_vars_def,
           save_vals_def,fold_def,var_upd_def] \\ EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [var_word_def,var_acc_def,return_vars_def,
           save_vals_def,fold_def,var_upd_def] \\ EVAL_TAC)

val MEM_CAll_next_trans = prove(
  ``!n1 d k q r. MEM (n,Call x1 x2 x3 x4) r /\ (next_trans d k n1 = (q,r)) ==>
                 (x4 = all_names_ignore)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [next_trans_def,MEM]
  \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `o'` \\ FULL_SIMP_TAC (srw_ss()) [next_trans_def])
  \\ Cases_on `next_trans k (k + 4) n1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `next_trans (k + 2) q' n1'` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [MEM,MEM_APPEND] \\ RES_TAC);

val MEM_Call_list_inst_trans = prove(
  ``!l k. MEM (n,Call x1 x2 x3 x4) (list_inst_trans k l) ==>
          (x4 = all_names_ignore)``,
  Induct \\ FULL_SIMP_TAC std_ss [list_inst_trans_def,MEM]
  \\ REPEAT STRIP_TAC \\ Cases_on `inst_trans k h`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,MEM_APPEND] \\ RES_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [inst_trans_def]
  \\ IMP_RES_TAC MEM_CAll_next_trans);

val arm_assert_for_def = Define `
  (arm_assert_for ([]:32 stack) = SEP_F) /\
  (arm_assert_for ((loc,state,name)::rest) =
     arm_STATE state * arm_PC (case loc of NextNode n => n2w n
                                         | _ => var_word "ret" state))`;

val arm8_assert_for_def = Define `
  (arm8_assert_for ([]:64 stack) = SEP_F) /\
  (arm8_assert_for ((loc,state,name)::rest) =
     arm8_STATE state * arm8_pc (case loc of NextNode n => n2w n
                                           | _ => var_word "ret" state))`;

val m0_assert_for_def = Define `
  (m0_assert_for ([]:32 stack) = SEP_F) /\
  (m0_assert_for ((loc,state,name)::rest) =
     m0_STATE state * m0_PC (case loc of NextNode n => n2w n
                                       | _ => var_word "ret" state))`;

fun exec_graph_step_IMP_exec_next arch = let
  val (assert_for_def,code,tm) =
    if arch = "arm" then
      (arm_assert_for_def,``ARM code``,
       ``arm_assert_for s4 = arm_STATE s7 * arm_PC w``) else
    if arch = "arm8" then
      (arm8_assert_for_def,``ARM8 code``,
       ``arm8_assert_for s4 = arm8_STATE s7 * arm8_pc w``) else
    if arch = "m0" then
      (m0_assert_for_def,``M0 code``,
       ``m0_assert_for s4 = m0_STATE s7 * m0_PC w``) else fail()
  in prove(
  ``!next i k n.
      NRC (exec_graph_step (list_func_trans fs)) n
        ((NextNode i,st,name)::t) s2 /\ n <> 0/\ funcs_ok ^code fs /\
      (list_func_trans fs name = SOME (GraphFunction x1 x2 (graph nodes) x3)) /\
      ODD k /\ LIST_SUBSET (SND (next_trans i k next)) nodes /\
      ALL_DISTINCT (MAP FST nodes) /\ next_ok next /\
      good_stack_tail fs ((NextNode i,st,name)::t) /\ good_stack fs s2 ==>
      ?s4 s7 j j1 call w.
         exec_next (fs_locs fs) next st s7 w call /\
         ^tm /\
         good_stack fs s4 /\
         NRC (exec_graph_step (list_func_trans fs)) j
           ((NextNode i,st,name)::t) s4 /\ j1 < n /\
         NRC (exec_graph_step (list_func_trans fs)) j1 s4 s2``,
  Induct \\ NTAC 4 STRIP_TAC
  THEN1 (* IF *)
   (Cases_on `n` \\ FULL_SIMP_TAC std_ss [NRC] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `exec_graph_step (list_func_trans fs)
         ((NextNode i,st,name)::t) z` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once exec_graph_step_def]
    \\ FULL_SIMP_TAC std_ss [next_trans_def]
    \\ Cases_on `next_trans k (k + 4) next` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.MATCH_ASSUM_RENAME_TAC `next_trans k (k + 4) next1 = (t1,xs)`
    \\ Cases_on `next_trans (k+2) t1 next'` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.MATCH_ASSUM_RENAME_TAC `next_trans (k+2) t1 next2 = (t2,ys)`
    \\ FULL_SIMP_TAC std_ss [LIST_SUBSET_def,EVERY_DEF,LET_DEF]
    \\ IMP_RES_TAC MEM_IMP_graph_SOME
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC (srw_ss()) [exec_node_def,exec_next_def,upd_stack_def]
    \\ Cases_on `f st` \\ FULL_SIMP_TAC std_ss [next_ok_def]
    THEN1 (SRW_TAC [] [] \\ Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC)
      \\ Q.PAT_X_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`k`,`k+4`,`n'`])
      \\ `n' <> 0` by ALL_TAC THEN1 (IMP_RES_TAC exec_graph_step_NOT_ZERO)
      \\ FULL_SIMP_TAC std_ss [ODD_ADD,EVERY_APPEND]
      \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC good_stack_tail_STEP \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`s4`,`s7`,`SUC j`,`j1`,`call`,`w`]
      \\ FULL_SIMP_TAC std_ss []
      \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
      \\ REWRITE_TAC [NRC]
      \\ FULL_SIMP_TAC (srw_ss()) [exec_graph_step_def,exec_node_def,upd_stack_def])
    THEN1 (SRW_TAC [] []
      \\ Q.PAT_X_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`k+2`,`t1`,`n'`])
      \\ `ODD (k+2) /\ ODD (k+4)` by FULL_SIMP_TAC std_ss [ODD_ADD]
      \\ `n' <> 0` by ALL_TAC THEN1 (IMP_RES_TAC exec_graph_step_NOT_ZERO)
      \\ `ODD t1` by METIS_TAC [next_trans_lemma]
      \\ FULL_SIMP_TAC std_ss [ODD_ADD,EVERY_APPEND]
      \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC good_stack_tail_STEP \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`s4`,`s7`,`SUC j`,`j1`,`call`,`w`]
      \\ FULL_SIMP_TAC std_ss []
      \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
      \\ REWRITE_TAC [NRC]
      \\ FULL_SIMP_TAC (srw_ss()) [exec_graph_step_def,exec_node_def,upd_stack_def]))
  THEN1 (* ASM *)
   (rename [‘ASM ooo’] \\ Cases_on ‘ooo’ THEN1
     (Cases_on `n` \\ FULL_SIMP_TAC std_ss [NRC] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `exec_graph_step (list_func_trans fs)
           ((NextNode i,st,name)::t) z` MP_TAC
      \\ ASM_SIMP_TAC (srw_ss()) [Once exec_graph_step_def]
      \\ FULL_SIMP_TAC std_ss [next_trans_def]
      \\ FULL_SIMP_TAC std_ss [LIST_SUBSET_def,EVERY_DEF]
      \\ IMP_RES_TAC MEM_IMP_graph_SOME
      \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC (srw_ss()) [exec_node_def]
      \\ FULL_SIMP_TAC std_ss [upd_stack_def]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [exec_next_def]
      \\ Q.LIST_EXISTS_TAC [`z`,`SUC 0`,`n'`]
      \\ FULL_SIMP_TAC std_ss [assert_for_def,upd_vars_thm,next_ok_def]
      \\ FULL_SIMP_TAC std_ss [get_assert_def]
      \\ Q.EXISTS_TAC `(case get_jump j of
            NextNode n => n2w n
          | Ret => var_word "ret" (apply_update l st)
          | Err => var_word "ret" (apply_update l st))`
      \\ FULL_SIMP_TAC std_ss []
      \\ REVERSE (REPEAT STRIP_TAC)
      THEN1 (REWRITE_TAC [NRC,DECIDE ``1 = SUC 0``]
        \\ FULL_SIMP_TAC (srw_ss()) [exec_graph_step_def,exec_node_def,upd_stack_def]
        \\ FULL_SIMP_TAC std_ss [upd_vars_thm])
      THEN1 (Cases_on `j`
        \\ FULL_SIMP_TAC (srw_ss()) [get_jump_def,good_stack_def,EVERY_DEF]
        \\ FULL_SIMP_TAC std_ss [EVEN_DOUBLE,jump_ok_def]
        \\ MATCH_MP_TAC good_stack_tail_UPDATE
        \\ IMP_RES_TAC good_stack_tail_STEP
        \\ FULL_SIMP_TAC std_ss [])
      \\ Cases_on `j`
      \\ FULL_SIMP_TAC (srw_ss()) [check_jump_def,get_jump_def])
    \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [NRC] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `exec_graph_step (list_func_trans fs)
         ((NextNode i,st,name)::t) z` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once exec_graph_step_def]
    \\ FULL_SIMP_TAC std_ss [next_trans_def]
    \\ FULL_SIMP_TAC std_ss [LIST_SUBSET_def,EVERY_DEF]
    \\ IMP_RES_TAC MEM_IMP_graph_SOME
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC (srw_ss()) [exec_node_def,get_assert_def]
    \\ FULL_SIMP_TAC std_ss [upd_stack_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [next_ok_def]
    \\ Cases_on `x st` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC NRC_Err
    \\ Q.MATCH_ASSUM_RENAME_TAC `SUC n1 <> 0`
    \\ `n1 <> 0` by ALL_TAC THEN1 (IMP_RES_TAC exec_graph_step_NOT_ZERO)
    \\ Cases_on `n1` \\ FULL_SIMP_TAC std_ss [NRC]
    \\ Q.PAT_X_ASSUM `exec_graph_step (list_func_trans fs)
         ((NextNode _,st,name)::t) _` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once exec_graph_step_def]
    \\ SIMP_TAC (srw_ss()) [exec_node_def,upd_stack_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [exec_next_def]
    \\ Q.LIST_EXISTS_TAC [`z'`,`SUC (SUC 0)`,`n`]
    \\ FULL_SIMP_TAC std_ss [assert_for_def,upd_vars_thm,next_ok_def,get_assert_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(case get_jump j of
          NextNode n => n2w n
        | Ret => var_word "ret" (apply_update l st)
        | Err => var_word "ret" (apply_update l st))`
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (REPEAT STRIP_TAC) THEN1 DECIDE_TAC
    THEN1 (REWRITE_TAC [NRC,DECIDE ``2 = SUC (SUC 0)``]
      \\ FULL_SIMP_TAC (srw_ss()) [exec_graph_step_def,exec_node_def,upd_stack_def]
      \\ FULL_SIMP_TAC std_ss [upd_vars_thm])
    THEN1 (Cases_on `j`
      \\ FULL_SIMP_TAC (srw_ss()) [get_jump_def,good_stack_def,EVERY_DEF]
      \\ FULL_SIMP_TAC std_ss [EVEN_DOUBLE,jump_ok_def]
      \\ MATCH_MP_TAC good_stack_tail_UPDATE
      \\ IMP_RES_TAC good_stack_tail_STEP
      \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `j`
    \\ FULL_SIMP_TAC (srw_ss()) [check_jump_def,get_jump_def])
  THEN (* CALL *) Cases_on `n` \\ FULL_SIMP_TAC std_ss [NRC] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `exec_graph_step (list_func_trans fs)
         ((NextNode i,st,name)::t) z` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once exec_graph_step_def]
    \\ FULL_SIMP_TAC std_ss [next_trans_def]
    \\ FULL_SIMP_TAC std_ss [LIST_SUBSET_def,EVERY_DEF]
    \\ IMP_RES_TAC MEM_IMP_graph_SOME
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC (srw_ss()) [exec_node_def]
    \\ REVERSE (Cases_on `get_assert o' st`)
    \\ FULL_SIMP_TAC std_ss [upd_stack_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC NRC_Err
    \\ Q.MATCH_ASSUM_RENAME_TAC `SUC n1 <> 0`
    \\ `n1 <> 0` by ALL_TAC THEN1 (IMP_RES_TAC exec_graph_step_NOT_ZERO)
    \\ Cases_on `n1` \\ FULL_SIMP_TAC std_ss [NRC]
    \\ Q.PAT_X_ASSUM `exec_graph_step (list_func_trans fs)
         ((NextNode _,st,name)::t) _` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once exec_graph_step_def]
    \\ SIMP_TAC (srw_ss()) [exec_node_def,upd_stack_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [exec_next_def]
    \\ Cases_on `list_func_trans fs s` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC NRC_Err
    \\ Q.ABBREV_TAC `n' = n` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [init_vars_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC
         `list_func_trans fs s = SOME (GraphFunction inp out f n)`
    \\ `inp = ret_and_all_names` by ALL_TAC
    THEN1 (IMP_RES_TAC list_func_trans_EQ_SOME_IMP)
    \\ `fs_locs fs s = SOME (n2w n)` by ALL_TAC
    THEN1 (IMP_RES_TAC list_func_trans_EQ_SOME_IMP)
    \\ FULL_SIMP_TAC std_ss [check_jump_def]
    \\ Q.LIST_EXISTS_TAC [`z'`,`SUC (SUC 0)`,`n'`]
    \\ REVERSE (REPEAT STRIP_TAC) \\ FULL_SIMP_TAC std_ss []
    THEN1 DECIDE_TAC
    THEN1 (REWRITE_TAC [NRC,DECIDE ``2 = SUC (SUC 0)``]
      \\ FULL_SIMP_TAC (srw_ss()) [exec_graph_step_def,exec_node_def,
           upd_stack_def] \\ FULL_SIMP_TAC std_ss [init_vars_def,MAP])
    THEN1
     (ASM_SIMP_TAC (srw_ss()) [next_ok_def,good_stack_def,HD,FST]
      \\ IMP_RES_TAC good_stack_tail_STEP
      \\ ASM_SIMP_TAC (srw_ss()) [good_stack_tail_def]
      \\ `EVEN n` by ALL_TAC THEN1
        (IMP_RES_TAC list_func_trans_EQ_SOME_IMP
         \\ FULL_SIMP_TAC std_ss [EVEN_DOUBLE,jump_ok_def]
         \\ IMP_RES_TAC find_func_IMP_EVEN)
      \\ FULL_SIMP_TAC std_ss [next_ok_def]
      \\ Cases_on `j`
      \\ FULL_SIMP_TAC (srw_ss()) [get_jump_def,check_ret_def,EVEN_DOUBLE]
      \\ FULL_SIMP_TAC std_ss [RW1[MULT_COMM]MULT_DIV,n2w_w2n]
      \\ FULL_SIMP_TAC std_ss [ret_and_all_names_def]
      \\ FULL_SIMP_TAC std_ss [save_vals_lemma,jump_ok_def])
    THEN1 (FULL_SIMP_TAC (srw_ss()) [assert_for_def]
      \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ TRY (MATCH_MP_TAC arm_STATE_all_names)
      \\ TRY (MATCH_MP_TAC arm8_STATE_all_names)
      \\ TRY (MATCH_MP_TAC m0_STATE_all_names)
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MAP_MAP_o,o_DEF]
      \\ FULL_SIMP_TAC std_ss [next_ok_def]
      \\ Q.PAT_X_ASSUM `MAP FST l = ret_and_all_names` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [save_vals_def,ZIP_MAP_MAP,fold_MAP]
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MAP_MAP_o,o_DEF]
      \\ POP_ASSUM (ASSUME_TAC o GSYM)
      \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC fold_EQ_apply_update
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [ret_and_all_names_def]
      \\ FULL_SIMP_TAC std_ss [MEM,all_names_def] \\ EVAL_TAC)
    \\ FULL_SIMP_TAC std_ss [next_ok_def]) end;

fun exec_inst_progress arch = let
  val lemma = exec_graph_step_IMP_exec_next arch
  val (assert_for_def,code,tm) =
    if arch = "arm" then
      (arm_assert_for_def,``ARM code``,
       ``SPEC ARM_MODEL (arm_assert_for ((NextNode i,st,name)::t)) code
                        (arm_assert_for s4)``) else
    if arch = "arm8" then
      (arm8_assert_for_def,``ARM8 code``,
       ``SPEC ARM8_MODEL (arm8_assert_for ((NextNode i,st,name)::t)) code
                         (arm8_assert_for s4)``) else
    if arch = "m0" then
      (m0_assert_for_def,``M0 code``,
       ``SPEC M0_MODEL (m0_assert_for ((NextNode i,st,name)::t)) code
                       (m0_assert_for s4)``) else fail()
  in prove(
  ``NRC (exec_graph_step (list_func_trans fs)) n
      ((NextNode i,st,name)::t) s2 /\ funcs_ok ^code fs /\
    (find_func name fs = SOME (Func name entry l)) /\
    (find_inst (n2w i) l = SOME (Inst (n2w i) a next)) /\
    (list_func_trans fs name =
      SOME (GraphFunction x1 x2 (graph nodes) x3)) /\ ODD k /\
    LIST_SUBSET (SND (next_trans i k next)) nodes /\
    ALL_DISTINCT (MAP FST nodes) /\
    IMPL_INST ^code (fs_locs fs) (Inst (n2w i) (K T) next) /\
    n <> 0 /\ good_stack fs ((NextNode i,st,name)::t) /\ good_stack fs s2 ==>
    ?s4 j j1.
      NRC (exec_graph_step (list_func_trans fs)) j
      ((NextNode i,st,name)::t) s4 /\
      NRC (exec_graph_step (list_func_trans fs)) j1 s4 s2 /\ j1 < n /\
      good_stack fs s4 /\ ^tm``,
  SIMP_TAC (srw_ss()) [IMPL_INST_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [assert_for_def]
  \\ FULL_SIMP_TAC std_ss [RW1[MULT_COMM]MULT_DIV]
  \\ MP_TAC (lemma |> SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [good_stack_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ fs [ARM_def,ARM8_def,M0_def,RISCV_def]
  \\ Q.LIST_EXISTS_TAC [`s4`,`j`,`j1`] \\ FULL_SIMP_TAC std_ss []) end;

fun exec_func_step_IMP arch = let
  val lemma = exec_inst_progress arch
  val (assert_for_def,code,assert_for_tm,model_tm) =
    if arch = "arm" then
      (arm_assert_for_def,``ARM code``,``arm_assert_for``,``ARM_MODEL``) else
    if arch = "arm8" then
      (arm8_assert_for_def,``ARM8 code``,``arm8_assert_for``,``ARM8_MODEL``) else
    if arch = "m0" then
      (m0_assert_for_def,``M0 code``,``m0_assert_for``,``M0_MODEL``) else
    fail()
  in prove(
  ``funcs_ok ^code fs ==>
    !n s1 s2.
      good_stack fs s1 /\ good_stack fs s2 /\
      exec_graph_n (list_func_trans fs) n s1 s2 ==>
      SPEC ^model_tm (^assert_for_tm s1) code (^assert_for_tm s2)``,
  STRIP_TAC
  \\ completeInduct_on `n` \\ Cases_on `n = 0`
  \\ FULL_SIMP_TAC std_ss [exec_graph_n_def,NRC,SPEC_REFL]
  \\ REPEAT STRIP_TAC
  \\ `?s3. NRC (exec_graph_step (list_func_trans fs)) (n-1) s3 s2 /\
           exec_graph_step (list_func_trans fs) s1 s3` by
  (Cases_on `n` \\ FULL_SIMP_TAC std_ss [exec_graph_n_def,NRC] \\ METIS_TAC [])
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [exec_graph_step_def]
  \\ Cases_on `s1` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `?l st name. h = (l,st,name)` by METIS_TAC [PAIR]
  \\ REVERSE (Cases_on `l`) \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [good_stack_def,EVERY_DEF])
  THEN1
   (Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `?l1 st1 name1. h' = (l1,st1,name1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC (srw_ss()) [upd_stack_def]
    \\ REVERSE (Cases_on `l1`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    THEN1 IMP_RES_TAC NRC_Err THEN1 IMP_RES_TAC NRC_Err
    \\ Cases_on `list_func_trans fs name1` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.MATCH_ASSUM_RENAME_TAC `list_func_trans fs name1 =
         SOME (GraphFunction x1 x2 graph1 x3)`
    \\ Cases_on `graph1 n'` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [upd_stack_def]
      \\ IMP_RES_TAC NRC_Err)
    \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [exec_node_return_def]
    \\ Cases_on `list_func_trans fs s` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [exec_node_return_def]
    \\ FULL_SIMP_TAC std_ss [upd_stack_def]
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM UNION_IDEMPOT]))
    \\ MATCH_MP_TAC SPEC_COMPOSE
    \\ Q.EXISTS_TAC `^assert_for_tm s3`
    \\ `(^assert_for_tm ((Ret,st,name)::(NextNode n',st1,name1)::t') =
         ^assert_for_tm s3) /\ good_stack fs s3` by ALL_TAC THEN1
     (Q.MATCH_ASSUM_RENAME_TAC `list_func_trans fs name2 =
         SOME (GraphFunction y1 y2 graph2 y3)`
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `good_stack fs (xx::yy::tt)` MP_TAC
      \\ SIMP_TAC (srw_ss()) [good_stack_def,good_stack_tail_def,HD,FST]
      \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Q.PAT_ASSUM `g = graph1` ASSUME_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ NTAC 6 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss []
      \\ REPEAT (POP_ASSUM (fn th => if is_eq (concl th) then ALL_TAC else NO_TAC))
      \\ NTAC 6 STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `graph1 n1 = SOME (Call ret name2 l l0)`
      \\ `(y2 = all_names_with_input) /\ (l0 = all_names_ignore)` by ALL_TAC THEN1
       (IMP_RES_TAC list_func_trans_EQ_SOME_IMP
        \\ FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC graph_SOME_IMP
        \\ IMP_RES_TAC MEM_Call_list_inst_trans)
      \\ FULL_SIMP_TAC std_ss []
      \\ REVERSE (REPEAT STRIP_TAC)
      THEN1 (Cases_on `ret` \\ FULL_SIMP_TAC (srw_ss()) [])
      THEN1 (MATCH_MP_TAC good_stack_tail_return_vars
        \\ IMP_RES_TAC good_stack_tail_STEP \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [assert_for_def]
      \\ MATCH_MP_TAC (METIS_PROVE [] ``(f1 = f2) /\ (x1 = x2) ==> (f1 x1 = f2 x2)``)
      \\ STRIP_TAC THEN1
       (AP_TERM_TAC
        \\ TRY (MATCH_MP_TAC arm_STATE_all_names)
        \\ TRY (MATCH_MP_TAC arm8_STATE_all_names)
        \\ TRY (MATCH_MP_TAC m0_STATE_all_names)
        \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
        \\ METIS_TAC [return_vars_SAME])
      \\ Cases_on `ret` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ AP_TERM_TAC
      \\ FULL_SIMP_TAC std_ss [var_word_def,var_acc_def,return_vars_def,
           save_vals_def,fold_def,var_upd_def,all_names_def] \\ EVAL_TAC
      \\ FULL_SIMP_TAC std_ss [var_word_def,var_acc_def,return_vars_def,
           save_vals_def,fold_def,var_upd_def] \\ EVAL_TAC)
    \\ FULL_SIMP_TAC std_ss [SPEC_REFL,PULL_FORALL,AND_IMP_INTRO]
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ Q.EXISTS_TAC `n-1` \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ DECIDE_TAC)
  \\ Cases_on `list_func_trans fs name` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.MATCH_ASSUM_RENAME_TAC `list_func_trans fs name =
         SOME (GraphFunction x1 x2 graph1 x3)`
  \\ Cases_on `graph1 n'` \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [upd_stack_def]
    \\ IMP_RES_TAC NRC_Err)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC list_func_trans_EQ_SOME_IMP
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ `EVEN n'` by ALL_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [good_stack_def])
  \\ `ODD 1n` by EVAL_TAC
  \\ drule_all list_inst_trans_IMP_LESS
  \\ strip_tac
  \\ drule_all graph_list_inst_trans_EQ_SOME_IMP
  \\ strip_tac
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `graph (list_inst_trans 1 l) i = SOME x`
  \\ Q.MATCH_ASSUM_RENAME_TAC `find_inst (n2w i) l = SOME (Inst (n2w i) a next)`
  \\ FULL_SIMP_TAC std_ss [funcs_ok_def,EVERY_MEM]
  \\ IMP_RES_TAC find_func_IMP_MEM
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [func_ok_def]
  \\ IMP_RES_TAC find_inst_IMP_MEM
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ drule_all find_inst_IMP_LIST_SUBSET \\ strip_tac
  \\ MP_TAC (lemma
             |> Q.INST [`x1`|->`ret_and_all_names`,
                        `x2`|->`all_names_with_input`,
                        `k`|->`k2`,
                        `x3`|->`w2n entry`,
                        `nodes`|->`list_inst_trans 1 l`])
  \\ FULL_SIMP_TAC (srw_ss()) [funcs_ok_def,EVERY_MEM]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (MATCH_MP_TAC ALL_DISTINCT_list_inst_trans
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,IMPL_INST_def,func_ok_def]
    \\ Cases \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [inst_loc_def])
  \\ REPEAT STRIP_TAC
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM UNION_IDEMPOT]))
  \\ MATCH_MP_TAC SPEC_COMPOSE
  \\ Q.EXISTS_TAC `(^assert_for_tm s4)` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SPEC_REFL,PULL_FORALL,AND_IMP_INTRO]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ Q.EXISTS_TAC `j1` \\ FULL_SIMP_TAC std_ss []) end

Theorem arm_exec_func_step_IMP  = exec_func_step_IMP "arm";
Theorem arm8_exec_func_step_IMP = exec_func_step_IMP "arm8";
Theorem m0_exec_func_step_IMP   = exec_func_step_IMP "m0";

(* misc lemmas *)

val LIST_IMPL_INST_def = Define `
  (LIST_IMPL_INST code names [] = T) /\
  (LIST_IMPL_INST code names ((Inst i assert next)::xs) =
     IMPL_INST code names (Inst i assert next) /\ (assert = K T) /\
     LIST_IMPL_INST code names xs)`;

val IMP_LIST_IMPL_INST = store_thm("IMP_LIST_IMPL_INST",
  ``IMPL_INST code names (Inst i (K T) next) /\
    LIST_IMPL_INST code names xs ==>
    LIST_IMPL_INST code names ((Inst i (K T) next)::xs)``,
  SIMP_TAC std_ss [LIST_IMPL_INST_def]);

val IMP_func_ok = store_thm("IMP_func_ok",
  ``!insts. LIST_IMPL_INST code names insts ==>
            ALL_DISTINCT (MAP inst_loc insts) /\ EVEN (w2n entry) ==>
            func_ok code names (Func name entry insts)``,
  SIMP_TAC std_ss [func_ok_def] \\ Induct
  \\ FULL_SIMP_TAC std_ss [LIST_IMPL_INST_def,MAP,ALL_DISTINCT,MEM] \\ Cases
  \\ FULL_SIMP_TAC std_ss [LIST_IMPL_INST_def,MAP,ALL_DISTINCT,MEM,inst_loc_def]
  \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) []);

val IMP_EVERY_func_ok = store_thm("IMP_EVERY_func_ok",
  ``func_ok code locs f /\
    EVERY (func_ok code locs) fs ==>
    EVERY (func_ok code locs) (f::fs)``,
  FULL_SIMP_TAC std_ss [EVERY_DEF]);

val _ = wordsLib.guess_lengths ()

val word32_def = Define `
  (word32 (b1:word8) (b2:word8) (b3:word8) (b4:word8)) :word32 =
    b1 @@ b2 @@ b3 @@ b4`;

val word64_def = Define `
  (word64 (b1:word8) (b2:word8) (b3:word8) (b4:word8)
          (b5:word8) (b6:word8) (b7:word8) (b8:word8)) :word64 =
    b1 @@ b2 @@ b3 @@ b4 @@ b5 @@ b6 @@ b7 @@ b8`;

val READ32_def = zDefine `
  READ32 a mem = word32 (mem (a + 3w)) (mem (a + 2w)) (mem (a + 1w)) (mem a)`;

val READ64_def = zDefine `
  READ64 a mem =
    word64 (mem (a + 7w)) (mem (a + 6w)) (mem (a + 5w)) (mem (a + 4w))
           (mem (a + 3w)) (mem (a + 2w)) (mem (a + 1w)) (mem a)`;

val READ8_def = zDefine `
  READ8 a mem = (mem:'a word -> word8) a`;

val WRITE32_def = zDefine `
  WRITE32 (a:word32) (w:word32) (mem:word32->word8) =
                    (a =+ w2w w)
                   ((a + 1w =+ w2w (w >>> 8))
                   ((a + 2w =+ w2w (w >>> 16))
                   ((a + 3w =+ w2w (w >>> 24)) mem)))`;

val WRITE64_def = zDefine `
  WRITE64 (a:word64) (w:word64) (mem:word64->word8) =
                    (a =+ w2w w)
                   ((a + 1w =+ w2w (w >>> 8))
                   ((a + 2w =+ w2w (w >>> 16))
                   ((a + 3w =+ w2w (w >>> 24))
                   ((a + 4w =+ w2w (w >>> 32))
                   ((a + 5w =+ w2w (w >>> 40))
                   ((a + 6w =+ w2w (w >>> 48))
                   ((a + 7w =+ w2w (w >>> 56)) mem)))))))`;

val WRITE8_def = zDefine `
  WRITE8 (a:'a word) (w:word8) (mem:'a word->word8) = (a =+ w) mem`;

val READ32_expand64 = store_thm("READ32_expand64",
  ``READ32 (a:word64) m =
    w2w (READ8 a m) ||
    (w2w (READ8 (a+1w) m) << 8) ||
    (w2w (READ8 (a+2w) m) << 16) ||
    (w2w (READ8 (a+3w) m) << 24)``,
  fs [READ32_def,READ8_def,word32_def] \\ blastLib.BBLAST_TAC);

val func_name_def = Define `
  func_name (Func name entry l) = name`;

val func_body_trans_def = zDefine `
  func_body_trans f = SND (func_trans f)`;

val list_func_trans_thm = store_thm("list_func_trans_thm",
  ``list_func_trans fs =
      graph (MAP (\f. (func_name f, func_body_trans f)) fs)``,
  SIMP_TAC std_ss [list_func_trans_def] \\ AP_TERM_TAC
  \\ Induct_on `fs` \\ FULL_SIMP_TAC std_ss [MAP] \\ Cases
  \\ FULL_SIMP_TAC std_ss [func_name_def,func_trans_def,func_body_trans_def]);

val word_extract_thm = store_thm("word_extract_thm",
  ``((7 >< 0) (w:word32) = (w2w w):word8) /\
    ((15 >< 8) (w:word32) = (w2w (w >>> 8)):word8) /\
    ((23 >< 16) (w:word32) = (w2w (w >>> 16)):word8) /\
    ((31 >< 24) (w:word32) = (w2w (w >>> 24)):word8) /\
    ((31 >< 0) (v:word64) = ((w2w v):word32)) /\
    ((63 >< 32) (v:word64) = ((w2w (v >>> 32)):word32))``,
  blastLib.BBLAST_TAC);

val n2w_lsr =
  ``n2w (w2n ((w:'a word) >>> m)):'a word``
  |> SIMP_CONV std_ss [w2n_lsr] |> RW [n2w_w2n]

val Align_lemma = prove(
  ``!w. (arm$Align (w,2) = w >>> 1 << 1) /\
        (m0$Align (w,2) = w >>> 1 << 1) /\
        (arm$Align (w,4) = w >>> 2 << 2) /\
        (m0$Align (w,4) = w >>> 2 << 2)``,
  Cases \\ SIMP_TAC std_ss [n2w_lsr,armTheory.Align_def,
    m0Theory.Align_def,w2n_n2w,WORD_MUL_LSL,word_mul_n2w]);

val REMOVE_Align = store_thm("REMOVE_Align",
  ``!w. ALIGNED w ==>
        (arm$Align (w,2) = w) /\ (arm$Align (w,4) = w) /\
        (m0$Align (w,2) = w) /\ (m0$Align (w,4) = w)``,
  SIMP_TAC std_ss [Align_lemma,ALIGNED_def] \\ blastLib.BBLAST_TAC);

val byte_lemma = prove(
  ``(((b1:word8) @@ (b2:word8)):word16 = w2w b1 << 8 || w2w b2) /\
    (((h1:word16) @@ (b2:word8)):24 word = w2w h1 << 8 || w2w b2) /\
    (((b1:word8) @@ (h2:word16)):24 word = w2w b1 << 16 || w2w h2) /\
    (((h1:word16) @@ (h2:word16)):word32 = w2w h1 << 16 || w2w h2)``,
  blastLib.BBLAST_TAC);

val lemma = blastLib.BBLAST_PROVE
  ``(w && 1w = 0w) <=> ~(w:word32) ' 0``

val Aligned2_thm = prove(
  ``(arm$Aligned (w:word32,2) = (w && 1w = 0w)) /\
    (m0$Aligned (w:word32,2) = (w && 1w = 0w))``,
  FULL_SIMP_TAC std_ss [lemma]
  \\ SIMP_TAC std_ss [armTheory.Aligned_def,m0Theory.Aligned_def,
       armTheory.Align_def,m0Theory.Align_def,ALIGNED_INTRO]
  \\ Cases_on `w` \\ FULL_SIMP_TAC (srw_ss()) [ALIGNED_n2w]
  \\ FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_index,
       bitTheory.BIT_def, bitTheory.BITS_THM]
  \\ `(2 * (n DIV 2)) < 4294967296` by ALL_TAC THEN1
   (SIMP_TAC bool_ss [GSYM (EVAL ``2 * 2147483648:num``),LT_MULT_LCANCEL]
    \\ FULL_SIMP_TAC std_ss [DIV_LT_X])
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (DIVISION |> Q.SPEC `2` |> SIMP_RULE std_ss []
                          |> GSYM |> Q.SPEC `n`)
  \\ Cases_on `n MOD 2 = 0` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]
  \\ `n MOD 2 < 2` by FULL_SIMP_TAC std_ss []
  \\ DECIDE_TAC);

val Aligned_thm = prove(
  ``(arm$Aligned (w:word32,4) = (w && 3w = 0w)) /\
    (m0$Aligned (w:word32,4) = (w && 3w = 0w))``,
  SIMP_TAC std_ss [armTheory.Aligned_def,m0Theory.Aligned_def,
     armTheory.Align_def,m0Theory.Align_def,ALIGNED_INTRO]
  \\ Cases_on `w` \\ FULL_SIMP_TAC (srw_ss()) [ALIGNED_n2w]
  \\ `(4 * (n DIV 4)) < 4294967296` by ALL_TAC THEN1
   (SIMP_TAC bool_ss [GSYM (EVAL ``4 * 1073741824:num``),LT_MULT_LCANCEL]
    \\ FULL_SIMP_TAC std_ss [DIV_LT_X])
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (DIVISION |> Q.SPEC `4` |> SIMP_RULE std_ss [] |> GSYM |> Q.SPEC `n`)
  \\ Cases_on `n MOD 4 = 0` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC] \\ DECIDE_TAC);

val w2n_eq = prove(
  ``!w. (w2n w = 0) <=> (w = 0w)``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) []);

val decomp_simp1 = prove(
  ``(K x y = x) /\ (SUC n = n + 1)``,
  SIMP_TAC std_ss [FUN_EQ_THM,ADD1]);

val decomp_simp1 = save_thm("decomp_simp1",
  LIST_CONJ [GSYM word32_def,Aligned_thm,Aligned2_thm,ALIGNED,
        decomp_simp1,word_extract_thm,word_bits_mask,word_extract_w2w_mask,
        ALIGNED_INTRO,w2n_eq,byte_lemma])

val decomp_simp2 = store_thm("decomp_simp2",
  ``(K x = \y. x) /\ (SUC = \n. n + 1)``,
  SIMP_TAC std_ss [FUN_EQ_THM,ADD1]);

val decomp_simp3 = store_thm("decomp_simp3",
  ``(K = \x y. x) /\ (ALIGNED x = (x && 3w = 0w)) /\
    (REV xs [] = REVERSE xs)``,
  SIMP_TAC std_ss [FUN_EQ_THM,ALIGNED_def] \\ EVAL_TAC);

val CALL_TAG_def = Define `
  CALL_TAG (s:string) (is_tail_call:bool) = T`;

val unspecified_pre_def = zDefine `unspecified_pre = F`;

val SKIP_TAG_def = zDefine `
  SKIP_TAG (s:string) = unspecified_pre`;

val SKIP_SPEC_ARM = store_thm("SKIP_SPEC_ARM",
  ``!asm n.
      SPEC ARM_MODEL (arm_PC p * cond (SKIP_TAG asm)) {} (arm_PC (p + n2w n))``,
  SIMP_TAC std_ss [SKIP_TAG_def,SPEC_MOVE_COND,unspecified_pre_def]);

val SKIP_SPEC_ARM8 = store_thm("SKIP_SPEC_ARM8",
  ``!asm n.
      SPEC ARM8_MODEL (arm8_pc p * cond (SKIP_TAG asm)) {} (arm8_pc (p + n2w n))``,
  SIMP_TAC std_ss [SKIP_TAG_def,SPEC_MOVE_COND,unspecified_pre_def]);

val SKIP_SPEC_M0 = store_thm("SKIP_SPEC_M0",
  ``!asm n.
      SPEC ARM_MODEL (arm_PC p * cond (SKIP_TAG asm)) {} (arm_PC (p + n2w n))``,
  SIMP_TAC std_ss [SKIP_TAG_def,SPEC_MOVE_COND,unspecified_pre_def]);

val SKIP_SPEC_RISCV = store_thm("SKIP_SPEC_RISCV",
  ``!asm n.
      SPEC RISCV_MODEL (riscv_PC p * cond (SKIP_TAG asm)) {} (riscv_PC (p + n2w n))``,
  SIMP_TAC std_ss [SKIP_TAG_def,SPEC_MOVE_COND,unspecified_pre_def]);

val fake_spec = store_thm("fake_spec",
  ``SPEC ARM_MODEL (aPC p * aR 0w r0 * cond (unspecified_pre)) {}
                   (aR 0w ARB * aPC (p + 4w))``,
  SIMP_TAC std_ss [unspecified_pre_def,SPEC_MOVE_COND]);

val WORD_LEMMA = prove(
  ``(a - l = w) = (l = a - w:word32)``,
  blastLib.BBLAST_TAC);

val SP_LEMMA = store_thm("SP_LEMMA",
  ``((a - n2w (l + n) * 4w = r13 - 4w * n2w l) ==> b) ==>
    ALIGNED a /\ ALIGNED r13 /\ (n = w2n (a - r13:word32) DIV 4) ==> b``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [Once ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_RIGHT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS]
  \\ FULL_SIMP_TAC std_ss [AC WORD_MULT_ASSOC WORD_MULT_COMM]
  \\ FULL_SIMP_TAC std_ss [WORD_LCANCEL_SUB]
  \\ FULL_SIMP_TAC std_ss [WORD_LEMMA]
  \\ `ALIGNED (a - r13)` by METIS_TAC [ALIGNED_SUB]
  \\ Cases_on `a - r13`
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,ALIGNED_n2w,word_mul_n2w]
  \\ MP_TAC (MATCH_MP DIVISION (DECIDE ``0<4:num``) |> Q.SPEC `n'`)
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []);

val ALIGNED_IMP_BITS_01 = store_thm("ALIGNED_IMP_BITS_01",
  ``ALIGNED w ==> ~(w ' 0) /\ ~(w ' 1)``,
  SIMP_TAC std_ss [ALIGNED_def] \\ blastLib.BBLAST_TAC);

val BITS_01_IMP_ALIGNED = store_thm("BITS_01_IMP_ALIGNED",
  ``~(w ' 0) /\ ~(w ' 1) ==> ((b ==> ALIGNED w) <=> ALIGNED w)``,
  SIMP_TAC std_ss [ALIGNED_def] \\ blastLib.BBLAST_TAC);

val ALIGNED_Align = store_thm("ALIGNED_Align",
  ``(ALIGNED (arm$Align (w,2)) = ~(w ' 1)) /\
    (ALIGNED (arm$Align (w,4)) = T) /\
    (ALIGNED (m0$Align (w,2)) = ~(w ' 1)) /\
    (ALIGNED (m0$Align (w,4)) = T)``,
  SIMP_TAC std_ss [Align_lemma,ALIGNED_def] \\ blastLib.BBLAST_TAC);

val carry_out_def = zDefine `
  carry_out w1 w2 c = CARRY_OUT w1 w2 c`;

val OVERFLOW_EQ = store_thm("OVERFLOW_EQ",
  ``OVERFLOW x y c =
      (word_msb x = word_msb y) /\
      (word_msb x <> word_msb (if c then x - ~y else x + y))``,
  SIMP_TAC std_ss [add_with_carry_def,LET_DEF]
  \\ Cases_on `x` \\ Cases_on `y` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [word_sub_def,WORD_NEG,WORD_NOT_NOT]
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC,word_add_n2w]);

val BIT_31 = prove(
  ``BIT 31 m = ((m DIV 2**31) MOD 2 = 1)``,
  SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]);

val word32_msb_n2w = store_thm("word32_msb_n2w",
  ``word_msb ((n2w n):word32) = ((n DIV 2**31) MOD 2 = 1)``,
  SIMP_TAC (srw_ss()) [word_msb_n2w,BIT_31]);

val count_leading_zero_bits_def = zDefine `
  count_leading_zero_bits (w:'a word) =
    (n2w (arm$CountLeadingZeroBits w)):'a word`;

val count_leading_zero_bits_thm =
  store_thm("count_leading_zero_bits_thm",
  ``(n2w (arm$CountLeadingZeroBits w) = count_leading_zero_bits w) /\
    (n2w (m0$CountLeadingZeroBits w) = count_leading_zero_bits w)``,
  FULL_SIMP_TAC std_ss [m0Theory.CountLeadingZeroBits_def,
    armTheory.CountLeadingZeroBits_def,count_leading_zero_bits_def,
    armTheory.HighestSetBit_def,m0Theory.HighestSetBit_def]);

val word_add_with_carry_def = zDefine `
  word_add_with_carry (w1:'a word) w2 c =
    FST (add_with_carry (w1,w2,c))`;

(* graph format helpers *)

val MemAcc8_def = Define `
  MemAcc8 m a = READ8 a m`;

val MemAcc32_def = Define `
  MemAcc32 m a = READ32 a (m:word32->word8)`;

val MemAcc64_def = Define `
  MemAcc64 m a = READ64 a (m:word64->word8)`;

val MemUpdate8_def = Define `
  MemUpdate8 m a w = WRITE8 a w m`;

val MemUpdate32_def = Define `
  MemUpdate32 m a w = WRITE32 a w (m:word32->word8)`;

val MemUpdate64_def = Define `
  MemUpdate64 m a w = WRITE64 a w (m:word64->word8)`;

val ShiftLeft_def = Define `
  ShiftLeft (w:'a word) (y:'a word) = word_lsl w (w2n y)`;

val ShiftRight_def = Define `
  ShiftRight (w:'a word) (y:'a word) = word_lsr w (w2n y)`;

val SignedShiftRight_def = Define `
  SignedShiftRight (w:'a word) (y:'a word) = word_asr w (w2n y)`;

val w2w_carry_alt = prove(
  ``((w2w:word32 -> 33 word) (w1:word32) << w2n ((w2w (w2:word32)):word8)) ' 32 <=>
    (ShiftLeft ((w2w:word32 -> word64) (w1:word32))
       (w2w ((w2w:word32->word8) w2))) ' 32``,
  FULL_SIMP_TAC (srw_ss()) [ShiftLeft_def]
  \\ `w2n ((w2w:word8->word64) (w2w w2)) = w2n ((w2w w2):word8)` by
   (FULL_SIMP_TAC (srw_ss()) [w2w_def]
    \\ MATCH_MP_TAC LESS_TRANS \\ Q.EXISTS_TAC `256`
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (srw_ss()) [word_lsl_def,fcpTheory.FCP_BETA]
  \\ Q.ABBREV_TAC `n = w2n ((w2w:word32->word8) w2)`
  \\ Cases_on `n <= 32` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `32 - n < dimindex (:33) /\ 32 - n < dimindex (:64)` by
    (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [wordsTheory.w2w]);

val w2w_carry = prove(
  ``EVERY (\i. (((w2w (w:word32) << i):33 word) ' 32) <=>
               ((w && n2w (2 ** (32 - i))) <> 0w)) (GENLIST I 32)``,
  FULL_SIMP_TAC (srw_ss()) [EVAL ``GENLIST I 32``,EVERY_DEF,
    ShiftLeft_def,ShiftRight_def,w2n_n2w] \\ blastLib.BBLAST_TAC) |> SIMP_RULE std_ss [EVAL ``GENLIST I 32``,EVERY_DEF];

val rw16 = prove(
  ``EVERY (\i. ((w:word16) ' i = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_bit i w = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_lsr w i = ShiftRight w ((n2w i):word16)) /\
               (word_asr w i = SignedShiftRight w ((n2w i):word16)) /\
               (word_lsl w i = ShiftLeft w ((n2w i):word16))) (GENLIST I 16) /\
    (word_msb w = (w:word16) ' 15)``,
  FULL_SIMP_TAC (srw_ss()) [EVAL ``GENLIST I 16``,EVERY_DEF,
    ShiftLeft_def,ShiftRight_def,SignedShiftRight_def,w2n_n2w] \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [EVAL ``GENLIST I 16``,EVERY_DEF]

val rw64 = prove(
  ``EVERY (\i. ((w:word64) ' i = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_bit i w = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_lsr w i = ShiftRight w ((n2w i):word64)) /\
               (word_asr w i = SignedShiftRight w ((n2w i):word64)) /\
               (word_lsl w i = ShiftLeft w ((n2w i):word64))) (GENLIST I 64) /\
    (word_msb w = (w:word64) ' 63)``,
  FULL_SIMP_TAC (srw_ss()) [EVAL ``GENLIST I 64``,EVERY_DEF,
    ShiftLeft_def,ShiftRight_def,SignedShiftRight_def,w2n_n2w] \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [EVAL ``GENLIST I 64``,EVERY_DEF]

val rw8 = prove(
  ``EVERY (\i. ((w:word8) ' i = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_bit i w = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_lsr w i = ShiftRight w ((n2w i):word8)) /\
               (word_asr w i = SignedShiftRight w ((n2w i):word8)) /\
               (word_lsl w i = ShiftLeft w ((n2w i):word8))) (GENLIST I 8) /\
    (word_msb w = (w:word8) ' 7)``,
  FULL_SIMP_TAC (srw_ss()) [EVAL ``GENLIST I 8``,EVERY_DEF,
    ShiftLeft_def,ShiftRight_def,SignedShiftRight_def,w2n_n2w] \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [EVAL ``GENLIST I 8``,EVERY_DEF]

val rw4 = let
  val lemma = blastLib.BBLAST_PROVE
    ``!v. ((w2w (v:word32)):word8 = w2w (v && 255w)) /\
          (v && 255w) <+ 256w:word32``
  val w2w_w2w_lemma = prove(
    ``w2n (w2w (v:word32) :word8) = w2n (v && 255w:word32)``,
    fs [w2n_11,Once lemma,w2w_def] \\ assume_tac lemma \\ fs [WORD_LO]);
  val lemma1 = prove(
    ``(w:word32) ' (w2n (w2w (v:word32) :word8) - (1 :num)) /\
      w2n (w2w (v:word32) :word8) <= (32 :num)
      <=>
      (v && 255w) <+ 33w /\
      if v && 255w = 0w then w ' 0 else ShiftRight w ((v && 255w) - 1w) ' 0``,
    fs [w2w_w2w_lemma,ShiftRight_def]
    \\ qspec_then `255w && v` mp_tac lemma
    \\ rw []
    \\ Cases_on `255w && v`
    \\ fs [WORD_LO]
    \\ rewrite_tac [GSYM word_sub_def]
    \\ full_simp_tac std_ss [word_arith_lemma2]
    \\ `~(n < 1) /\ (n - 1) < 4294967296 /\ (n <= 32 = n < 33)` by decide_tac
    \\ fs [word_lsr_def,fcpTheory.FCP_BETA]
    \\ Cases_on `n < 33` \\ fs [])
  val lemma2 = prove(
    ``(w:word32) ' (w2n (w2w (v:word32) :word8)) /\
      w2n (w2w (v:word32) :word8) <= (31 :num)
      <=>
      (v && 255w) <+ 32w /\ ShiftRight w (v && 255w) ' 0``,
    fs [w2w_w2w_lemma,ShiftRight_def]
    \\ qspec_then `255w && v` mp_tac lemma
    \\ rw []
    \\ Cases_on `255w && v`
    \\ fs [WORD_LO]
    \\ `n < 4294967296 /\ (n <= 31 = n < 32)` by decide_tac
    \\ fs [word_lsr_def,fcpTheory.FCP_BETA]
    \\ Cases_on `n < 32` \\ fs [])
  val lemma1 = CONJ lemma1 (lemma1 |> RW1 [CONJ_COMM])
  val lemma2 = CONJ lemma2 (lemma2 |> RW1 [CONJ_COMM])
  val lemma3 = CONJ lemma1 lemma2 |> RW [GSYM CONJ_ASSOC]
  in lemma3 end;

val rw1 = prove(
  ``EVERY (\i. ((w:word32) ' i = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_bit i w = ((w && n2w (2 ** i)) <> 0w)) /\
               (word_lsr w i = ShiftRight w ((n2w i):word32)) /\
               (word_asr w i = SignedShiftRight w ((n2w i):word32)) /\
               (word_lsl w i = ShiftLeft w ((n2w i):word32))) (GENLIST I 32) /\
    (word_msb w = (w:word32) ' 31)``,
  FULL_SIMP_TAC (srw_ss()) [EVAL ``GENLIST I 32``,EVERY_DEF,
    ShiftLeft_def,ShiftRight_def,SignedShiftRight_def,w2n_n2w] \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [EVAL ``GENLIST I 32``,EVERY_DEF]

val word_add_with_carry_eq = prove(
  ``word_add_with_carry (x:'a word) y z =
    x + y + if z then 1w else 0w``,
  Cases_on `z` \\ Cases_on `x` \\ Cases_on `y`
  \\ FULL_SIMP_TAC std_ss [word_add_with_carry_def]
  \\ FULL_SIMP_TAC std_ss [carry_out_def,add_with_carry_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,w2w_def,word_add_n2w]);

val w2w_blast = prove(
  ``!w. w <+ n2w (2 ** 33):word64 ==>
        ((w2w ((w2w w):word32) = w) <=> (w && (n2w (2 ** 32)) = 0w))``,
  blastLib.BBLAST_TAC);

val carry_out_eq = prove(
  ``carry_out (x:word32) (y:word32) z =
    ((w2w x + w2w y + if z then 1w else 0w:word64) && n2w (2 ** 32)) <> 0w``,
  Cases_on `z` \\ Cases_on `x` \\ Cases_on `y`
  \\ FULL_SIMP_TAC std_ss [carry_out_def,add_with_carry_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,w2w_def,word_add_n2w]
  \\ `(n + n') < 18446744073709551616` by (fs [] \\ DECIDE_TAC)
  \\ `(n + n' + 1) < 18446744073709551616` by (fs [] \\ DECIDE_TAC)
  \\ `n2w (n + n' + 1) <+ n2w (2 ** 33):word64 /\
      n2w (n + n') <+ n2w (2 ** 33):word64` by (fs [WORD_LO] \\ DECIDE_TAC)
  \\ IMP_RES_TAC w2w_blast
  \\ `(n + n' + 1) < dimword (:64)` by (fs [WORD_LO] \\ DECIDE_TAC)
  \\ `(n + n' + 1) MOD dimword (:32) < dimword (:64) /\
      (n + n') MOD dimword (:32) < dimword (:64)` by
   (REPEAT STRIP_TAC \\ MATCH_MP_TAC LESS_TRANS
    \\ Q.EXISTS_TAC `dimword (:32)`
    \\ FULL_SIMP_TAC std_ss [MATCH_MP MOD_LESS ZERO_LT_dimword]
    \\ EVAL_TAC)
  \\ `(n + n') < dimword (:64)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [w2w_def,w2n_n2w,n2w_11]);

val rw3 = prove(
  ``(w << w2n y = ShiftLeft (w:word64) (w2w (y:word32))) /\
    (w >>> w2n y = ShiftRight (w:word64) (w2w (y:word32))) /\
    (w << w2n x = ShiftLeft (w:word64) (w2w (x:word8))) /\
    (w >>> w2n x = ShiftRight (w:word64) (w2w (x:word8))) /\
    (v << w2n x = ShiftLeft (v:word32) (w2w (x:word8))) /\
    (v >>> w2n x = ShiftRight (v:word32) (w2w (x:word8)))``,
  Cases_on `y` \\ Cases_on `x` \\ fs [ShiftLeft_def,ShiftRight_def,w2w_def]
  \\ `n < 18446744073709551616` by DECIDE_TAC \\ fs []
  \\ `n' < 18446744073709551616` by DECIDE_TAC \\ fs []
  \\ `n' < 4294967296` by DECIDE_TAC \\ fs []);

val fix_align = blastLib.BBLAST_PROVE
  ``(((63 '' 3) v = v:word64) <=> (v && 7w = 0w)) /\
    ((v = ((63 '' 3) v):word64) <=> (v && 7w = 0w)) /\
    (((63 '' 2) v = v:word64) <=> (v && 3w = 0w)) /\
    ((v = ((63 '' 2) v):word64) <=> (v && 3w = 0w)) /\
    (((63 '' 1) v = v:word64) <=> (v && 1w = 0w)) /\
    ((v = ((63 '' 1) v):word64) <=> (v && 1w = 0w)) /\
    (((31 '' 2) w = w:word32) <=> (w && 1w = 0w) /\ (w && 2w = 0w)) /\
    ((w = (31 '' 2) w:word32) <=> (w && 1w = 0w) /\ (w && 2w = 0w)) /\
    (((31 '' 1) w = w:word32) <=> (w && 1w = 0w)) /\
    ((w = (31 '' 1) w:word32) <=> (w && 1w = 0w)) /\
    ((31 '' 2) w = w >>> 2 << 2) /\
    ((31 '' 1) w = w >>> 1 << 1) /\
    ((31 '' 0) w = w)``;

val w2w_w2w_and_255 = prove(
  ``w2w ((w2w:word32->word8) v) = (v && 0xFFw)``,
  blastLib.BBLAST_TAC)

val Shift_intro = prove(
  ``(w >> w2n ((w2w:word32->word8) v) = SignedShiftRight w (v && 0xFFw)) /\
    (w >>> w2n ((w2w:word32->word8) v) = ShiftRight w (v && 0xFFw)) /\
    (w << w2n ((w2w:word32->word8) v) = ShiftLeft w (v && 0xFFw))``,
  fs [SignedShiftRight_def,ShiftRight_def,ShiftLeft_def,GSYM w2w_w2w_and_255]
  \\ fs [w2w_def,w2n_n2w]
  \\ `w2n v MOD 256 < 4294967296` by all_tac \\ fs []
  \\ match_mp_tac LESS_TRANS \\ qexists_tac `256` \\ fs []);

val blast_append_0_lemma = prove(
  ``(((w2w:word32 -> 31 word) w @@ (0w:word1)) : word32 = w << 1) /\
    (((w2w:word32 -> 30 word) w @@ (0w:word2)) : word32 = w << 2)``,
  blastLib.BBLAST_TAC);

val SignedDiv_def = zDefine ‘SignedDiv (w:'a word) (v:'a word) = word_div w v’;
val UnsignedDiv_def = zDefine ‘UnsignedDiv (w:'a word) (v:'a word) = word_quot w v’;

val graph_format_preprocessing = save_thm("graph_format_preprocessing",
  LIST_CONJ [MemAcc8_def, MemAcc32_def, MemAcc64_def,
             ShiftLeft_def, ShiftRight_def, SignedDiv_def, UnsignedDiv_def,
             MemUpdate8_def, MemUpdate32_def, MemUpdate64_def] |> GSYM
  |> CONJ rw1 |> CONJ rw3 |> CONJ rw64 |> CONJ rw16 |> CONJ rw8 |> CONJ rw4
  |> CONJ w2w_carry |> CONJ w2w_carry_alt
  |> CONJ carry_out_eq
  |> CONJ READ32_expand64
  |> CONJ word_add_with_carry_eq
  |> CONJ fix_align
  |> CONJ Shift_intro
  |> CONJ blast_append_0_lemma
  |> RW [GSYM CONJ_ASSOC]
  |> SIMP_RULE std_ss [])

(* misc *)

val STAR_IF = store_thm("STAR_IF",
  ``(if b then x else y) * (q:'a set set) = (if b then x * q else STAR y q)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [])

val emp_STAR = store_thm("emp_STAR",
  ``(emp * p = p) /\ (p * emp = p:'a set set)``,
  SIMP_TAC std_ss [SEP_CLAUSES])

val T_IMP = store_thm("T_IMP",``(T ==> b) ==> b``,SIMP_TAC std_ss [])

val EQ_T = store_thm("EQ_T",``(x = T) ==> x``,SIMP_TAC std_ss [])

val ret_lemma = store_thm("ret_lemma",
  ``(s "ret" = VarWord w) ==> (w = var_word "ret" s)``,
  SRW_TAC [] [var_word_def,var_acc_def]);

val apply_update_NIL = store_thm("apply_update_NIL",
  ``apply_update [] s = (s:'a->'b)``,
  SIMP_TAC std_ss [apply_update_def]);

val var_word_apply_update = store_thm("var_word_apply_update",
  ``var_word n (apply_update ((x,y)::xs) s) =
      if n = x then (case y s of VarWord w => w | _ => 0w) else
        var_word n (apply_update xs s)``,
  SRW_TAC [] [var_word_def,var_acc_def,apply_update_def,APPLY_UPDATE_THM]);

val I_LEMMA = store_thm("I_LEMMA",
  ``(\x.x:'a) = I``,
  SIMP_TAC std_ss [FUN_EQ_THM]);

val Aligned_Align = store_thm("Aligned_Align",
  ``arm$Aligned (w,n) ==> (arm$Align (w:'a word,n) = w)``,
  SIMP_TAC std_ss [armTheory.Aligned_def,armTheory.Align_def]);

val SWITCH_LEMMA = store_thm("SWITCH_LEMMA",
  ``SPEC m (p * f x) c (q * f x) <=>
    !v. (v = x) ==> SPEC m (p * f v) c (q * f v)``,
  SIMP_TAC std_ss []);

val SWITCH_COMBINE = store_thm("SWITCH_COMBINE",
  ``(b1 ==> SPEC m p c1 q1) /\ (b2 ==> SPEC m p c2 q2) ==>
    (~b1 ==> b2) ==> SPEC m p (c1 UNION c2) (if b1 then q1 else q2)``,
  Cases_on `b1` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_SUBSET_CODE |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ TRY (Q.EXISTS_TAC `c1` \\ FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ TRY (Q.EXISTS_TAC `c2` \\ FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC));

val SPEC_PC_LEMMA = store_thm("SPEC_PC_LEMMA",
  ``SPEC m (p * r x) c q ==>
    !pc. (pc = x) ==> SPEC m (p * r pc) c q``,
  SIMP_TAC std_ss []);

val ABBBREV_CODE_LEMMA = store_thm("ABBBREV_CODE_LEMMA",
  ``!a (x :('a, 'b, 'c) processor) p c q.
      (a ==> SPEC x p c q) ==> !d. c SUBSET d ==> a ==> SPEC x p d q``,
  REPEAT STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC SPEC_SUBSET_CODE);

val NEQ_SYM = store_thm("NEQ_SYM",
  ``~(x = y) <=> ~(y = x)``,
  METIS_TAC []);

val SKIP_TAG_IMP_CALL_ARM = store_thm("SKIP_TAG_IMP_CALL_ARM",
  ``IMPL_INST (ARM code) locs
     (Inst entry (K T)
        (ASM (SOME (\s. SKIP_TAG str)) []
           (Jump exit))) ==>
    !old. (old = str) ==>
    !name.
      (locs name = SOME entry) ==>
      IMPL_INST (ARM code) locs
       (Inst entry (K T)
         (CALL NONE
           [("ret",(\s. VarWord exit));
            ("r0",var_acc "r0");
            ("r1",var_acc "r1");
            ("r2",var_acc "r2");
            ("r3",var_acc "r3");
            ("r4",var_acc "r4");
            ("r5",var_acc "r5");
            ("r6",var_acc "r6");
            ("r7",var_acc "r7");
            ("r8",var_acc "r8");
            ("r9",var_acc "r9");
            ("r10",var_acc "r10");
            ("r11",var_acc "r11");
            ("r12",var_acc "r12");
            ("r13",var_acc "r13");
            ("r14",var_acc "r14");
            ("r15",var_acc "r15");
            ("r16",var_acc "r16");
            ("r17",var_acc "r17");
            ("r18",var_acc "r18");
            ("r19",var_acc "r19");
            ("r20",var_acc "r20");
            ("r21",var_acc "r21");
            ("r22",var_acc "r22");
            ("r23",var_acc "r23");
            ("r24",var_acc "r24");
            ("r25",var_acc "r25");
            ("r26",var_acc "r26");
            ("r27",var_acc "r27");
            ("r28",var_acc "r28");
            ("r29",var_acc "r29");
            ("r30",var_acc "r30");
            ("r31",var_acc "r31");
            ("sp",var_acc "sp");
            ("mode",var_acc "mode"); ("n",var_acc "n");
            ("z",var_acc "z"); ("c",var_acc "c"); ("v",var_acc "v");
            ("mem",var_acc "mem"); ("dom",var_acc "dom");
            ("stack",var_acc "stack");
            ("dom_stack",var_acc "dom_stack");
            ("clock",var_acc "clock"); ("ret_addr_input",var_acc "r0")]
          name (Jump exit)))``,
  fs [IMPL_INST_def,next_ok_def,check_ret_def,exec_next_def,
      check_jump_def,get_assert_def,LET_THM]
  \\ fs [ARM_def] \\ rpt BasicProvers.TOP_CASE_TAC \\ fs []
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
         arm_STATE_CPSR_def,var_bool_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
         arm_STATE_CPSR_def,var_bool_def,arm_STATE_REGS_def,
         m0_STATE_REGS_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
      arm_STATE_REGS_def,STAR_ASSOC,SPEC_REFL]);

val SKIP_TAG_IMP_CALL_ARM8 = store_thm("SKIP_TAG_IMP_CALL_ARM8",
  ``IMPL_INST (ARM8 code) locs
     (Inst entry (K T)
        (ASM (SOME (\s. SKIP_TAG str)) []
           (Jump exit))) ==>
    !old. (old = str) ==>
    !name.
      (locs name = SOME entry) ==>
      IMPL_INST (ARM8 code) locs
       (Inst entry (K T)
         (CALL NONE
           [("ret",(\s. VarWord exit));
            ("r0",var_acc "r0");
            ("r1",var_acc "r1");
            ("r2",var_acc "r2");
            ("r3",var_acc "r3");
            ("r4",var_acc "r4");
            ("r5",var_acc "r5");
            ("r6",var_acc "r6");
            ("r7",var_acc "r7");
            ("r8",var_acc "r8");
            ("r9",var_acc "r9");
            ("r10",var_acc "r10");
            ("r11",var_acc "r11");
            ("r12",var_acc "r12");
            ("r13",var_acc "r13");
            ("r14",var_acc "r14");
            ("r15",var_acc "r15");
            ("r16",var_acc "r16");
            ("r17",var_acc "r17");
            ("r18",var_acc "r18");
            ("r19",var_acc "r19");
            ("r20",var_acc "r20");
            ("r21",var_acc "r21");
            ("r22",var_acc "r22");
            ("r23",var_acc "r23");
            ("r24",var_acc "r24");
            ("r25",var_acc "r25");
            ("r26",var_acc "r26");
            ("r27",var_acc "r27");
            ("r28",var_acc "r28");
            ("r29",var_acc "r29");
            ("r30",var_acc "r30");
            ("r31",var_acc "r31");
            ("sp",var_acc "sp");
            ("mode",var_acc "mode"); ("n",var_acc "n");
            ("z",var_acc "z"); ("c",var_acc "c"); ("v",var_acc "v");
            ("mem",var_acc "mem"); ("dom",var_acc "dom");
            ("stack",var_acc "stack");
            ("dom_stack",var_acc "dom_stack");
            ("clock",var_acc "clock"); ("ret_addr_input",var_acc "r0")]
          name (Jump exit)))``,
  fs [IMPL_INST_def,next_ok_def,check_ret_def,exec_next_def,
      check_jump_def,get_assert_def,LET_THM]
  \\ fs [ARM8_def] \\ rpt BasicProvers.TOP_CASE_TAC \\ fs []
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm8_STATE_def,m0_STATE_def,
         arm8_PSTATE_NZCV_def,var_bool_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm8_STATE_def,m0_STATE_def,
         arm8_PSTATE_NZCV_def,var_bool_def,arm8_STATE_REGS_def,
         m0_STATE_REGS_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm8_STATE_def,m0_STATE_def,
      arm8_STATE_REGS_def,STAR_ASSOC,SPEC_REFL]);

val SKIP_TAG_IMP_CALL_ARM8 = store_thm("SKIP_TAG_IMP_CALL_ARM8",
  ``IMPL_INST (ARM8 code) locs
     (Inst entry (K T)
        (ASM (SOME (\s. SKIP_TAG str)) []
           (Jump exit))) ==>
    !old. (old = str) ==>
    !name:string.
      T ==>
      IMPL_INST (ARM8 code) locs
       (Inst entry (K T)
         (ASM (SOME (K F)) [] Return))``,
  fs [IMPL_INST_def,next_ok_def,check_ret_def,exec_next_def,
      check_jump_def,get_assert_def,LET_THM,jump_ok_def]);

val SKIP_TAG_IMP_CALL_M0 = store_thm("SKIP_TAG_IMP_CALL_M0",
  ``IMPL_INST (M0 code) locs
     (Inst entry (K T)
        (ASM (SOME (\s. SKIP_TAG str)) []
           (Jump exit))) ==>
    !old. (old = str) ==>
    !name.
      (locs name = SOME entry) ==>
      IMPL_INST (M0 code) locs
       (Inst entry (K T)
         (CALL NONE
           [("ret",(\s. VarWord exit));
            ("r0",var_acc "r0");
            ("r1",var_acc "r1");
            ("r2",var_acc "r2");
            ("r3",var_acc "r3");
            ("r4",var_acc "r4");
            ("r5",var_acc "r5");
            ("r6",var_acc "r6");
            ("r7",var_acc "r7");
            ("r8",var_acc "r8");
            ("r9",var_acc "r9");
            ("r10",var_acc "r10");
            ("r11",var_acc "r11");
            ("r12",var_acc "r12");
            ("r13",var_acc "r13");
            ("r14",var_acc "r14");
            ("r15",var_acc "r15");
            ("r16",var_acc "r16");
            ("r17",var_acc "r17");
            ("r18",var_acc "r18");
            ("r19",var_acc "r19");
            ("r20",var_acc "r20");
            ("r21",var_acc "r21");
            ("r22",var_acc "r22");
            ("r23",var_acc "r23");
            ("r24",var_acc "r24");
            ("r25",var_acc "r25");
            ("r26",var_acc "r26");
            ("r27",var_acc "r27");
            ("r28",var_acc "r28");
            ("r29",var_acc "r29");
            ("r30",var_acc "r30");
            ("r31",var_acc "r31");
            ("sp",var_acc "sp");
            ("mode",var_acc "mode"); ("n",var_acc "n");
            ("z",var_acc "z"); ("c",var_acc "c"); ("v",var_acc "v");
            ("mem",var_acc "mem"); ("dom",var_acc "dom");
            ("stack",var_acc "stack");
            ("dom_stack",var_acc "dom_stack");
            ("clock",var_acc "clock"); ("ret_addr_input",var_acc "r0")]
          name (Jump exit)))``,
  fs [IMPL_INST_def,next_ok_def,check_ret_def,exec_next_def,
      check_jump_def,get_assert_def,LET_THM]
  \\ fs [M0_def] \\ rpt BasicProvers.TOP_CASE_TAC \\ fs []
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
         arm_STATE_CPSR_def,var_bool_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
         arm_STATE_CPSR_def,var_bool_def,arm_STATE_REGS_def,
         m0_STATE_REGS_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
      arm_STATE_REGS_def,STAR_ASSOC,SPEC_REFL]);

val SKIP_TAG_IMP_CALL_RISCV = store_thm("SKIP_TAG_IMP_CALL_RISCV",
  ``IMPL_INST (RISCV c) locs
     (Inst entry (K T)
        (ASM (SOME (\s. SKIP_TAG str)) []
           (Jump exit))) ==>
    !old. (old = str) ==>
    !name.
      (locs name = SOME entry) ==>
      IMPL_INST (RISCV code) locs
       (Inst entry (K T)
         (CALL NONE
           [("ret",(\s. VarWord exit));
            ("r0",var_acc "r0");
            ("r1",var_acc "r1");
            ("r2",var_acc "r2");
            ("r3",var_acc "r3");
            ("r4",var_acc "r4");
            ("r5",var_acc "r5");
            ("r6",var_acc "r6");
            ("r7",var_acc "r7");
            ("r8",var_acc "r8");
            ("r9",var_acc "r9");
            ("r10",var_acc "r10");
            ("r11",var_acc "r11");
            ("r12",var_acc "r12");
            ("r13",var_acc "r13");
            ("r14",var_acc "r14");
            ("r15",var_acc "r15");
            ("r16",var_acc "r16");
            ("r17",var_acc "r17");
            ("r18",var_acc "r18");
            ("r19",var_acc "r19");
            ("r20",var_acc "r20");
            ("r21",var_acc "r21");
            ("r22",var_acc "r22");
            ("r23",var_acc "r23");
            ("r24",var_acc "r24");
            ("r25",var_acc "r25");
            ("r26",var_acc "r26");
            ("r27",var_acc "r27");
            ("r28",var_acc "r28");
            ("r29",var_acc "r29");
            ("r30",var_acc "r30");
            ("r31",var_acc "r31");
            ("sp",var_acc "sp");
            ("mode",var_acc "mode"); ("n",var_acc "n");
            ("z",var_acc "z"); ("c",var_acc "c"); ("v",var_acc "v");
            ("mem",var_acc "mem"); ("dom",var_acc "dom");
            ("stack",var_acc "stack");
            ("dom_stack",var_acc "dom_stack");
            ("clock",var_acc "clock"); ("ret_addr_input",var_acc "r10")]
          name (Jump exit)))``,
  fs [IMPL_INST_def,next_ok_def,check_ret_def,exec_next_def,
      check_jump_def,get_assert_def,LET_THM]
  \\ fs [RISCV_def] \\ rpt BasicProvers.TOP_CASE_TAC \\ fs []
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
         arm_STATE_CPSR_def,var_bool_def,var_nat_def,m0_STATE_PSR_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
         arm_STATE_CPSR_def,var_bool_def,arm_STATE_REGS_def,
         m0_STATE_REGS_def,var_nat_def,m0_STATE_PSR_def,riscv_STATE_REGS_def,
         riscv_STATE_def,
         var_word_def,var_acc_def,ret_and_all_names_def,all_names_def,
         var_dom_def,var_word_def,var_mem_def,var_word8_def]
  \\ fs [apply_update_def,APPLY_UPDATE_THM,arm_STATE_def,m0_STATE_def,
      arm_STATE_REGS_def,STAR_ASSOC,SPEC_REFL]);

val fixwidth_w2v = prove(
  ``fixwidth (dimindex (:'a)) (w2v (w:'a word)) = w2v w``,
  EVAL_TAC \\ fs []);

val bit_field_insert_31_16 = store_thm("bit_field_insert_31_16",
  ``(bit_field_insert 31 16 v (w:word32) =
     (v << 16 || (w << 16) >>> 16):word32) /\
    (bit_field_insert 31 16 (x:word16) (w:word32) =
     (w2w x << 16 || (w << 16) >>> 16):word32)``,
  blastLib.BBLAST_TAC);

val v2w_field_insert_31_16 = prove(
  ``(v2w (field_insert 31 16
                      (field 15 0 (w2v (w:word32)))
                      (w2v (v:word32)))) =
    bit_field_insert 31 16 w v``,
  fs [bit_field_insert_def,bitstringTheory.field_insert_def]
  \\ once_rewrite_tac [GSYM fixwidth_w2v]
  \\ rewrite_tac [GSYM bitstringTheory.word_modify_v2w,bitstringTheory.v2w_w2v]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC \\ fs []
  \\ EVAL_TAC \\ Cases_on `i` \\ fs []
  \\ rpt (Cases_on `n` \\ fs [] \\ Cases_on `n'` \\ fs []));

val word_cancel_extra = store_thm("word_cancel_extra",
  ``(w + x − w = x:'a word) /\
    (w + x − (w + y) = x - y:'a word) /\
    (w + x − (w - y) = x + y:'a word)``,
  fs [WORD_LEFT_ADD_DISTRIB]);

val aligned_rw =
  LIST_CONJ [
    Q.SPEC ‘1’ alignmentTheory.aligned_bitwise_and,
    Q.SPEC ‘2’ alignmentTheory.aligned_bitwise_and,
    Q.SPEC ‘3’ alignmentTheory.aligned_bitwise_and,
    Q.SPEC ‘4’ alignmentTheory.aligned_bitwise_and] |> SIMP_RULE std_ss [];

val export_init_rw = save_thm("export_init_rw",
  LIST_CONJ [aligned_rw, GSYM wordsTheory.WORD_SUB_LZERO,
             bit_field_insert_31_16,
             v2w_field_insert_31_16]);

val m0_preprocessing = save_thm("m0_preprocessing",
  CONJ (EVAL ``RName_LR = RName_PC``) (EVAL ``RName_PC = RName_LR``));

val WRITE64_intro = store_thm("WRITE64_intro",
  ``m⦇a ↦ (7 >< 0) w; a + 1w ↦ (15 >< 8) w;
        a + 3w ↦ (31 >< 24) w; a + 7w ↦ (63 >< 56) w;
        a + 5w ↦ (47 >< 40) w; a + 2w ↦ (23 >< 16) w;
        a + 4w ↦ (39 >< 32) w; a + 6w ↦ (55 >< 48) w⦈ =
    WRITE64 (a:word64) (w:word64) (m:word64->word8)``,
  fs [WRITE64_def,FUN_EQ_THM,combinTheory.APPLY_UPDATE_THM]
  \\ rw [] \\ fs [] \\ fs [WORD_EQ_ADD_CANCEL]
  \\ blastLib.BBLAST_TAC);

val v2w_sing = store_thm("v2w_sing",
  ``v2w [x] = if x then 1w else 0w``,
  Cases_on `x` \\ EVAL_TAC);

val _ = export_theory();
