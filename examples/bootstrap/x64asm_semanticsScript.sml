
open HolKernel Parse boolLib bossLib;
open wordsTheory wordsLib arithmeticTheory listTheory llistTheory pairTheory
     finite_mapTheory x64asm_syntaxTheory alignmentTheory lprefix_lubTheory;

val _ = new_theory "x64asm_semantics";


(* semantics *)

Datatype:
  word_or_ret = Word word64 | RetAddr num
End

Datatype:
  state =
    <| instructions : inst list
     ; pc : num
     ; regs : reg -> word64 option
     ; stack : word_or_ret list
     ; memory : word64 -> word64 option option
     ; input  : char llist  (* input can be an infinite stream     *)
     ; output : char list   (* at each point output must be finite *)
     |>
End

Definition lookup_def:
  lookup n [] = NONE ∧
  lookup n (x::xs) = if n = 0 then SOME x else lookup (n-1) xs
End

Definition fetch_def:
  fetch s = lookup s.pc s.instructions
End

Definition inc_def:
  inc s = s with pc := s.pc + 1
End

Definition write_reg_def:
  write_reg r w s = s with regs := s.regs⦇r ↦ SOME w⦈
End

Definition unset_reg_def:
  unset_regs [] s = s ∧
  unset_regs (r::rs) s = unset_regs rs (s with regs := s.regs⦇r ↦ NONE⦈)
End

Definition put_char_def:
  put_char c s = s with output := s.output ++ [c]
End

Definition read_mem_def:
  read_mem a s =
    case s.memory a of
    | NONE => NONE
    | SOME opt => opt
End

Definition write_mem_def:
  write_mem a w s =
    case s.memory a of
    | SOME NONE => SOME (s with memory := ((a =+ SOME (SOME w)) s.memory))
    | _ => NONE
End

Definition set_stack_def:
  set_stack xs s = (s with stack := xs)
End

Definition set_pc_def:
  set_pc n s = (s with pc := n)
End

Datatype:
  s_or_h = State state | Halt word64 string
End

Inductive take_branch:
  (∀s.
    take_branch Always s T)
  ∧
  (∀s r1 r2 w1 w2.
    s.regs r1 = SOME w1 ∧
    s.regs r2 = SOME w2 ⇒
    take_branch (Less r1 r2) s (w2n w1 < w2n w2))
  ∧
  (∀s r1 r2 w1 w2.
    s.regs r1 = SOME w1 ∧
    s.regs r2 = SOME w2 ⇒
    take_branch (Equal r1 r2) s (w1 = w2))
End

Overload EOF_CONST = “0xFFFFFFFFw : word64”

Definition read_char_def:
  read_char input =
    case input of
    | LNIL => (EOF_CONST, input)
    | LCONS c cs => (n2w (ORD c), cs)
End

Inductive step:
  (∀s r w.
    fetch s = SOME (Const r w) ⇒
    step (State s) (State (write_reg r w (inc s))))
  ∧
  (∀s r1 r2 w.
    fetch s = SOME (Mov r1 r2) ∧
    s.regs r2 = SOME w ⇒
    step (State s) (State (write_reg r1 w (inc s))))
  ∧
  (∀s r1 r2 w1 w2.
    fetch s = SOME (Add r1 r2) ∧
    s.regs r1 = SOME w1 ∧
    s.regs r2 = SOME w2 ⇒
    step (State s) (State (write_reg r1 (w1 + w2) (inc s))))
  ∧
  (∀s r1 r2 w1 w2.
    fetch s = SOME (Sub r1 r2) ∧
    s.regs r1 = SOME w1 ∧
    s.regs r2 = SOME w2 ⇒
    step (State s) (State (write_reg r1 (w1 - w2) (inc s))))
  ∧
  (∀s r w1 w2.
    fetch s = SOME (Div r) ∧ w2 ≠ 0w ∧
    s.regs RDX = SOME 0w ∧
    s.regs RAX = SOME w1 ∧
    s.regs r = SOME w2 ⇒
    step (State s) (State (write_reg RAX (n2w (w2n w1 DIV w2n w2))
                            (write_reg RDX (n2w (w2n w1 MOD w2n w2))
                              (inc s)))))
  ∧
  (∀s cond n yes.
    fetch s = SOME (Jump cond n) ∧
    take_branch cond s yes ⇒
    step (State s) (State (set_pc (if yes then n else (s.pc + 1)) s)))
  ∧
  (∀s n.
    fetch s = SOME (Call n) ⇒
    step (State s) (State (set_pc n
                      (set_stack (RetAddr (s.pc+1) :: s.stack) s))))
  ∧
  (∀s n rest.
    fetch s = SOME Ret ∧
    s.stack = RetAddr n :: rest ⇒
    step (State s) (State (set_pc n (set_stack rest s))))
  ∧
  (∀s r w rest.
    fetch s = SOME (Pop r) ∧
    s.stack = Word w :: rest ⇒
    step (State s) (State (set_stack rest (write_reg r w (inc s)))))
  ∧
  (∀s r w.
    fetch s = SOME (Push r) ∧
    s.regs r = SOME w ⇒
    step (State s) (State (set_stack (Word w :: s.stack) (inc s))))
  ∧
  (∀s r w offset.
    fetch s = SOME (Load_RSP r offset) ∧
    offset < LENGTH s.stack ∧
    EL offset s.stack = Word w ⇒
    step (State s) (State (write_reg r w (inc s))))
  ∧
  (∀s xs ys.
    fetch s = SOME (Add_RSP (LENGTH xs)) ∧
    s.stack = xs ++ ys ⇒
    step (State s) (State (set_stack ys (inc s))))
  ∧
  (∀s src ra imm wa w s'.
    fetch s = SOME (Store src ra imm) ∧
    s.regs ra = SOME wa ∧
    s.regs src = SOME w ∧
    write_mem (wa + w2w imm) w s = SOME s' ⇒
    step (State s) (State (inc s')))
  ∧
  (∀s dst ra imm wa w.
    fetch s = SOME (Load dst ra imm) ∧
    s.regs ra = SOME wa ∧
    read_mem (wa + w2w imm) s = SOME w ⇒
    step (State s) (State (write_reg dst w (inc s))))
  ∧
  (∀s c.
    fetch s = SOME GetChar ∧
    read_char s.input = (c, rest) ∧
    EVEN (LENGTH s.stack) ⇒
    step (State s)
         (State (write_reg RET_REG c
                   (unset_regs [ARG_REG; RDX]
                      (inc (s with input := rest))))))
  ∧
  (∀s n.
    fetch s = SOME PutChar ∧
    s.regs ARG_REG = SOME (n2w n) ∧ n < 256 ∧
    EVEN (LENGTH s.stack) ⇒
    step (State s)
         (State (unset_regs [RET_REG; ARG_REG; RDX]
                   (inc (put_char (CHR n) s)))))
  ∧
  (∀s exit_code.
    fetch s = SOME Exit ∧
    s.regs ARG_REG = SOME exit_code ∧
    EVEN (LENGTH s.stack) ⇒
    step (State s) (Halt exit_code s.output))
End

Definition can_write_mem_def:
  can_write_mem_at m a <=> m a = SOME NONE
End

Definition memory_writable_def:
  memory_writable r14 r15 m <=>
    r14 <=+ r15 ∧ aligned 4 r14 ∧ aligned 4 r15 ∧ r14 ≠ 0w ∧
    ∀a. r14 <=+ a ∧ a <+ r15 ∧ aligned 3 a ⇒
        can_write_mem_at m a
End

Definition init_state_ok_def:
  init_state_ok t input asm =
    ∃r14 r15.
      t.pc = 0 ∧ t.instructions = asm ∧
      t.input = input ∧ t.output = [] ∧
      t.stack = [] ∧
      t.regs R14 = SOME r14 ∧
      t.regs R15 = SOME r15 ∧
      memory_writable r14 r15 t.memory
End

val _ = set_fixity "asm_terminates" (Infixl 480);

Definition asm_terminates_def:
  (input, asm) asm_terminates output =
    ∃t. init_state_ok t input asm ∧
        step꙳ (State t) (Halt 0w output)  (* reflexive transitive closure of step *)
End

Overload asm_terminates =
  “λ(input:string,p) output. (fromList input,p) asm_terminates output”;

val _ = set_fixity "asm_diverges" (Infixl 480);

Definition asm_diverges_def:
  (input, asm) asm_diverges output =
    ∃t. init_state_ok t input asm ∧
      (* repeated application of step never halts or gets stuck: *)
      (∀k. ∃t'. NRC step k (State t) (State t')) ∧
      (* the output is the least upper bound of all reachable output *)
      output = build_lprefix_lub { fromList t'.output | step꙳ (State t) (State t') }
End

val _ = export_theory();
