
open HolKernel Parse boolLib bossLib;
open wordsTheory wordsLib arithmeticTheory listTheory stringTheory finite_mapTheory;

val _ = new_theory "x64asm_syntax";


(* syntax *)

Datatype:
  reg = RAX (* ret val *)
      | RDI (* arg to call *)
      | RBX | RBP | R12 | R13 | R14 | R15 (* callee saved *)
      | RDX (* caller saved, i.e. gets clobbered by external calls *)
End

Overload ARG_REG[inferior] = “RDI”
Overload RET_REG[inferior] = “RAX”

Datatype:
  cond = Always | Less reg reg | Equal reg reg
End

Datatype:
  inst =
     (* arithmetic *)
   | Const reg word64
   | Mov reg reg
   | Add reg reg
   | Sub reg reg
   | Div reg
     (* jumps *)
   | Jump cond num
   | Call num
     (* stack *)
   | Ret
   | Pop reg
   | Push reg
   | Add_RSP num
   | Load_RSP reg num
     (* memory *)
   | Load reg reg word4
   | Store reg reg word4
     (* I/O *)
   | GetChar
   | PutChar
   | Exit
     (* comment (has no semantics) *)
   | Comment string
End

Type asm[pp] = “:inst list”;


(* converting to string form *)

val reg_tm = (rand o concl o REWRITE_CONV [APPEND])
 “reg RAX s = "%rax" ++ s ∧
  reg RDI s = "%rdi" ++ s ∧
  reg RDX s = "%rdx" ++ s ∧
  reg RBP s = "%rbp" ++ s ∧
  reg RBX s = "%rbx" ++ s ∧
  reg R12 s = "%r12" ++ s ∧
  reg R13 s = "%r13" ++ s ∧
  reg R14 s = "%r14" ++ s ∧
  reg R15 s = "%r15" ++ s”

Definition reg_def:
  ^reg_tm
End

Definition num_def:
  num n s = if n < 10 then CHR (48 + n) :: s else
                num (n DIV 10) (CHR (48 + (n MOD 10)) :: s)
End

Definition lab_def:
  lab n s = #"L" :: num n s
End

Definition clean_def:
  clean [] acc = acc ∧
  clean (c::cs) acc = if ORD c < 43 then clean cs acc else c :: clean cs acc
End

val inst_tm = (rand o concl o REWRITE_CONV [APPEND])
 “inst (Const r imm) s = "movq $" ++ num (w2n imm) (", " ++ reg r s) ∧
  inst (Mov dst src) s = "movq " ++ reg src (", " ++ reg dst s) ∧
  inst (Add dst src) s = "addq " ++ reg src (", " ++ reg dst s) ∧
  inst (Sub dst src) s = "subq " ++ reg src (", " ++ reg dst s) ∧
  inst (Div r) s = "divq " ++ reg r s ∧
  inst (Jump Always n) s = "jmp " ++ lab n s ∧
  inst (Jump (Equal r1 r2) n) s =
    "cmpq " ++ reg r2 (", " ++ reg r1 (" ; je " ++ lab n s)) ∧
  inst (Jump (Less r1 r2) n) s =
    "cmpq " ++ reg r2 (", " ++ reg r1 (" ; jb " ++ lab n s)) ∧
  inst (Call n) s = "call " ++ lab n s ∧
  inst Ret s = "ret" ++ s ∧
  inst (Pop r) s = "popq " ++ reg r s ∧
  inst (Push r) s = "pushq " ++ reg r s ∧
  inst (Load_RSP r n) s = "movq " ++ num (8 * n) ("(%rsp), " ++ reg r s) ∧
  inst (Add_RSP n) s = "addq $" ++ num (8 * n) (", %rsp" ++ s) ∧
  inst (Store src a w) s =
    "movq " ++ reg src (", " ++ num (w2n w) ("(" ++ reg a (")" ++ s))) ∧
  inst (Load dst a w) s =
    "movq " ++ num (w2n w) ("(" ++ reg a ("), " ++ reg dst s)) ∧
  inst GetChar s = "movq stdin(%rip), %rdi ; call _IO_getc@PLT" ++ s ∧
  inst PutChar s = "movq stdout(%rip), %rsi ; call _IO_putc@PLT" ++ s ∧
  inst Exit s = "call exit@PLT" ++ s ∧
  inst (Comment c) s = "\n\n\t/* " ++ clean c (" */" ++ s)”

Definition inst_def:
  ^inst_tm
End

Definition insts_def:
  insts n [] = [] ∧
  insts n (x::xs) = lab n (#":" :: #"\t" :: inst x (#"\n" :: insts (n+1) xs))
End

Definition asm2str_def:
  asm2str xs = FLAT
    ["\t.bss\n";
     "\t.p2align 3          /* 8-byte align        */\n";
     "heapS:\n";
     "\t.space 8*1024*1024  /* bytes of heap space */\n";
     "\t.p2align 3          /* 8-byte align        */\n";
     "heapE:\n\n";
     "\t.text\n";
     "\t.globl main\n";
     "main:\n";
     "\tsubq $8, %rsp        /* 16-byte align %rsp */\n";
     "\tmovabs $heapS, %r14  /* r14 := heap start  */\n";
     "\tmovabs $heapE, %r15  /* r15 := heap end    */\n\n"]
    ++ insts 0 xs
End

val _ = export_theory();
