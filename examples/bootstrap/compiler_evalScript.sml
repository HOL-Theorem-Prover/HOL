
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open wordsTheory wordsLib automationLib compiler_progTheory;

val _ = new_theory "compiler_eval";


Definition compiler_str_def:
  compiler_str = prog2str compiler_prog coms
End

Definition compiler_asm_def:
  compiler_asm = codegen compiler_prog
End

Definition compiler_asm_str_def:
  compiler_asm_str = asm2str compiler_asm
End

Theorem compiler_str      = time EVAL “compiler_str”;
Theorem compiler_asm      = time EVAL “compiler_asm”;
Theorem compiler_asm_str  = time EVAL “compiler_asm_str”;

val _ = write_hol_string_to_file "compiler_prog.txt" (compiler_str |> concl |> rand);
val _ = write_hol_string_to_file "compiler_asm.s"    (compiler_asm_str |> concl |> rand);

val _ = export_theory();
