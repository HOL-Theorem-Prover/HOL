
open HolKernel Parse boolLib bossLib term_tactic cv_transLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open wordsTheory wordsLib automationLib compiler_progTheory compiler_funs_cvTheory;

val _ = new_theory "compiler_eval";

val _ = max_print_depth := 10;

Definition compiler_str_def:
  compiler_str = prog2str compiler_prog coms
End

Definition compiler_asm_def:
  compiler_asm = codegen compiler_prog
End

Definition compiler_asm_str_def:
  compiler_asm_str = asm2str compiler_asm
End

val _ = cv_trans_deep_embedding EVAL compiler_prog_def;
val _ = cv_trans coms_def;
val _ = cv_trans compiler_str_def;
val _ = cv_trans compiler_asm_def;
val _ = cv_trans compiler_asm_str_def;

Theorem compiler_str      = time cv_eval “compiler_str”;
Theorem compiler_asm      = time cv_eval “compiler_asm”;
Theorem compiler_asm_str  = time cv_eval “compiler_asm_str”;

val _ = write_hol_string_to_file "compiler_prog.txt" (compiler_str |> concl |> rand);
val _ = write_hol_string_to_file "compiler_asm.s"    (compiler_asm_str |> concl |> rand);

val _ = export_theory();
