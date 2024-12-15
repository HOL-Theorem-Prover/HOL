(*
  Proves that the compiler in assembly form implements the compiler function.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory x64asm_syntaxTheory
     parsingTheory codegenTheory wordsLib compiler_evalTheory
     codegen_proofsTheory compiler_progTheory parsing_proofsTheory;

val _ = new_theory "compiler_proofs";

Theorem compiler_asm_correct:
  ∀input output.
    (input, compiler_asm) asm_terminates output ⇒
    output = compiler input
Proof
  metis_tac [compiler_asm_def,codegen_terminates,compiler_prog_correct]
QED

Theorem compiler_compiler_str:
  compiler compiler_str = compiler_asm_str
Proof
  fs [compiler_str_def,codegenTheory.compiler_def,
      parser_lexer_prog2str,compiler_asm_str_def,compiler_asm_def]
QED

Theorem compiler_asm_bootstrap:
  (compiler_str, compiler_asm) asm_terminates output ⇒
  output = compiler_asm_str
Proof
  metis_tac [compiler_asm_correct,compiler_compiler_str]
QED

val _ = export_theory();
