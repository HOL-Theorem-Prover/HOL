(*
  Proves that the compiler in assembly form implements the compiler function.
*)
Theory compiler_proofs
Ancestors
  arithmetic list pair finite_map string
  source_values source_syntax x64asm_syntax
  parsing codegen compiler_eval
  codegen_proofs compiler_prog parsing_proofs

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
