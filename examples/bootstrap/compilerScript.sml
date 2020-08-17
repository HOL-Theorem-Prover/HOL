(*
  This file contains the top-level compiler definition.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory x64asm_syntaxTheory
     parsingTheory codegenTheory wordsLib;

val _ = new_theory "compiler";

Definition compiler_def:
  compiler input =
    asm2str (codegen (parser (lexer input)))
End

val _ = export_theory();
