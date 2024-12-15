# A Small Verified Bootstrapped Compiler

The source language is defined in files:
 - [source_syntaxScript.sml](source_syntaxScript.sml)
 - [source_valuesScript.sml](source_valuesScript.sml)
 - [source_semanticsScript.sml](source_semanticsScript.sml)
 - [source_propertiesScript.sml](source_propertiesScript.sml)

The target assembly language is defined in files:
 - [x64asm_syntaxScript.sml](x64asm_syntaxScript.sml)
 - [x64asm_semanticsScript.sml](x64asm_semanticsScript.sml)
 - [x64asm_propertiesScript.sml](x64asm_propertiesScript.sml)

The code generator and its verification proof:
 - [codegenScript.sml](codegenScript.sml)
 - [codegen_proofsScript.sml](codegen_proofsScript.sml)

Functions and proofs about lexing, parsing and pretty printing of source code:
 - [parsingScript.sml](parsingScript.sml)
 - [parsing_proofsScript.sml](parsing_proofsScript.sml)
 - [printingScript.sml](printingScript.sml)

Top-level compiler definition as shallow embedding is at the bottom of:
 - [codegenScript.sml](codegenScript.sml)

Automation that converts shallow embeddings into deep embeddings:
 - [automation_lemmasScript.sml](automation_lemmasScript.sml)
 - [automationLib.sml](automationLib.sml)
 - [automationLib.sig](automationLib.sig)
 - [compiler_progScript.sml](compiler_progScript.sml)

In-logic evaluation of the code generator applied to the deeply embedded compiler:
 - [compiler_evalScript.sml](compiler_evalScript.sml)

A file with the top-level correctness theorems:
 - [compiler_proofsScript.sml](compiler_proofsScript.sml)
