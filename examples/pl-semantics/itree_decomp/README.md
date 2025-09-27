# Proof-producing decompilation into interaction trees

## Introduction
The Interaction Tree (Xia et al., 2020) is a data structure for representing possibly __infinite__ computations with a __formalised__ treatment of the interactions between the program and the environment. We believe that it is convenient and useful for verification purposes to use this structure as a high-level representation for programs (denotational semantics). The decompiler (into interaction trees) will automatically generate the interaction trees that __fully__ describe the behaviour of a program. The decompiler also guarantees the __correctness__ of its output by producing correspondence theorems between the programs and the interaction trees.

## Language
We define `lambdaStateLang` as a simple imperative language with its interaction tree semantics. The language has simple loops `While` so it is possible to have infinite programs, sequencing operator `Seq` as in a practical imperative language, a `FlipCoin` call for random choosing between the two program bodies, and a `Skip` that does nothing. `lambdaStateLang` has immutable states, which serves only for the purpose of returning a program for each function `Call`.

The interaction tree semantics of the language is defined as a step function that unfolds the next behaviour of the program. Manually deriving the interaction tree representation requires self-exploring the programs and figuring out which trees that describes the program. Proving the correctness of the representation also requires care in rewriting the terms since the semantics of infinite programs can be infinitely traversed.

## Decompilation
The decompiler takes input as a program and outputs a triple of theorems
- A conjunction of abbreviated mutually recursive tree definitions that fully describe the behaviour program and omit the unfolding of the language semantics.
- A conjunction of definitions of what exactly the abbreviations are (which program segments that they directly stand for).
- An abbreviation of the program state (so we are printing each occurrence of the state as a name rather than a long lambda function).