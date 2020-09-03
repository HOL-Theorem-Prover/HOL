# A Hoare Logic for Diverging Programs

This directory contains:

 1. a formalisation of a small While language with support for output;

 2. a standard total-correctness Hoare logic that has been proved sound and complete;

 3. a new Hoare logic for proving that programs diverge: this new logic has also been proved sound and complete.

The files are:

[while_langScript.sml](while_langScript.sml): definition of the While language

[while_lang_lemmasScript.sml](while_lang_lemmasScript.sml): lemmas about the While language

[std_logicScript.sml](std_logicScript.sml): definition of standard Hoare logic

[std_logic_soundnessScript.sml](std_logic_soundnessScript.sml): soundness proof of standard Hoare logic

[std_logic_completenessScript.sml](std_logic_completenessScript.sml): completeness proof of standard Hoare logic

[div_logicScript.sml](div_logicScript.sml): definition of Hoare logic for divergence

[div_logic_soundnessScript.sml](div_logic_soundnessScript.sml): soundness proof of Hoare logic for divergence

[div_logic_completenessScript.sml](div_logic_completenessScript.sml): completeness proof of Hoare logic for divergence
