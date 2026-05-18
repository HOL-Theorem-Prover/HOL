# A Verified Cost Model for Call-By-Push-Value (𝜆-Calculus) (by Zhuo Zoey Chen et al.)

## Important definitions and theorems

- Figure 1 The rules defining big-step semantics of CBPV terms with time cost: timeBS from CBPV_Mutual_RecursiveScript.sml
- Figure 2 The rules defining big-step semantics of CBPV terms with space cost: spaceBS from CBPV_Mutual_RecursiveScript.sml
- Figure 3 Transition Rules for the Substitution Machine: subst_step from SubstMachineScript.sml
- Figure 4 Transition Rules for the Heap Machine: heap_step from HeapMachineScript.sml
- Figure 5 Unfolding rules: unfoldsVal from HeapMachineScript.sml
- Definition 3 Size of Tokens and Programs: sizeT and sizeP from ProgramScript.sml and ProgramHeapScript.sml
- Definition 4 Compilation Function for Substitution Machine: compileVal_def from ProgramScript.sml
- Definition 5 Compilation Function for Heap Machine: compileVal_def from ProgramHeapScript.sml
- Lemma 6 (Program Size Bounds). sizeP_size from ProgramScript.sml and ProgramHeapScript.sml
- Definition 7 (Program-Term Correspondence). Not explicitly defined in formalisation. 
- Definition 8 (Extraction Function). jump* theorems (e.g. jumpTarget)from ProgramScript.sml and ProgramHeapScript.sml
- Lemma 9 (Substitution Machine Time Simulation). subst_big_step_correct_n from SubstMachineScript.sml
- Lemma 10 (Substitution Machine Space Simulation). subst_big_step_correctSpace from SubstMachineScript.sml
- Definition 11 (Closure). clos from HeapMachineScript.sml
- Definition 12 (Heap). Heap from HeapMachineScript.sml
- Definition 13 (put and lookup). put and lookup from HeapMachineScript.sml
- Definition 14 (Closure-Term Correspondence with Heap). reprCVal from HeapMachineScript.sml
- Lemma 15 (Heap Machine Time Simulation). correctTime from HeapMachineScript.sml
- Lemma 16 (Heap Machine Space Simulation). correctSpace from HeapMachineScript.sml
- Lemma 19. If s is bounded by k, then (s, a| H) ⇝k s. unfolds_bound from HeapMachineScript.sml
- Compilation function γ is injective: compileVal_injective from ProgramScript.sml and ProgramHeapScript.sml
