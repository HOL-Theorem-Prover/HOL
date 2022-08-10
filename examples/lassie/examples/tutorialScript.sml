open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic boolTheory
     bossLib arithmeticTheory;
open LassieLib arithTacticsLib logicTacticsLib;

val _ = new_theory "tutorial";

val _ = loadJargon "Arithmetic";
val _ = loadJargon "Logic";

Definition sum_def:
  sum (n:num) = if n = 0 then 0 else sum (n-1) + n
End

Definition sumEq_def:
  sumEq (0:num) = 0 /\
  sumEq n = n + sumEq (n-1)
End

Theorem closed_form_sum:
  ! n. sumEq n = n * (n + 1) DIV 2
Proof
  nltac `Induction on 'n'.`
  \\ nltac `simplify with [sumEq_def].`
  \\ nltac
  `simplify with [sumEq_def, GSYM ADD_DIV_ADD_DIV].`
  \\ nltac `'2 * SUC n + n * (n + 1) = SUC n * (SUC n + 1)'
              suffices to show the goal.`
  \\ nltac
  `show 'SUC n * (SUC n + 1) = (SUC n + 1) + n * (SUC n + 1)'
    using (simplify with [MULT_CLAUSES]).`
  \\ nltac `simplify.`
  \\ nltac `show 'n * (n + 1) = SUC n * n' using (trivial using [MULT_CLAUSES,
           MULT_SYM]).`
  \\ nltac `rewrite assumptions. simplify.`
QED

val _ = export_theory();
