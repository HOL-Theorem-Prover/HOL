open BasicProvers Defn HolKernel Parse Tactic
     arithmeticTheory boolLib boolSimps bossLib;
open LassieLib arithTacticsLib realTacticsLib logicTacticsLib;

val _ = new_theory "gauss";

val _ = LassieLib.loadJargon "Arithmetic";
val _ = LassieLib.loadJargon "Logic";

Definition sum_def:
  sum (0:num) = 0 ∧
  sum n = n + sum (n-1)
End

Theorem closed_form_sum:
  ∀ n.
    sum n = (n * (n + 1)) DIV 2
Proof
  nltac
    ‘Induction on 'n'.
    use [sum_def] to simplify.
    use [sum_def, GSYM ADD_DIV_ADD_DIV] to simplify.
    '2 * SUC n + n * (n + 1) = SUC n * (SUC n + 1)'
      suffices to show the goal.
    show 'SUC n * (SUC n + 1) = (SUC n + 1) + n * (SUC n + 1)'
      using (simplify with [MULT_CLAUSES]).
    simplify.
    show 'n * (n + 1) = SUC n * n'
      using (trivial using [MULT_CLAUSES, MULT_SYM]).
    '2 * SUC n = SUC n + SUC n' follows trivially.
    'n * (SUC n + 1) = SUC n * n + n' follows trivially.
    rewrite assumptions. simplify.’
QED

val _ = export_theory();
