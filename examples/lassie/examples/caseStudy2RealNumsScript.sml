open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib;

open realTheory arithmeticTheory realLib RealArith;

open LassieLib realTacticsLib logicTacticsLib;

val _ = new_theory "caseStudy2RealNums";

val _ = (LassieLib.loadJargon "Reals"; LassieLib.loadJargon "Logic");

Theorem binom1:
  ! (a b:real). (a + b) pow 2 = a pow 2 + 2 * a * b + b pow 2
Proof
  LassieLib.nltac `
    introduce assumptions.
  rewrite with [POW_2, REAL_LDISTRIB, REAL_RDISTRIB].
  rewrite with [<- REAL_ADD_ASSOC].
  simplify with [REAL_EQ_RADD].
  rewrite with [REAL_ADD_ASSOC].
  simplify with [REAL_EQ_LADD]. trivial.`
  (*
  rpt strip_tac
  \\ once_rewrite_tac [POW_2]
  \\ once_rewrite_tac [REAL_LDISTRIB]
  \\ once_rewrite_tac [REAL_RDISTRIB]
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ simp[REAL_EQ_RADD]
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ simp[REAL_EQ_LADD]
  \\ `b * a = a * b` by (fs[REAL_MUL_COMM])
  \\ simp[REAL_DOUBLE, REAL_MUL_ASSOC] *)
QED

Theorem binom2:
  ! (a b:real). (a - b) pow 2 = a pow 2 - 2 * a * b + b pow 2
Proof
  LassieLib.nltac `
    introduce assumptions.
    rewrite with [POW_2, real_sub, REAL_LDISTRIB, REAL_RDISTRIB].
    rewrite with [<- REAL_ADD_ASSOC].
    simplify with [REAL_EQ_RADD].
    rewrite once [REAL_NEG_MUL2].
    rewrite with [REAL_ADD_ASSOC].
    simplify with [REAL_EQ_LADD]. trivial.`
  (*
  rpt strip_tac
  \\ once_rewrite_tac [POW_2]
  \\ once_rewrite_tac [real_sub]
  \\ once_rewrite_tac [REAL_LDISTRIB]
  \\ once_rewrite_tac [REAL_RDISTRIB]
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ once_rewrite_tac [REAL_NEG_MUL2]
  \\ simp[REAL_EQ_RADD]
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ simp[REAL_EQ_LADD]
  \\ `-b * a = a * -b` by (fs[REAL_MUL_COMM])
  \\ simp[REAL_DOUBLE, GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL, REAL_MUL_ASSOC] *)
QED

Definition sum_of_cubes_def:
  (sum_of_cubes 0 = 0:real) /\
  (sum_of_cubes (SUC n) = (&(SUC n)) pow 3 + sum_of_cubes n)
End

Definition sum_def:
  (sum 0 = 0:real) /\
  (sum (SUC n) = (&(SUC n) + sum n))
End

Theorem closed_form_sum:
  ! n. (sum n = (((&n):real) * (1 + &n)) / 2)
Proof
  LassieLib.nltac ‘
    induction on 'n'. simplify with [sum_def, REAL_DIV_LZERO, MULT].
    rewrite MULT_SYM for 'n'.
    we show 'SUC n + 1 = SUC (SUC n)' using (simplify).
    rewrite last assumption.
    we show 'SUC (SUC n) * n = n + n + n * n' using (simplify with [MULT]).
    rewrite last assumption.
    we show 'n + n + n * n + 1 = SUC n + n * (n + 1)' using
      (simplify with [ADD1, LEFT_ADD_DISTRIB, MULT_RIGHT_1]).
    rewrite last assumption.
    rewrite with [ADD_ASSOC].
    we show 'SUC n + SUC n = 2 * (SUC n)' using (simplify).
    rewrite last assumption.
    rewrite once [MULT_COMM].
    rewrite with [GSYM REAL_MUL, GSYM REAL_ADD, GSYM REAL_DIV_ADD].
    rewrite with [real_div].
    simplify with [GSYM REAL_MUL_ASSOC, REAL_MUL_RINV].
    simplify with [REAL_MUL_ASSOC].’
  (* Induct_on `n`
  \\ fs[sum_def, REAL_DIV_LZERO]
  \\ pop_assum (fn thm=> once_rewrite_tac [GSYM thm] \\ assume_tac thm)
  \\ fs[MULT]
  \\ qspec_then `n` (fn thm => once_rewrite_tac [thm]) MULT_SYM
  \\ `SUC n + 1 = SUC (SUC n)`
      by (pop_assum kall_tac \\ Induct_on `n` \\ fs[])
  \\ qpat_x_assum `SUC n + 1 = _` (fn thm => once_rewrite_tac [thm])
  \\ `SUC (SUC n) * n = n + n + n * n`
      by (fs[MULT])
  \\ qpat_x_assum `SUC (SUC n) * _ = _` (fn thm => once_rewrite_tac [thm])
  \\ `n + n + n * n + 1 = SUC n + n * (n + 1)`
      by (once_rewrite_tac [ADD1] \\ once_rewrite_tac [LEFT_ADD_DISTRIB]
          \\ rewrite_tac [ADD_ASSOC, MULT_RIGHT_1] \\ fs[])
  \\ qpat_x_assum `n + n + _ + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ rewrite_tac [ADD_ASSOC]
  \\ `SUC n + SUC n = 2 * (SUC n)`
      by (fs[])
  \\ qpat_x_assum `SUC n + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM REAL_MUL, GSYM REAL_ADD]
  \\ rewrite_tac [GSYM REAL_DIV_ADD]
  \\ rewrite_tac [real_div]
  \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
  \\ fs[REAL_MUL_RINV]
  \\ fs[REAL_MUL_ASSOC] *)
QED

Theorem pow_3:
  n pow 3 = n * n * n
Proof
  LassieLib.nltac `
    we show '3 = SUC 2' using (simplify).
    rewrite last assumption. simplify with [pow, POW_2]. trivial.`
  (*
  `3 = SUC 2` by (fs[])
  \\ pop_assum rw_th
  \\ fs[pow, POW_2] \\ REAL_ASM_ARITH_TAC *)
QED

(**
  The sum of cubed numbers up to n is the squared sum
**)
Theorem sum_of_cubes_is_squared_sum:
  ! n. sum_of_cubes n = (sum n) pow 2
Proof
  LassieLib.nltac ‘
    induction on 'n'.
    simplify conclusion with [sum_of_cubes_def, sum_def].
    rewrite with [POW_2, REAL_LDISTRIB, REAL_RDISTRIB, REAL_ADD_ASSOC].
    showing '&SUC n pow 3 = &SUC n * &SUC n + &SUC n * sum n + sum n * &SUC n'
      closes the proof because (simplify conclusion with [REAL_EQ_LADD]).
    we know '& SUC n * sum n + sum n * &SUC n = 2 * (sum n * & SUC n)'.
    rewrite once [<- REAL_ADD_ASSOC].
    rewrite last assumption.
    rewrite with [pow_3, closed_form_sum, real_div, REAL_MUL_ASSOC].
    we know '2 * &n * (1 + &n) * inv 2 = 2 * inv 2 * & n * (1 + &n)'.
    rewrite last assumption.
    simplify conclusion with [REAL_MUL_RINV].
    we show 'n + 1 = SUC n' using (simplify conclusion).
    rewrite last assumption. simplify conclusion.
    we show '2 = (SUC (SUC 0))' using (simplify conclusion).
    rewrite last assumption. rewrite last assumption.
    rewrite with [EXP].
    we show 'SUC n = n + 1' using (simplify conclusion).
    rewrite last assumption.
    rewrite with [GSYM REAL_OF_NUM_ADD, pow_3].
    rewrite with [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, MULT_RIGHT_1,
                  RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_LEFT_1].
    simplify.’
QED

(*
Induct_on ‘n’ \\ simp [sum_of_cubes_def, sum_def, ]
    \\ fs[pow_3]
    \\ once_rewrite_tac [REAL_ADD_ASSOC]
    \\ pop_assum rw_th
    \\ once_rewrite_tac [closed_form_sum]
    \\ once_rewrite_tac [real_div]
    \\ rewrite_tac [REAL_MUL_ASSOC]
    \\ `2 * &n * (1 + &n) * inv 2 = 2 * inv 2 * & n * (1 + &n)` by (REAL_ASM_ARITH_TAC)
    \\ pop_assum rw_th
    \\ simp [REAL_MUL_RINV]
    \\ `(SUC n) ** 3 = (SUC n)**2 + (SUC n)**2 * n`
        by (`3= SUC (SUC (SUC 0))` by (fs[]) \\ pop_assum rw_th
            \\ `2 = SUC(SUC 0)` by (fs[]) \\ pop_assum rw_th
            \\ rewrite_tac[EXP]
            \\ `SUC n = n + 1` by (fs[])
            \\ pop_assum rw_th
            \\ rewrite_tac [MULT_RIGHT_1, RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_LEFT_1]
            \\ fs[])
    \\ pop_assum rw_th
    \\ `n + 1 = SUC n` by (fs[])
    \\ pop_assum rw_th \\ fs[]
QED
  *)

val _ = export_theory();
