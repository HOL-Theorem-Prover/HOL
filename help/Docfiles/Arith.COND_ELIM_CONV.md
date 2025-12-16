## `COND_ELIM_CONV`

``` hol4
Arith.COND_ELIM_CONV : conv
```

------------------------------------------------------------------------

Eliminates conditional statements from a formula.

This function moves conditional statements up through a term and if at
any point the branches of the conditional become Boolean-valued the
conditional is eliminated. If the term is a formula, only an abstraction
can prevent a conditional being moved up far enough to be eliminated.

### Failure

Never fails.

### Example

``` hol4
#COND_ELIM_CONV "!f n. f ((SUC n = 0) => 0 | (SUC n - 1)) < (f n) + 1";;
|- (!f n. (f((SUC n = 0) => 0 | (SUC n) - 1)) < ((f n) + 1)) =
   (!f n.
     (~(SUC n = 0) \/ (f 0) < ((f n) + 1)) /\
     ((SUC n = 0) \/ (f((SUC n) - 1)) < ((f n) + 1)))

#COND_ELIM_CONV "!f n. (\m. f ((m = 0) => 0 | (m - 1))) (SUC n) < (f n) + 1";;
|- (!f n. ((\m. f((m = 0) => 0 | m - 1))(SUC n)) < ((f n) + 1)) =
   (!f n. ((\m. ((m = 0) => f 0 | f(m - 1)))(SUC n)) < ((f n) + 1))
```

Useful as a preprocessor to decision procedures which do not allow
conditional statements in their argument formula.

### See also

[`Arith.SUB_AND_COND_ELIM_CONV`](#Arith.SUB_AND_COND_ELIM_CONV)
