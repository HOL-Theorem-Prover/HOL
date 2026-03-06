## `TRANS_TAC`

``` hol4
Tactic.TRANS_TAC : thm -> term -> tactic
```

------------------------------------------------------------------------

Applies transitivity theorem to goal with chosen intermediate term.

When applied to a 'transitivity' theorem, i.e. one of the form

``` hol4
   |- !xs. R1 x y /\ R2 y z ==> R3 x z
```

and a term `t`, `TRANS_TAC` produces a tactic that reduces a goal with
conclusion of the form `R3 s u` to one with conclusion
`R1 s t /\ R2 t u`.

``` hol4
       A ?- R3 s u
  ======================== TRANS_TAC (|- !xs. R1 x y /\ R2 y z ==> R3 x z) `t`
   A ?- R1 s t /\ R2 t u
```

### Example

Consider the simple inequality goal:

``` hol4
  > g `n < (m + 2) * (n + 1)`;
```

We can use the following transitivity theorem

``` hol4
  > LESS_EQ_LESS_TRANS;
  val it = |- !m n p. m <= n /\ n < p ==> m < p: thm


  # e (TRANS_TAC LESS_EQ_LESS_TRANS ``1 * (n + 1)``);
  OK..
  1 subgoal:
  val it =
   
   n <= 1 * (n + 1) /\ 1 * (n + 1) < (m + 2) * (n + 1)
   
   : proof
```

### Failure

Fails unless the input theorem is of the expected form (some of the
relations `R1`, `R2` and `R3` may be, and often are, the same) and the
conclusion matches the goal, in the usual sense of higher-order
matching.

### Comments

The effect of `TRANS_TAC th t` can often be replicated by the more
primitive tactic sequence `MATCH_MP_TAC th THEN EXISTS_TAC t`. The use
of `TRANS_TAC` is not only less verbose, but it is also more general in
that it ensures correct type-instantiation of the theorem, whereas in
highly polymorphic theorems the use of `MATCH_MP_TAC` may leave the
wrong types for the subsequent `EXISTS_TAC` step.

If `R1 x y`, etc. are actually overloads of negated terms, e.g.,
`~(R1' y x)`, `TRANS_TAC` can still work. Such overloads are common for
many definitions of "less" as an overload of "not less-or-equal",
i.e. `x < y` is an overload of `~(y <= x)`.

### See also

[`MATCH_MP_TAC`](#MATCH_MP_TAC), [`TRANS`](#TRANS)
