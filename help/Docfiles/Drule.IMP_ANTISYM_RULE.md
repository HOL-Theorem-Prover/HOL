## `IMP_ANTISYM_RULE`

``` hol4
Drule.IMP_ANTISYM_RULE : thm -> thm -> thm
```

------------------------------------------------------------------------

Deduces equality of boolean terms from forward and backward
implications.

When applied to the theorems `A1 |- t1 ==> t2` and `A2 |- t2 ==> t1`,
the inference rule `IMP_ANTISYM_RULE` returns the theorem
`A1 u A2 |- t1 = t2`.

``` hol4
   A1 |- t1 ==> t2     A2 |- t2 ==> t1
  -------------------------------------  IMP_ANTISYM_RULE
           A1 u A2 |- t1 = t2
```

### Failure

Fails unless the theorems supplied are a complementary implicative pair
as indicated above.

### See also

[`Thm.EQ_IMP_RULE`](#Thm.EQ_IMP_RULE), [`Thm.EQ_MP`](#Thm.EQ_MP),
[`Tactic.EQ_TAC`](#Tactic.EQ_TAC)
