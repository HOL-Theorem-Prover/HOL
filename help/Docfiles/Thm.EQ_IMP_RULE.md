## `EQ_IMP_RULE`

``` hol4
Thm.EQ_IMP_RULE : thm -> thm * thm
```

------------------------------------------------------------------------

Derives forward and backward implication from equality of boolean terms.

When applied to a theorem `A |- t1 = t2`, where `t1` and `t2` both have
type `bool`, the inference rule `EQ_IMP_RULE` returns the theorems
`A |- t1 ==> t2` and `A |- t2 ==> t1`.

``` hol4
              A |- t1 = t2
   -----------------------------------  EQ_IMP_RULE
    A |- t1 ==> t2     A |- t2 ==> t1
```

### Failure

Fails unless the conclusion of the given theorem is an equation between
boolean terms.

### See also

[`Thm.EQ_MP`](#Thm.EQ_MP), [`Tactic.EQ_TAC`](#Tactic.EQ_TAC),
[`Drule.IMP_ANTISYM_RULE`](#Drule.IMP_ANTISYM_RULE)
