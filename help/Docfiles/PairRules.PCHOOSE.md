## `PCHOOSE`

``` hol4
PairRules.PCHOOSE : term * thm -> thm -> thm
```

------------------------------------------------------------------------

Eliminates paired existential quantification using deduction from a
particular witness.

When applied to a term-theorem pair `(q,A1 |- ?p. s)` and a second
theorem of the form `A2 u {s[q/p]} |- t`, the inference rule `PCHOOSE`
produces the theorem `A1 u A2 |- t`.

``` hol4
    A1 |- ?p. s   A2 u {s[q/p]} |- t
   ------------------------------------  PCHOOSE ("q",(A1 |- ?q. s))
               A1 u A2 |- t
```

Where no variable in the paired variable structure `q` is free in `A1`,
`A2` or `t`.

### Failure

Fails unless the terms and theorems correspond as indicated above; in
particular `q` must have the same type as the pair existentially
quantified over, and must not contain any variable free in `A1`, `A2` or
`t`.

### See also

[`Thm.CHOOSE`](#Thm.CHOOSE),
[`PairRules.PCHOOSE_TAC`](#PairRules.PCHOOSE_TAC),
[`PairRules.PEXISTS`](#PairRules.PEXISTS),
[`PairRules.PEXISTS_TAC`](#PairRules.PEXISTS_TAC),
[`PairRules.PSELECT_ELIM`](#PairRules.PSELECT_ELIM)
