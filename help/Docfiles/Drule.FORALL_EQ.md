## `FORALL_EQ`

``` hol4
Drule.FORALL_EQ : (term -> thm -> thm)
```

------------------------------------------------------------------------

Universally quantifies both sides of an equational theorem.

When applied to a variable `x` and a theorem `A |- t1 = t2`, whose
conclusion is an equation between boolean terms, `FORALL_EQ` returns the
theorem `A |- (!x. t1) = (!x. t2)`, unless the variable `x` is free in
any of the assumptions.

``` hol4
         A |- t1 = t2
   ------------------------  FORALL_EQ "x"      [where x is not free in A]
    A |- (!x.t1) = (!x.t2)
```

### Failure

Fails if the theorem is not an equation between boolean terms, or if the
supplied term is not simply a variable, or if the variable is free in
any of the assumptions.

### See also

[`Thm.AP_TERM`](#Thm.AP_TERM), [`Drule.EXISTS_EQ`](#Drule.EXISTS_EQ),
[`Drule.SELECT_EQ`](#Drule.SELECT_EQ)
