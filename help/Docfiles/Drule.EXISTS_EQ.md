## `EXISTS_EQ`

``` hol4
Drule.EXISTS_EQ : (term -> thm -> thm)
```

------------------------------------------------------------------------

Existentially quantifies both sides of an equational theorem.

When applied to a variable `x` and a theorem whose conclusion is
equational, `A |- t1 = t2`, the inference rule `EXISTS_EQ` returns the
theorem `A |- (?x. t1) = (?x. t2)`, provided the variable `x` is not
free in any of the assumptions.

``` hol4
         A |- t1 = t2
   ------------------------  EXISTS_EQ "x"      [where x is not free in A]
    A |- (?x.t1) = (?x.t2)
```

### Failure

Fails unless the theorem is equational with both sides having type
`bool`, or if the term is not a variable, or if the variable to be
quantified over is free in any of the assumptions.

### See also

[`Thm.AP_TERM`](#Thm.AP_TERM), [`Drule.EXISTS_IMP`](#Drule.EXISTS_IMP),
[`Drule.FORALL_EQ`](#Drule.FORALL_EQ),
[`Drule.MK_EXISTS`](#Drule.MK_EXISTS),
[`Drule.SELECT_EQ`](#Drule.SELECT_EQ)
