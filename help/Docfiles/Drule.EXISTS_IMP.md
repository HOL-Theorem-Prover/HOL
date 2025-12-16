## `EXISTS_IMP`

``` hol4
Drule.EXISTS_IMP : (term -> thm -> thm)
```

------------------------------------------------------------------------

Existentially quantifies both the antecedent and consequent of an
implication.

When applied to a variable `x` and a theorem `A |- t1 ==> t2`, the
inference rule `EXISTS_IMP` returns the theorem
`A |- (?x. t1) ==> (?x. t2)`, provided `x` is not free in the
assumptions.

``` hol4
         A |- t1 ==> t2
   --------------------------  EXISTS_IMP "x"   [where x is not free in A]
    A |- (?x.t1) ==> (?x.t2)
```

### Failure

Fails if the theorem is not implicative, or if the term is not a
variable, or if the term is a variable but is free in the assumption
list.

### See also

[`Drule.EXISTS_EQ`](#Drule.EXISTS_EQ)
