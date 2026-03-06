## `underAIs`

``` hol4
Drule.underAIs : (thm -> thm) -> (thm -> thm)
```

------------------------------------------------------------------------

Applies a derived rule underneath external "guarding" of universal
variables and implications.

A call to `underAIs f th` strips away external guarding in `th`, applies
the function `f`, and then restores the original guarding. In this
context, "guarding" is the presence of universal quantifications and
antecedents in implications. Thus, this function sees the theorem
`∀x. p x ==> ∀y. q y ∧ r x y ==> s` as the body `s`, guarded by the
universal variables `x` and `y` and the assumptions `p x` and
`q y ∧ r x y`. Negations in the body are not viewed as implications.

### Failure

As all theorems are of this shape, the stripping and restoration of
guarding always succeeds. However, this function will fail if `f` fails
when applied to the theorem `A' |- s`, with `s` the body (as above), and
`A'` the original hypotheses of theorem augmented with the antecendents
of guarding implications.

### Example

``` hol4
> underAIs (EXISTS (“∃m. (k * n) MOD m = 0”, “n:num”))
           arithmeticTheory.MOD_EQ_0;
val it = ⊢ ∀n. 0 < n ⇒ ∀k. ∃m. (k * n) MOD m = 0: thm
```

### See also

[`Drule.cj`](#Drule.cj), [`Drule.iffLR`](#Drule.iffLR)
