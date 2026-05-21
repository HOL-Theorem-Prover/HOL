## `aconv`

``` hol4
Term.aconv : term -> term -> bool
```

------------------------------------------------------------------------

Tests for alpha-convertibility of terms.

When applied to two terms, `aconv` returns `true` if they are
alpha-convertible, and `false` otherwise. Two terms are
alpha-convertible if they differ only in the way that names have been
given to bound variables.

### Failure

Never fails.

### Example

``` hol4
- aconv (Term `?x y. x /\ y`) (Term `?y x. y /\ x`)
> val it = true : bool
```

### See also

[`Thm.ALPHA`](#Thm.ALPHA), [`Drule.ALPHA_CONV`](#Drule.ALPHA_CONV)
