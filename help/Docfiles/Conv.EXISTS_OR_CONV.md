## `EXISTS_OR_CONV`

``` hol4
Conv.EXISTS_OR_CONV : conv
```

------------------------------------------------------------------------

Moves an existential quantification inwards through a disjunction.

When applied to a term of the form `?x. P \/ Q`, the conversion
`EXISTS_OR_CONV` returns the theorem:

``` hol4
   |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)
```

### Failure

Fails if applied to a term not of the form `?x. P \/ Q`.

### See also

[`Conv.OR_EXISTS_CONV`](#Conv.OR_EXISTS_CONV),
[`Conv.LEFT_OR_EXISTS_CONV`](#Conv.LEFT_OR_EXISTS_CONV),
[`Conv.RIGHT_OR_EXISTS_CONV`](#Conv.RIGHT_OR_EXISTS_CONV)
