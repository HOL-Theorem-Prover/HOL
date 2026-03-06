## `OR_EXISTS_CONV`

``` hol4
Conv.OR_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves an existential quantification outwards through a disjunction.

When applied to a term of the form `(?x.P) \/ (?x.Q)`, the conversion
`OR_EXISTS_CONV` returns the theorem:

``` hol4
   |- (?x.P) \/ (?x.Q) = (?x. P \/ Q)
```

### Failure

Fails if applied to a term not of the form `(?x.P) \/ (?x.Q)`.

### See also

[`Conv.EXISTS_OR_CONV`](#Conv.EXISTS_OR_CONV),
[`Conv.LEFT_OR_EXISTS_CONV`](#Conv.LEFT_OR_EXISTS_CONV),
[`Conv.RIGHT_OR_EXISTS_CONV`](#Conv.RIGHT_OR_EXISTS_CONV)
