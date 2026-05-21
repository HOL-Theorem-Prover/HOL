## `EXISTS_UNIQUE_CONV`

``` hol4
Conv.EXISTS_UNIQUE_CONV : conv
```

------------------------------------------------------------------------

Expands with the definition of unique existence.

Given a term of the form `"?!x.P[x]"`, the conversion
`EXISTS_UNIQUE_CONV` proves that this assertion is equivalent to the
conjunction of two statements, namely that there exists at least one
value `x` such that `P[x]`, and that there is at most one value `x` for
which `P[x]` holds. The theorem returned is:

``` hol4
   |- (?! x. P[x]) = (?x. P[x]) /\ (!x x'. P[x] /\ P[x'] ==> (x = x'))
```

where `x'` is a primed variant of `x` that does not appear free in the
input term. Note that the quantified variable `x` need not in fact
appear free in the body of the input term. For example,
`EXISTS_UNIQUE_CONV "?!x.T"` returns the theorem:

``` hol4
   |- (?! x. T) = (?x. T) /\ (!x x'. T /\ T ==> (x = x'))
```

### Failure

`EXISTS_UNIQUE_CONV tm` fails if `tm` does not have the form `"?!x.P"`.

### See also

[`Conv.EXISTENCE`](#Conv.EXISTENCE)
