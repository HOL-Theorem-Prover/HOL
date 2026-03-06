## `PEXISTS_UNIQUE_CONV`

``` hol4
PairRules.PEXISTS_UNIQUE_CONV : conv
```

------------------------------------------------------------------------

Expands with the definition of paired unique existence.

Given a term of the form `"?!p. t[p]"`, the conversion
`PEXISTS_UNIQUE_CONV` proves that this assertion is equivalent to the
conjunction of two statements, namely that there exists at least one
pair `p` such that `t[p]`, and that there is at most one value `p` for
which `t[p]` holds. The theorem returned is:

``` hol4
   |- (?!p. t[p]) = (?p. t[p]) /\ (!p p'. t[p] /\ t[p'] ==> (p = p'))
```

where `p'` is a primed variant of the pair `p` none of the components of
which appear free in the input term. Note that the quantified pair `p`
need not in fact appear free in the body of the input term. For example,
`PEXISTS_UNIQUE_CONV "?!(x,y). T"` returns the theorem:

``` hol4
   |- (?!(x,y). T) =
      (?(x,y). T) /\ (!(x,y) (x',y'). T /\ T ==> ((x,y) = (x',y')))
```

### Failure

`PEXISTS_UNIQUE_CONV tm` fails if `tm` does not have the form `"?!p.t"`.

### See also

[`Conv.EXISTS_UNIQUE_CONV`](#Conv.EXISTS_UNIQUE_CONV),
[`PairRules.PEXISTENCE`](#PairRules.PEXISTENCE)
