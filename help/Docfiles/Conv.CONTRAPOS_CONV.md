## `CONTRAPOS_CONV`

``` hol4
Conv.CONTRAPOS_CONV : conv
```

------------------------------------------------------------------------

Proves the equivalence of an implication and its contrapositive.

When applied to an implication `P ==> Q`, the conversion
`CONTRAPOS_CONV` returns the theorem:

``` hol4
   |- (P ==> Q) = (~Q ==> ~P)
```

### Failure

Fails if applied to a term that is not an implication.

### See also

[`Drule.CONTRAPOS`](#Drule.CONTRAPOS)
