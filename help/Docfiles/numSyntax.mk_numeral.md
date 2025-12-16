## `mk_numeral`

``` hol4
numSyntax.mk_numeral : Arbnum.num -> term
```

------------------------------------------------------------------------

Convert ML bignum value to HOL numeral.

An invocation `mk_numeral n`, where `n` is an ML value of type
`Arbnum.num` returns the corrresponding HOL term.

### Example

``` hol4
- Arbnum.fromString "1234";
> val it = 1234 : num

- mk_numeral it;
> val it = ``1234`` : term
```

### Failure

Never fails.

### See also

[`numSyntax.dest_numeral`](#numSyntax.dest_numeral),
[`numSyntax.is_numeral`](#numSyntax.is_numeral)
