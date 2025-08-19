## `dest_numeral`

``` hol4
numSyntax.dest_numeral : term -> Arbnum.num
```

------------------------------------------------------------------------

Convert HOL numeral to ML bignum value.

An invocation `dest_numeral tm`, where `tm` is a HOL numeral (a literal
of type `num`), returns the corrresponding ML value of type
`Arbnum.num`. A numeral is a dyadic positional notation described by the
following BNF:

``` hol4
     <numeral> ::= 0 | NUMERAL <bits>
     <bits>    ::= ZERO | BIT1 (<bits>) | BIT2 (<bits>)
```

The `NUMERAL` constant is used as a tag signalling that its argument is
indeed a numeric literal. The `ZERO` constant is equal to `0`, and
`BIT1(n) = 2*n + 1` while `BIT2(n) = 2*n + 2`. This representation
allows asymptotically efficient operations on numeric values.

The system prettyprinter will print a numeral as a string of digits.

### Example

``` hol4
- dest_numeral ``1234``;
> val it = 1234 : num
```

### Failure

Fails if `tm` is not in the specified format.

### See also

[`numSyntax.mk_numeral`](#numSyntax.mk_numeral),
[`numSyntax.is_numeral`](#numSyntax.is_numeral)
