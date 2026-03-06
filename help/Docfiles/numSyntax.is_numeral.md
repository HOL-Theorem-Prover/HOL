## `is_numeral`

``` hol4
numSyntax.is_numeral : term -> bool
```

------------------------------------------------------------------------

Check if HOL term is a numeral.

An invocation `is_numeral tm`, where `tm` is a HOL term with the
following form

``` hol4
     <numeral> ::= 0 | NUMERAL <bits>
     <bits>    ::= ZERO | BIT1 (<bits>) | BIT2 (<bits>)
```

returns `true`; otherwise, `false` is returned. The `NUMERAL` constant
is used as a tag signalling that its argument is indeed a numeric
literal. The `ZERO` constant is equal to `0`, and `BIT1(n) = 2*n + 1`
while `BIT2(n) = 2*n + 2`. This representation allows asymptotically
efficient operations on numeric values.

The system prettyprinter will print a numeral as a string of digits.

### Example

``` hol4
- is_numeral ``1234``;
> val it = true : bool
```

### Failure

Fails if `tm` is not in the specified format.

### See also

[`numSyntax.dest_numeral`](#numSyntax.dest_numeral),
[`numSyntax.mk_numeral`](#numSyntax.mk_numeral)
