## `STRIP_QUANT_CONV`

``` hol4
Conv.STRIP_QUANT_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion underneath a quantifier prefix.

If `tm` has the form `Q(\v1. ... (Q(\vn.M))...)` and the application of
`conv` to `M` yields `|- M = N`, then `STRIP_QUANT_CONV conv tm` returns
`|- Q(\v1. ... (Q(\vn.M))...) = Q(\v1. ... (Q(\vn.N))...)`, provided `Q`
is Hilbert's choice operator or a universal, existential, or
unique-existence quantifer.

Otherwise, `STRIP_QUANT_CONV conv tm` returns `conv tm`.

### Failure

If `conv M` fails. Or if `conv tm` fails when `tm` is not a quantified
term. Also fails if some of `[v1,...,vn]` are free in the hypotheses of
`conv M`.

### Example

``` hol4
- STRIP_QUANT_CONV (STRIP_QUANT_CONV SYM_CONV)
    (Term `!x y z. ?!p q r. x + y*z = p*q + r`);

> val it =
    |- (!x y z. ?!p q r. x + y * z = p * q + r) =
        !x y z. ?!p q r. p * q + r = x + y * z : thm
```

### Comments

To deal with binders not in the above list, e.g., newly introduced ones,
use `STRIP_BINDER_CONV`.

For deeply nested quantifiers, `STRIP_QUANT_CONV` and
`STRIP_BINDER_CONV` are more efficient than iterated application of
`QUANT_CONV`, `BINDER_CONV`, or `ABS_CONV`.

### See also

[`Conv.STRIP_BINDER_CONV`](#Conv.STRIP_BINDER_CONV),
[`Conv.QUANT_CONV`](#Conv.QUANT_CONV),
[`Conv.BINDER_CONV`](#Conv.BINDER_CONV),
[`Conv.ABS_CONV`](#Conv.ABS_CONV)
