## `QUANT_CONV`

``` hol4
Conv.QUANT_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion underneath a quantifier.

If `conv N` returns `A |- N = P`, then `QUANT_CONV conv (M (\v.N))`
returns `A |- M (\v.N) = M (\v.P)`.

### Failure

If `conv N` fails, or if `v` is free in `A`.

### Example

``` hol4
- QUANT_CONV SYM_CONV (Term `!x. x + 0 = x`);
> val it = |- (!x. x + 0 = x) = !x. x = x + 0 : thm
```

### Comments

For deeply nested quantifiers, `STRIP_QUANT_CONV` and
`STRIP_BINDER_CONV` are more efficient than iterated application of
`QUANT_CONV`, `BINDER_CONV`, or `ABS_CONV`.

### See also

[`Conv.BINDER_CONV`](#Conv.BINDER_CONV),
[`Conv.STRIP_QUANT_CONV`](#Conv.STRIP_QUANT_CONV),
[`Conv.STRIP_BINDER_CONV`](#Conv.STRIP_BINDER_CONV),
[`Conv.ABS_CONV`](#Conv.ABS_CONV)
