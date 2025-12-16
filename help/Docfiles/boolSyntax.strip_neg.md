## `strip_neg`

``` hol4
boolSyntax.strip_neg : term -> term * int
```

------------------------------------------------------------------------

Breaks iterated negations down to an unnegated core.

If `M` is of the form `~...~t`, then `strip_neg M` returns `(t,n)`,
where `n` is the number of consecutive negations being applied to `t`.

### Failure

Never fails.

### Example

``` hol4
- strip_neg (Term `~~~~t`);
> val it = (`t`, 4) : term * int

- strip_neg (Term `x`);
<<HOL message: inventing new type variable names: 'a>>
> val it = (`x`, 0) : term * int
```

### Comments

There is no corresponding entrypoint for building iterated negations. If
such functionality is desired, `funpow` may be used:

``` hol4
    - funpow 3 mk_neg T;
    > val it = `~~~T` : term
```

### See also

[`boolSyntax.dest_neg`](#boolSyntax.dest_neg),
[`boolSyntax.mk_neg`](#boolSyntax.mk_neg), [`Lib.funpow`](#Lib.funpow)
