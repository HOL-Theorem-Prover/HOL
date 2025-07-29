## `dest_let`

``` hol4
boolSyntax.dest_let : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a let-expression.

If `M` is a term of the form `LET M N`, then `dest_let M` returns
`(M,N)`.

### Example

``` hol4
- dest_let (Term `let x = P /\ Q in x \/ x`);
> val it = (`\x. x \/ x`, `P /\ Q`) : term * term
```

### Failure

Fails if `M` is not of the form `LET M N`.

### See also

[`boolSyntax.mk_let`](#boolSyntax.mk_let),
[`boolSyntax.is_let`](#boolSyntax.is_let)
