## `is_let`

``` hol4
boolSyntax.is_let : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a `let`-expression.

If `tm` is a term of the form `LET M N`, then `dest_let tm` returns
`true`. Otherwise, it returns `false`.

### Failure

Never fails.

### Example

``` hol4
- Term `LET f x`;
<<HOL message: inventing new type variable names: 'a, 'b>>
> val it = `LET f x` : term

- is_let it;
> val it = true : bool

- is_let (Term `let x = P /\ Q in x \/ x`);
> val it = true : bool
```

### See also

[`boolSyntax.mk_let`](#boolSyntax.mk_let),
[`boolSyntax.dest_let`](#boolSyntax.dest_let)
