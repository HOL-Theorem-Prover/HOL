## `mk_let`

``` hol4
boolSyntax.mk_let : term * term -> term
```

------------------------------------------------------------------------

Constructs a `let` term.

The invocation `mk_let (M,N)` returns the term `` `LET M N` ``. If `M`
is of the form `\x.t` then the result will be pretty-printed as
`let x = N in t`. Since `LET M N` is defined to be `M N`, one can think
of a `let`-expression as a suspended beta-redex (if that helps).

### Failure

Fails if the types of `M` and `N` are such that `LET M N` is not
well-typed, i.e., the type of `M` must be a function type, and the type
of `N` must equal the domain of the type of `M`.

### Example

``` hol4
- mk_let(Term`\x. x \/ x`, Term`Q /\ R`);
> val it = `let x = Q /\ R in x \/ x` : term
```

### Comments

`let` expressions may be nested.

Pairing can also be used in the `let` syntax, provided `pairTheory` has
been loaded. The library `pairLib` provides support for manipulating
'paired' lets.

### See also

[`boolSyntax.dest_let`](#boolSyntax.dest_let),
[`boolSyntax.is_let`](#boolSyntax.is_let),
[`pairSyntax.mk_anylet`](#pairSyntax.mk_anylet)
