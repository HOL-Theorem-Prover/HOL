## `mk_bool_case`

``` hol4
boolSyntax.mk_bool_case : term * term * term -> term
```

------------------------------------------------------------------------

Constructs a case expression over `bool`.

`mk_bool_case M1 M2 b` returns `bool_case M1 M2 b`. The prettyprinter
displays this as `case b of T -> M1 || F -> M2`. The `bool_case`
constant may be thought of as a pattern-matching version of the
conditional.

### Failure

Fails if `b` is not of type `bool`. Also fails if `M1` and `M2` do not
have the same type.

### Example

``` hol4
- mk_bool_case (Term`f x`,Term`b:'b`,Term`x:bool`);
<<HOL message: inventing new type variable names: 'a, 'b>>

> val it = `case x of T -> f x || F -> b` : term
```

### See also

[`boolSyntax.dest_bool_case`](#boolSyntax.dest_bool_case),
[`boolSyntax.is_bool_case`](#boolSyntax.is_bool_case)
