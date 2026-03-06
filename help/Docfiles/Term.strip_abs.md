## `strip_abs`

``` hol4
Term.strip_abs : term -> term list * term
```

------------------------------------------------------------------------

Break apart consecutive lambda abstractions.

If M is a term of the form `\v1...vn.N`, where `N` is not a lambda
abstraction, then `strip_abs M` equals `([v1,...,vn],N)`. Otherwise, the
result is `([],M)`.

### Failure

Never fails.

### Example

``` hol4
- strip_abs (Term `\x y z. x ==> y ==> z`);
> val it = ([`x`, `y`, `z`], `x ==> y ==> z`) : term list * term

- strip_abs T;
> val it = ([], `T`) : term list * term
```

### Comments

In the current implementation of HOL, `strip_abs` is far faster than
iterating `dest_abs` for terms with many consecutive binders.

### See also

[`Term.strip_binder`](#Term.strip_binder),
[`Term.dest_abs`](#Term.dest_abs),
[`boolSyntax.strip_forall`](#boolSyntax.strip_forall),
[`boolSyntax.strip_exists`](#boolSyntax.strip_exists)
