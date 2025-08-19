## `same_const`

``` hol4
Term.same_const : term -> term -> bool
```

------------------------------------------------------------------------

Constant time equality check for constants.

In many cases, one needs to check that a constant is an instance of the
generic constant originally introduced into the signature, or that two
constants are both type instantiations of another. This can be achieved
by taking the constants apart with `dest_thy_const` and comparing their
name and theory. However, this is relatively inefficient. Instead, one
can invoke `same_const`, which takes constant time.

### Failure

Never fails.

### Example

``` hol4
- same_const boolSyntax.universal (rator (concl BOOL_CASES_AX));

> val it = true : bool
```

### See also

[`Term.aconv`](#Term.aconv),
[`Term.dest_thy_const`](#Term.dest_thy_const),
[`Term.match_term`](#Term.match_term)
