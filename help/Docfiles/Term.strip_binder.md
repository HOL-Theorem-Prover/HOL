## `strip_binder`

``` hol4
Term.strip_binder : term option -> term -> term list * term
```

------------------------------------------------------------------------

Break apart consecutive binders.

An application `strip_binder (SOME c) (c(\v1. ... (c(\vn.M))...))`
returns `([v1,...,vn],M)`. The constant `c` should represent a term
binding operation.

An application `strip_binder NONE (\v1...vn. M)` returns
`([v1,...,vn],M)`.

### Failure

Never fails.

### Example

`strip_abs` could be defined as follows.

``` hol4
   - val strip_abs = strip_binder NONE;
   > val strip_abs = fn : term -> term list * term

   - strip_abs (Term `\x y z. x /\ y ==> z`);
   > val it = ([`x`, `y`, `z`], `x /\ y ==> z`) : term list * term
```

Defining `strip_forall` is similar.

``` hol4
   strip_binder (SOME boolSyntax.universal)
```

### Comments

Terms with many consecutive binders should be taken apart using
`strip_binder` and its instantiations `strip_abs`, `strip_forall`, and
`strip_exists`. In the current implementation of HOL, iterating
`dest_abs`, `dest_forall`, or `dest_exists` is far slower for terms with
many consecutive binders.

### See also

[`Term.list_mk_binder`](#Term.list_mk_binder),
[`Term.strip_abs`](#Term.strip_abs),
[`boolSyntax.strip_forall`](#boolSyntax.strip_forall),
[`boolSyntax.strip_exists`](#boolSyntax.strip_exists)
