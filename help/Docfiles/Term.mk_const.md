## `mk_const`

``` hol4
Term.mk_const : string * hol_type -> term
```

------------------------------------------------------------------------

Constructs a constant.

If `n` is a string that has been previously declared to be a constant
with type `ty` and `ty1` is an instance of `ty`, then `mk_const(n,ty1)`
returns the specified instance of the constant.

(A type `ty1` is an 'instance' of a type `ty2` when `match_type ty2 ty1`
does not fail.)

Note, however, that constants with the same name (and type) may be
declared in different theories. If two theories having constants with
the same name `n` are in the ancestry of the current theory, then
`mk_const(n,ty)` will issue a warning before arbitrarily selecting which
constant to construct. In such situations, `mk_thy_const` allows one to
specify exactly which constant to use.

### Failure

Fails if `n` is not the name of a known constant, or if `ty` is not an
instance of the type that the constant has in the signature.

### Example

``` hol4
   - mk_const ("T", “:bool”);
   > val it = `T` : term

   - mk_const ("=", “:bool -> bool -> bool”);
   > val it = `$=` : term

   - try mk_const ("test", “:bool”);
   Exception raised at Term.mk_const:
   test not found
```

The following example shows a new constant being introduced that has the
same name as the standard equality of HOL. Then we attempt to make an
instance of that constant.

``` hol4
   - new_constant ("=", “:bool -> bool -> bool”);
   > val it = () : unit

   - mk_const("=", “:bool -> bool -> bool”);
   <<HOL warning: Term.mk_const: "=": more than one possibility>>

   > val it = `$=` : term
```

### See also

[`Term.mk_thy_const`](#Term.mk_thy_const),
[`Term.dest_const`](#Term.dest_const),
[`Term.is_const`](#Term.is_const), [`Term.mk_var`](#Term.mk_var),
[`Term.mk_comb`](#Term.mk_comb), [`Term.mk_abs`](#Term.mk_abs),
[`Type.match_type`](#Type.match_type)
