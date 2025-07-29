## `mk_ucomb`

``` hol4
boolSyntax.mk_ucomb : term * term -> term
```

------------------------------------------------------------------------

Forms an application term, possibly instantiating both the function and
the argument types.

A call to `mk_ucomb(f,x)` checks to see if the term `f` (which must have
a function type) can have its type variables instantiated to make the
domain of the function match some instantiation of the type of `x`. If
so, then the call returns the application of the instantiated `f` to the
instantiated `x`.

### Failure

Fails if there is no way to instantiate the types to make the function
domain match the argument type.

### Example

Note how both the FOLDR combinator and the argument (the K combinator)
have type variables invented for them when the two quotations are
parsed.

``` hol4
   - val t = mk_ucomb(``FOLDR``, ``K``);
  <<HOL message: inventing new type variable names: 'a, 'b>>
  <<HOL message: inventing new type variable names: 'a, 'b>>
   > val t = ``FOLDR K`` : term
```

The resulting term `t` has only the type variable `:'a` left after
instantiation.

``` hol4
   - type_of t;
   > val it = ``:'a -> 'a list -> 'a`` : hol_type
```

This term can now be combined with an argument and the final type
variable instantiated:

``` hol4
   - mk_ucomb(t, ``T``);
   > val it = ``FOLDR K T`` : term

   - type_of it;
   > val it = ``:bool list -> bool``;
```

Attempting to use `mk_icomb` in the first example above results in
immediate error because it can only instantiate the function type:

``` hol4
   - mk_icomb(``FOLDR``, ``K``) handle e => Raise e;
   <<HOL message: inventing new type variable names: 'a, 'b>>
   <<HOL message: inventing new type variable names: 'a, 'b>>

   Exception raised at HolKernel.list_mk_icomb:
   double bind on type variable 'b
   Exception-
      HOL_ERR
        {message = "double bind on type variable 'b", origin_function =
         "list_mk_icomb", origin_structure = "HolKernel"} raised
```

However it can be used in the second example, as only the function type
requires instantiation:

``` hol4
   - mk_icomb(t, ``T``);
   > val it = ``FOLDR K T`` : term
```

### Comments

`mk_ucomb` makes use of `sep_type_unify`.

### See also

[`boolSyntax.list_mk_ucomb`](#boolSyntax.list_mk_ucomb),
[`boolSyntax.sep_type_unify`](#boolSyntax.sep_type_unify),
[`Term.mk_icomb`](#Term.mk_icomb), [`Term.mk_comb`](#Term.mk_comb)
