## `mk_icomb`

``` hol4
boolSyntax.mk_icomb : term * term -> term
```

------------------------------------------------------------------------

Forms an application term, possibly instantiating the function.

A call to `mk_icomb(f,x)` checks to see if the term `f`, which must have
function type, can have any of its type variables instantiated so as to
make the domain of the function match the type of `x`. If so, then the
call returns the application of the instantiated `f` to `x`.

### Failure

Fails if there is no way to instantiate the function term to make its
domain match the argument's type.

### Example

Note how both the S combinator and the argument have type variables
invented for them when the two quotations are parsed.

``` hol4
   - val t = mk_icomb(``S``, ``\n:num b. (n,b)``);
  <<HOL message: inventing new type variable names: 'a, 'b, 'c>>
  <<HOL message: inventing new type variable names: 'a>>
   > val t = ``S (\n b. (n,b))`` : term
```

The resulting term `t` has only the type variable `:'a` left after
instantiation.

``` hol4
   - type_of t;
   > val it = ``:(num -> 'a) -> num -> num # 'a`` : hol_type
```

This term can now be combined with an argument and the final type
variable instantiated:

``` hol4
   - mk_icomb(t, ``ODD``);
   > val it = ``S (\n b. (n,b)) ODD`` : term

   - type_of it;
   > val it = ``:num -> num # bool``;
```

Attempting to use `mk_comb` above results in immediate error because it
requires domain and arguments types to be identical:

``` hol4
   - mk_comb(``S``, ``\n:num b. (n,b)``) handle e => Raise e;
   <<HOL message: inventing new type variable names: 'a, 'b, 'c>>
   <<HOL message: inventing new type variable names: 'a>>

   Exception raised at Term.mk_comb:
   incompatible types
   ! Uncaught exception:
   ! HOL_ERR
```

### See also

[`boolSyntax.list_mk_icomb`](#boolSyntax.list_mk_icomb),
[`Term.mk_comb`](#Term.mk_comb)
