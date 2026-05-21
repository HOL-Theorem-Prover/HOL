## `variant`

``` hol4
Term.variant : term list -> term -> term
```

------------------------------------------------------------------------

Modifies a variable name to avoid clashes.

When applied to a list of variables to avoid clashing with, and a
variable to modify, `variant` returns a variant of the variable to
modify, that is, it changes the name as intuitively as possible to make
it distinct from any variables in the list, or any constants. This is
done by adding primes to the name.

The exact form of the variable name should not be relied on, except that
the original variable will be returned unmodified unless it is itself in
the list to avoid clashing with, or if it is the name of a constant.

### Failure

`variant l t` fails if any term in the list `l` is not a variable or if
`t` is not a variable.

### Example

The following shows a couple of typical cases:

``` hol4
   > variant [“y:bool”, “z:bool”] “x:bool”;
   val it = “x” : term

   > variant [“x:bool”, “x':num”, “x'':num”] “x:bool”;
   > val it = “x'''” : term
```

while the following shows that clashes with the names of constants are
also avoided:

``` hol4
   > variant [] (mk_var("T",bool));
   val it = “T'” : term
```

The function `variant` is extremely useful for complicated derived rules
which need to rename variables to avoid free variable capture while
still making the role of the variable obvious to the user.

### Comments

There is a `Term.numvariant` function that has the same type signature,
but which varies by adding and then incrementing a numeric suffix to the
variable's stem.

### See also

[`Term.genvar`](#Term.genvar), [`Term.prim_variant`](#Term.prim_variant)
