## `all_atoms`

``` hol4
Term.all_atoms : term -> term set
```

------------------------------------------------------------------------

Returns variables and constants occurring in a term.

A call to `all_atoms t` will return the set of all the variables and
constants that appear in a term. The variables include those that occur
under binders, even if only in binding position. Multiple instances of
the same (polymorphic) constant can occur in the result if those
instances are present in the term.

Because bound variables are returned as part of the result,
alpha-equivalent terms will not necessarily give the same results when
`all_atoms` is applied to them.

### Failure

Never fails.

### Example

``` hol4
> HOLset.listItems (all_atoms ``!v. v /\ p``);
val it = [``p``, ``v``, ``$!``, ``$/\``]: term list

> show_types := true;
val it = () : unit

> HOLset.listItems (all_atoms ``!v. v /\ !f. f v``);
val it =
   [``(f :bool -> bool)``, ``(v :bool)``,
    ``($! :(bool -> bool) -> bool)``,
    ``($! :((bool -> bool) -> bool) -> bool)``,
    ``$/\``]: term list

> HOLset.listItems (all_atoms ``!v:'a. T``);
val it =
   [``(v :'a)``, ``($! :('a -> bool) -> bool)``, ``T``]: term list
```

### Comments

There is a companion function `all_atomsl` taking an accumulator, which
has type `term list -> term set -> term set`.

### See also

[`Term.all_vars`](#Term.all_vars)
