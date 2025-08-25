## `RENAME_VARS_CONV`

``` hol4
Conv.RENAME_VARS_CONV : string list -> conv
```

------------------------------------------------------------------------

Renames variables underneath a binder.

`RENAME_VARS_CONV` takes a list of strings specifying new names for
variables under a binder. More precisely, it will rename variables in
abstractions, or bound by universal, existential, unique existence or
the select (or Hilbert-choice) "quantifier".

More than one variable can be renamed at once. If variables occur past
the first, then the renaming continues on the appropriate sub-term of
the first. (That is, if the term is an abstraction, then renaming will
continue on the body of the abstraction. If it is one of the supported
quantifiers, then renaming will continue on the body of the abstraction
that is the argument of the "binder constant".)

If `RENAME_VARS_CONV` is passed the empty list, it is equivalent to
`ALL_CONV`. The binders do not need to be of the same type all the way
into the term.

### Failure

Fails if an attempt is made to rename a variable in a term that is not
an abstraction, or is not one of the accepted quantifiers. Also fails if
all of the names in the list are not distinct.

### Example

``` hol4
- RENAME_VARS_CONV ["a", "b"] ``\x y. x /\ y``;
> val it = |- (\x y. x /\ y) = (\a b. a /\ b) : thm
- RENAME_VARS_CONV ["a", "b"] ``!x:'a y. P x /\ P y``;
> val it = |- (!x y. P x /\ P y) = !a b. P a /\ P b : thm
- RENAME_VARS_CONV ["a", "b"] ``!x:'a. ?y. P x /\ P y``;
> val it = |- (!x. ?y. P x /\ P y) = !a. ?b. P a /\ P b : thm
```

Post-processing mangling of names in code implementing derived logical
procedures to make names look more appropriate. Changing names can only
affect the presentation of terms, not their semantics.

### See also

[`Term.aconv`](#Term.aconv), [`Thm.ALPHA`](#Thm.ALPHA)
