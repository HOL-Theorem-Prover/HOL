## `gen_tyvarify`

``` hol4
boolSyntax.gen_tyvarify : term -> term
```

------------------------------------------------------------------------

Instantiates a term with fresh type variables

A call to `gen_tyvarify tm` renames all of the type variables in term
`tm` to fresh replacements (generated with `gen_tyvar`).

### Failure

Never fails.

### Example

``` hol4
> show_types := true;
> gen_tyvarify “h::t”;
<<HOL message: inventing new type variable names: 'a>>
val it = “(h :%%gen_tyvar%%30)::(t :%%gen_tyvar%%30 list)”: term
```

### See also

[`Type.gen_tyvar`](#Type.gen_tyvar)
