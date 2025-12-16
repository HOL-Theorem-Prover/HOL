## `subst`

``` hol4
Lib.type ('a,'b) subst
```

------------------------------------------------------------------------

Type abbreviation for substitutions.

The type `('a,'b) subst` abbreviates the type `{redex,residue} list`, in
which `redex` has type `'a` and `residue` has type `'b`. Usually, a
`{redex,residue}` pair in a substition is interpreted as 'replace
occurrences of `redex` by `residue`'.

### Comments

The different types of `redex` and `residue` components allows
flexibility, as in the rule of inference `SUBST`, which takes a
`(term,thm) subst` argument.

### See also

[`Lib.|->`](#Lib..GZKQ4), [`Term.subst`](#Term.subst),
[`Term.inst`](#Term.inst), [`Thm.SUBST`](#Thm.SUBST)
