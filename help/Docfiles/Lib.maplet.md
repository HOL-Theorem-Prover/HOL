## `|->`

``` hol4
op Lib.|-> : 'a * 'b -> {redex : 'a, residue : 'b}
```

------------------------------------------------------------------------

Infix operator for building a component of a substitution.

An application `x |-> y` is equal to `{redex = x, residue = y}`. Since
HOL substitutions are lists of `{redex,residue}` records, the `|->`
operator is merely sugar used to create substitutions.

### Failure

Never fails.

### Example

``` hol4
- type_subst [alpha |-> beta, beta |-> gamma]
             (alpha --> beta);
> val it = `:'b -> 'c` : hol_type
```

### See also

[`Lib.subst`](#Lib.subst), [`Type.type_subst`](#Type.type_subst),
[`Term.subst`](#Term.subst), [`Term.inst`](#Term.inst),
[`Thm.SUBST`](#Thm.SUBST)
