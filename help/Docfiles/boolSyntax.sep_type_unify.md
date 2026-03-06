## `sep_type_unify`

``` hol4
boolSyntax.sep_type_unify : hol_type -> hol_type ->
        (hol_type,hol_type) subst * (hol_type,hol_type) subst
```

------------------------------------------------------------------------

Calculates a pair of substitutions `(theta1, theta2)` such that
instantiating the first argument with `theta1` equals the second
argument instatiated with `theta2`.

If `sep_type_unify ty1 ty2` succeeds, then

``` hol4
    type_subst (sep_type_unify ty1 ty2 |> fst) ty1 =
      type_subst (sep_type_unify ty1 ty2 |> snd) ty2
```

### Failure

If no such substitution can be found.

### Example

``` hol4
- let val alpha_list = Type `:'a list`
  in
     sep_type_unify alpha alpha_list
  end;
> val it = ([{redex = “:α”, residue = “:α list”}], []):
   (hol_type, hol_type) Lib.subst * (hol_type, hol_type) subst

- let val ty1 = Type `:'a -> 'b -> 'b`
      val ty2 = Type `:'a list -> 'b list -> 'a list`
  in
    sep_type_unify ty1 ty2
  end;
> val it =
   ([{redex = “:β”, residue = “:α list”},
     {redex = “:α”, residue = “:α list”}], [{redex = “:β”, residue = “:α”}]):
   (hol_type, hol_type) Lib.subst * (hol_type, hol_type) subst
```

Note that in these examples, `type_unify` would fail due to an occurs
check:

``` hol4
- let val ty1 = Type `:'a -> 'b -> 'b`
      val ty2 = Type `:'a list -> 'b list -> 'a list`
  in
    type_unify ty1 ty2
  end;

  Exception raised at boolSyntax.type_unify:
  occurs check
  Exception-
     HOL_ERR
       {message = "occurs check", origin_function = "type_unify",
        origin_structure = "boolSyntax"} raised
```

### Comments

`sep_type_unify` is similar to `type_unify`, but does not run into
problems with occurs checks. It first renames all type variables, then
attempt to unify the argument types, returning two separate
substitutions as a result.

### See also

[`boolSyntax.type_unify`](#boolSyntax.type_unify),
[`Type.type_subst`](#Type.type_subst), [`Term.inst`](#Term.inst)
