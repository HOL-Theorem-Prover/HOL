## `type_unify`

``` hol4
boolSyntax.type_unify : hol_type -> hol_type -> (hol_type,hol_type) subst
```

------------------------------------------------------------------------

Performs classical type unification.

Calculates a substitution `theta` such that instantiating each of the
arguments with `theta` gives the same result type.

If `type_unify ty1 ty2` succeeds, then

``` hol4
    type_subst (type_unify ty1 ty2) ty1 = type_subst (type_unify ty1 ty2) ty2
```

### Failure

If no such substitution can be found. This could be due to incompatible
type constructors, or the failing of an occurs check.

### Example

``` hol4
- let val ty1 = Type `:'a -> 'b -> 'a`
      val ty2 = Type `:'a -> 'b -> 'b`
  in
     type_subst (type_unify ty1 ty2) ty1 = type_subst (type_unify ty1 ty2) ty2
  end;
> val it = true : bool

- let val alpha_list = Type `:'a list`
  in
     type_unify alpha alpha_list handle e => Raise e
  end;

  Exception raised at boolSyntax.type_unify:
  occurs check
  Exception-
     HOL_ERR
       {message = "occurs check", origin_function = "type_unify",
        origin_structure = "boolSyntax"} raised
```

Note that attempting to use `Type.match_type` in the first example
results in immediate error, as it can only attempt to substitute the
first argument to match the second:

``` hol4
- let val ty1 = Type `:'a -> 'b -> 'a`
      val ty2 = Type `:'a -> 'b -> 'b`
  in
     match_type ty1 ty2 handle e => Raise e
  end;

  Exception raised at Type.raw_match_type:
  double bind on type variable 'a
  Exception-
   HOL_ERR
     {message = "double bind on type variable 'a", origin_function =
      "raw_match_type", origin_structure = "Type"} raised
```

### See also

[`boolSyntax.sep_type_unify`](#boolSyntax.sep_type_unify),
[`Type.match_type`](#Type.match_type),
[`Type.type_subst`](#Type.type_subst), [`Term.inst`](#Term.inst)
