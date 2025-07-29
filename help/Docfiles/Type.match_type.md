## `match_type`

``` hol4
Type.match_type : hol_type -> hol_type -> (hol_type,hol_type) subst
```

------------------------------------------------------------------------

Calculates a substitution `theta` such that instantiating the first
argument with `theta` equals the second argument.

If `match_type ty1 ty2` succeeds, then

``` hol4
    type_subst (match_type ty1 ty2) ty1 = ty2
```

### Failure

If no such substitution can be found.

### Example

``` hol4
- match_type alpha (Type`:num`);
> val it = [{redex = `:'a`, residue = `:num`}] : hol_type subst

- let val patt = Type`:('a -> bool) -> 'b`
      val ty =   Type`:(num -> bool) -> bool`
  in
     type_subst (match_type patt ty) patt = ty
  end;
> val it = true : bool

- match_type (alpha --> alpha)
             (ind   --> bool);
! Uncaught exception:
! HOL_ERR
```

### See also

[`Term.match_term`](#Term.match_term),
[`Type.type_subst`](#Type.type_subst)
