## `apropos_in`

``` hol4
DB.apropos_in : term -> data list -> data list
```

------------------------------------------------------------------------

Attempt to select matching theorems among a given list.

An invocation `DB.apropos_in M data_list` selects all theorems,
definitions, and axioms within `data_list` that have a subterm that
matches `M`. If there are no matches, the empty list is returned.

### Failure

Never fails.

### Example

``` hol4
- DB.apropos (Term `(!x y. P x y) ==> Q`);
<<HOL message: inventing new type variable names: 'a, 'b>>
> val it =
    [(("ind_type", "INJ_INVERSE2"),
      (|- !P.
            (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) = (x1 = x2) /\ (y1 = y2)) ==>
            ?X Y. !x y. (X (P x y) = x) /\ (Y (P x y) = y), Thm)),
     (("pair", "pair_induction"),
      (|- (!p_1 p_2. P (p_1,p_2)) ==> !p. P p, Thm))] :
  ((string * string) * (thm * class)) list

- DB.apropos_in (Term `(x, y)`) it ;
    [(("pair", "pair_induction"),
      (|- (!p_1 p_2. P (p_1,p_2)) ==> !p. P p, Thm))] :
  ((string * string) * (thm * class)) list
```

### Comments

The notion of matching is a restricted version of higher-order matching.
It uses `DB.matches`.

Finding theorems in interactive proof sessions. The second argument will
normally be the result of a previous call to
`DB.find, DB.match, DB.apropos, DB.listDB, DB.thy` etc.

### See also

[`DB.apropos`](#DB.apropos), [`DB.match`](#DB.match),
[`DB.matches`](#DB.matches), [`DB.find`](#DB.find),
[`DB.find_in`](#DB.find_in), [`DB.listDB`](#DB.listDB),
[`DB.thy`](#DB.thy), [`DB.theorems`](#DB.theorems)
