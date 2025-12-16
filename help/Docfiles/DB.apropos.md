## `apropos`

``` hol4
DB.apropos : term -> data list
```

------------------------------------------------------------------------

Attempt to find matching theorems in the currently loaded theories.

An invocation `DB.apropos M` collects all theorems, definitions, and
axioms of the currently loaded theories that have a subterm that matches
`M`. If there are no matches, the empty list is returned.

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
```

### Comments

The notion of matching is a restricted version of higher-order matching.

For finer control over the theories searched, use `DB.match`.

### See also

[`DB.match`](#DB.match), [`DB.find`](#DB.find),
[`DB.apropos_in`](#DB.apropos_in), [`DB.matches`](#DB.matches)
