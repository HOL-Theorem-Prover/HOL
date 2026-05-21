## `match`

``` hol4
DB.match : string list -> term -> data list
```

------------------------------------------------------------------------

Attempt to find matching theorems in the specified theories.

An invocation `DB.match [s1,...,sn] M` collects all theorems,
definitions, and axioms of the theories designated by `s1`,...,`sn` that
have a subterm that matches `M`. If there are no matches, the empty list
is returned.

The strings `s1`,...,`sn` should be a subset of the currently loaded
theory segments. The string `"-"` may be used to designate the current
theory segment. If the list of theories is empty, then all currently
loaded theories are searched.

### Failure

Never fails.

### Example

``` hol4
- DB.match ["bool","pair"] (Term `(a = b) = c`);
<<HOL message: inventing new type variable names: 'a>>
> val it =
    [(("bool", "EQ_CLAUSES"),
      (|- !t.((T = t) = t) /\ ((t = T) = t) /\
             ((F = t) = ~t) /\ ((t = F) = ~t), Db.Thm)),
     (("bool", "EQ_EXPAND"),
      (|- !t1 t2. (t1 = t2) = t1 /\ t2 \/ ~t1 /\ ~t2, Db.Thm)),
     (("bool", "EQ_IMP_THM"),
      (|- !t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1), Db.Thm)),
     (("bool", "EQ_SYM_EQ"), (|- !x y. (x = y) = (y = x), Db.Thm)),
     (("bool", "FUN_EQ_THM"), (|- !f g. (f = g) = !x. f x = g x, Db.Thm)),
     (("bool", "OR_IMP_THM"), (|- !A B. (A = B \/ A) = B ==> A, Db.Thm)),
     (("bool", "REFL_CLAUSE"), (|- !x. (x = x) = T, Db.Thm)),
     (("pair", "CLOSED_PAIR_EQ"),
      (|- !x y a b. ((x,y) = (a,b)) = (x = a) /\ (y = b), Db.Thm)),
     (("pair", "CURRY_ONE_ONE_THM"),
      (|- (CURRY f = CURRY g) = (f = g), Db.Thm)),
     (("pair", "PAIR_EQ"), (|- ((x,y) = (a,b)) = (x = a) /\ (y = b), Db.Thm)),
     (("pair", "UNCURRY_ONE_ONE_THM"),
      (|- (UNCURRY f = UNCURRY g) = (f = g), Db.Thm))] :
  ((string * string) * (thm * class)) list
```

### Comments

The notion of matching is a restricted version of higher-order matching.

For locating theorems when doing interactive proof.

### See also

[`DB.matcher`](#DB.matcher), [`DB.matchp`](#DB.matchp),
[`DB.find`](#DB.find), [`DB.theorems`](#DB.theorems),
[`DB.thy`](#DB.thy), [`DB.listDB`](#DB.listDB),
[`holyHammer.hh`](#holyHammer.hh)
