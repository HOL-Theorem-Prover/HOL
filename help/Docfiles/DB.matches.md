## `matches`

``` hol4
DB.matches : term -> thm -> bool
```

------------------------------------------------------------------------

Tells whether part of a theorem matches a pattern.

An invocation `DB.match pat th` tells whether the conclusion of `th` has
a subterm matching `pat`.

### Failure

Never fails.

### Example

``` hol4
> DB.matches (Term `(a = b) = c`) EQ_CLAUSES ;
<<HOL message: inventing new type variable names: 'a>>
val it = true: bool

> DB.matches (Term `(a = b) = c`)  EQ_TRANS ;
<<HOL message: inventing new type variable names: 'a>>
val it = false: bool
```

### Comments

The notion of matching is a restricted version of higher-order matching,
as used by `DB.apropos, DB.apropos_in, DB.match`, etc.

For locating theorems relevant to a given pattern.

### See also

[`DB.matcher`](#DB.matcher), [`DB.matchp`](#DB.matchp),
[`DB.apropos`](#DB.apropos), [`DB.apropos_in`](#DB.apropos_in)
