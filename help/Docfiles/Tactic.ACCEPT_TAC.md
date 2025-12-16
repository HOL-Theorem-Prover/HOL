## `ACCEPT_TAC`

``` hol4
Tactic.ACCEPT_TAC : thm_tactic
```

------------------------------------------------------------------------

Solves a goal if supplied with the desired theorem (up to
alpha-conversion).

`ACCEPT_TAC` maps a given theorem `th` to a tactic that solves any goal
whose conclusion is alpha-convertible to the conclusion of `th`.

### Failure

`ACCEPT_TAC th (A,g)` fails if the term `g` is not alpha-convertible to
the conclusion of the supplied theorem `th`.

### Example

`ACCEPT_TAC` applied to the axiom

``` hol4
   BOOL_CASES_AX = |- !t. (t = T) \/ (t = F)
```

will solve the goal

``` hol4
   ?- !x. (x = T) \/ (x = F)
```

but will fail on the goal

``` hol4
   ?- !x. (x = F) \/ (x = T)
```

Used for completing proofs by supplying an existing theorem, such as an
axiom, or a lemma already proved.

### See also

[`Tactic.MATCH_ACCEPT_TAC`](#Tactic.MATCH_ACCEPT_TAC)
