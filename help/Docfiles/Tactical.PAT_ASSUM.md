## `PAT_ASSUM`

``` hol4
Tactical.PAT_ASSUM : term -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Finds the first assumption that matches the term argument, applies the
theorem tactic to it. The matching assumption remains in the assumption
list.

The tactic

``` hol4
   PAT_ASSUM tm ttac ([A1, ..., An], g)
```

finds the first `Ai` which matches `tm` using higher-order pattern
matching in the sense of `ho_match_term`. Free variables in the pattern
that are also free in the assumptions or the goal must not be bound by
the match. In effect, these variables are being treated as local
constants.

### Failure

Fails if the term doesn't match any of the assumptions, or if the
theorem-tactic fails when applied to the first assumption that does
match the term.

### Example

The tactic

``` hol4
   PAT_ASSUM ``x:num = y`` SUBST_ALL_TAC
```

searches the assumptions for an equality over numbers and causes its
right hand side to be substituted for its left hand side throughout the
goal and assumptions. It also removes the equality from the assumption
list. Trying to use `FIRST_ASSUM` above (i.e., replacing `PAT_ASSUM`
with `FIRST_ASSUM` and dropping the term argument entirely) would
require that the desired equality was the first such on the list of
assumptions.

If one is trying to solve the goal

``` hol4
   { !x. f x = g (x + 1), !x. g x = f0 (f x)} ?- f x = g y
```

rewriting with the assumptions directly will cause a loop. Instead, one
might want to rewrite with the formula for `f`. This can be done in an
assumption-order-independent way with

``` hol4
   PAT_ASSUM (Term`!x. f x = f' x`) (fn th => REWRITE_TAC [th])
```

This use of the tactic exploits higher order matching to match the RHS
of the assumption, and the fact that `f` is effectively a local constant
in the goal to find the correct assumption.

### Comments

The behavior of `PAT_ASSUM` changed in Kananaskis 12. The old
`PAT_ASSUM` (and `qpat_assum`, `Q.PAT_ASSUM`) was changed to include an
extra `_X_` (or `_x_`), indicating that the matching assumption is
pulled out of the assumption list. The old name now provides a version
that doesn't pull the assumption out of the list.

### See also

[`Tactical.PAT_X_ASSUM`](#Tactical.PAT_X_ASSUM),
[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST),
[`Thm_cont.UNDISCH_THEN`](#Thm_cont.UNDISCH_THEN),
[`Term.match_term`](#Term.match_term)
