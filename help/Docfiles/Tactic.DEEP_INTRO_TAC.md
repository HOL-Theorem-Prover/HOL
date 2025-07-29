## `DEEP_INTRO_TAC`

``` hol4
Tactic.DEEP_INTRO_TAC : thm -> tactic
```

------------------------------------------------------------------------

Applies an introduction-rule backwards; instantiating a predicate
variable.

The function `DEEP_INTRO_TAC` expects a theorem of the form

``` hol4
   antecedents ==> P (term-pattern)
```

where `P` is a variable, and `term-pattern` is a pattern describing the
form of an expected sub-term in the goal. When `th` is of this form, the
tactic `DEEP_INTRO_TAC th` finds a higher-order instantiation for the
variable `P` and a first order instantiation for the variables in
`term-pattern` such that the instantiated conclusion of `th` is
identical to the goal. It then applies `MATCH_MP_TAC` to turn the goal
into an instantiation of the antecedents of `th`.

### Failure

Fails if there is no (free) instance of `term-pattern` in the goal. Also
fails if `th` is not of the required form.

### Example

The theorem `SELECT_ELIM_THM` states

``` hol4
   |- !P Q. (?x. P x) /\ (!x. P x ==> Q x) ==> Q ($@ P)
```

This is of the required form for use by `DEEP_INTRO_TAC`, and can be
used to transform a goal mentioning Hilbert Choice (the `@` operator)
into one that doesn't. Indeed, this is how `SELECT_ELIM_TAC` is
implemented.

### See also

[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC),
[`Tactic.SELECT_ELIM_TAC`](#Tactic.SELECT_ELIM_TAC)
