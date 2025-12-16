## `SPOSE_NOT_THEN`

``` hol4
bossLib.SPOSE_NOT_THEN : (thm -> tactic) -> tactic
```

------------------------------------------------------------------------

Initiate proof by contradiction.

`SPOSE_NOT_THEN` provides a flexible way to start a proof by
contradiction. Simple tactics for contradiction proofs often simply
negate the goal and place it on the assumption list. However, if the
goal is quantified, as is often the case, then more processing is
required in order to get it into a suitable form for subsequent work.
`SPOSE_NOT_THEN ttac` negates the current goal, pushes the negation
inwards, and applies `ttac` to it.

### Failure

Never fails, unless `ttac` fails.

### Example

Suppose we want to prove Euclid's theorem.

``` hol4
   !m. ?n. prime n /\ m < n
```

The classic proof is by contradiction. However, if we start such a proof
with `CCONTR_TAC`, we get the goal

``` hol4
   { ~!m. ?n. prime n /\ m < n } ?- F
```

and one would immediately want to simplify the assumption, which is a
bit awkward. Instead, an invocation `SPOSE_NOT_THEN ASSUME_TAC` yields

``` hol4
   { ?m. !n. ~prime n \/ ~(m < n) } ?- F
```

and `SPOSE_NOT_THEN STRIP_ASSUME_TAC` results in

``` hol4
   { !n. ~prime n \/ ~(m < n) } ?- F
```

### See also

[`Tactic.CCONTR_TAC`](#Tactic.CCONTR_TAC),
[`Tactic.CONTR_TAC`](#Tactic.CONTR_TAC),
[`Tactic.ASSUME_TAC`](#Tactic.ASSUME_TAC),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC)
