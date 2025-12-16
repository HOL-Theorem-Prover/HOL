## `drule_all`

``` hol4
Tactic.drule_all : thm -> tactic
```

------------------------------------------------------------------------

Attempts to discharge all of a theorem's antecedents from assumptions

If `th` is a theorem with a conclusion that is a (possibly universally
quantified) implication (or negation), the theorem-tactic `drule_all`
(implicitly) normalises it have form

``` hol4
    !v1 .. vn. P1 ==> (P2 ==> (P3 ==> ... Q)...)
```

where each `Pi` is not a conjunction. (In other words, `P /\ Q ==> R` is
normalised to `P ==> (Q ==> R)`.) An application of `drule_all th` to a
goal then attempts to find a consistent instantiation so that all of the
`Pi` antecedents can be discharged by appeal to the goal's assumptions.
If this repeated instantiation and use of `MP` is possible, then the
(instantiated) conclusion `Q` is added to the goal with the `MP_TAC`
`thm_tactic`.

When finding assumptions, those that have been most recently added to
the assumption list will be preferred.

### Failure

An invocation of `drule_all th` can only fail when applied to a goal. It
can then fail if `th` is not an implication, or if all of `th`'s
implications cannot be eliminated by matching against the goal's
assumptions.

### Example

The `LESS_LESS_EQ_TRANS` theorem states:

``` hol4
   !m n p. m < n /\ n <= p ==> m < p
```

Then:

``` hol4
   > drule_all arithmeticTheory.LESS_LESS_EQ_TRANS
      ([“x < w”, “1 < x”, “z <= y”, “x <= z”, “y < z”], “P:bool”);
   val it =
      ([([“x < w”, “1 < x”, “z <= y”, “x <= z”, “y < z”],
         “1 < z ==> P”)], fn): goal list * validation
```

Note how the other possible instance of the theorem (chaining `y < z`
and `z <= y`) is not found.

### Comments

The variant `dxrule_all` removes used assumptions from the assumption
list as they resolve against the theorem. The variant `drule_all_then`
allows a continuation other than `MP_TAC` to be used. The variant
`dxrule_all_then` combines both.

A negated conclusion (`~Q`) is not treated as an implication (`Q ==> F`)
so the tactic will not attempt to find an instantiation of `Q` among the
assumptions.

### See also

[`Tactic.drule`](#Tactic.drule),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC)
