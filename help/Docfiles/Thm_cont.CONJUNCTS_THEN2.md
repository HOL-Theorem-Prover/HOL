## `CONJUNCTS_THEN2`

``` hol4
Thm_cont.CONJUNCTS_THEN2 : (thm_tactic -> thm_tactical)
```

------------------------------------------------------------------------

Applies two theorem-tactics to the corresponding conjuncts of a theorem.

`CONJUNCTS_THEN2` takes two theorem-tactics, `f1` and `f2`, and a
theorem `t` whose conclusion must be a conjunction. `CONJUNCTS_THEN2`
breaks `t` into two new theorems, `t1` and `t2` which are `CONJUNCT1`
and `CONJUNCT2` of `t` respectively, and then returns the tactic
`f1 t1 THEN f2 t2`. Thus

``` hol4
   CONJUNCTS_THEN2 f1 f2 (A |- l /\ r) =  f1 (A |- l) THEN f2 (A |- r)
```

so if

``` hol4
   A1 ?- t1                     A2 ?- t2
  ==========  f1 (A |- l)      ==========  f2 (A |- r)
   A2 ?- t2                     A3 ?- t3
```

then

``` hol4
    A1 ?- t1
   ==========  CONJUNCTS_THEN2 f1 f2 (A |- l /\ r)
    A3 ?- t3
```

### Failure

`CONJUNCTS_THEN f` will fail if applied to a theorem whose conclusion is
not a conjunction.

### Comments

The system shows the type as `(thm_tactic -> thm_tactical)`.

The construction of complex `tactical`s like `CONJUNCTS_THEN`.

### See also

[`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS),
[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Thm_cont.CONJUNCTS_THEN2`](#Thm_cont.CONJUNCTS_THEN2),
[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN)
