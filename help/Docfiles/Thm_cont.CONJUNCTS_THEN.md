## `CONJUNCTS_THEN`

``` hol4
Thm_cont.CONJUNCTS_THEN : thm_tactical
```

------------------------------------------------------------------------

Applies a theorem-tactic to each conjunct of a theorem.

`CONJUNCTS_THEN` takes a theorem-tactic `f`, and a theorem `t` whose
conclusion must be a conjunction. `CONJUNCTS_THEN` breaks `t` into two
new theorems, `t1` and `t2` which are `CONJUNCT1` and `CONJUNCT2` of `t`
respectively, and then returns a new tactic: `f t1 THEN f t2`. That is,

``` hol4
   CONJUNCTS_THEN f (A |- l /\ r) =  f (A |- l) THEN f (A |- r)
```

so if

``` hol4
   A1 ?- t1                    A2 ?- t2
  ==========  f (A |- l)      ==========  f (A |- r)
   A2 ?- t2                    A3 ?- t3
```

then

``` hol4
    A1 ?- t1
   ==========  CONJUNCTS_THEN f (A |- l /\ r)
    A3 ?- t3
```

### Failure

`CONJUNCTS_THEN f` will fail if applied to a theorem whose conclusion is
not a conjunction.

### Comments

`CONJUNCTS_THEN f (A |- u1 /\ ... /\ un)` results in the tactic:

``` hol4
   f (A |- u1) THEN f (A |- u2 /\ ... /\ un)
```

Unfortunately, it is more likely that the user had wanted the tactic:

``` hol4
   f (A |- u1) THEN ... THEN f(A |- un)
```

Such a tactic could be defined as follows:

``` hol4
   fun CONJUNCTS_THENL (f:thm_tactic) thm =
     List.foldl (op THEN) ALL_TAC (map f (CONJUNCTS thm));
```

or by using `REPEAT_TCL`.

### See also

[`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS),
[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Thm_cont.CONJUNCTS_THEN2`](#Thm_cont.CONJUNCTS_THEN2),
[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN)
