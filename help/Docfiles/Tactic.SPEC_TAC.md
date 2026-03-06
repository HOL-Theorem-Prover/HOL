## `SPEC_TAC`

``` hol4
Tactic.SPEC_TAC : term * term -> tactic
```

------------------------------------------------------------------------

Generalizes a goal.

When applied to a pair of terms `(u,x)`, where `x` is just a variable,
and a goal `A ?- t`, the tactic `SPEC_TAC` generalizes the goal to
`A ?- !x. t[x/u]`, that is, all instances of `u` are turned into `x`.

``` hol4
        A ?- t
   =================  SPEC_TAC (u,x)
    A ?- !x. t[x/u]
```

### Failure

Fails unless `x` is a variable with the same type as `u`.

Removing unnecessary speciality in a goal, particularly as a prelude to
an inductive proof.

### See also

[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL),
[`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Thm.SPEC`](#Thm.SPEC), [`Drule.SPECL`](#Drule.SPECL),
[`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC)
