## `PSPEC_TAC`

``` hol4
PairRules.PSPEC_TAC : term * term -> tactic
```

------------------------------------------------------------------------

Generalizes a goal.

When applied to a pair of terms `(q,p)`, where `p` is a paired structure
of variables and a goal `A ?- t`, the tactic `PSPEC_TAC` generalizes the
goal to `A ?- !p. t[p/q]`, that is, all components of `q` are turned
into the corresponding components of `p`.

``` hol4
        A ?- t
   =================  PSPEC_TAC (q,p)
    A ?- !x. t[p/q]
```

### Failure

Fails unless `p` is a paired structure of variables with the same type
as `q`.

### Example

``` hol4
- g `1 + 2 = 2 + 1`;
> val it =
    Proof manager status: 1 proof.
    1. Incomplete:
         Initial goal:
         1 + 2 = 2 + 1

- e (PSPEC_TAC (Term`(1,2)`, Term`(x:num,y:num)`));
OK..
1 subgoal:
> val it =
    !(x,y). x + y = y + x

     : proof
```

Removing unnecessary speciality in a goal, particularly as a prelude to
an inductive proof.

### See also

[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC)
