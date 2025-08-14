## `VALIDATE`

``` hol4
Tactical.VALIDATE : tactic -> tactic
```

------------------------------------------------------------------------

Makes a tactic valid if its invalidity is due to relying on assumptions
not present in the goal.

Suppose `tac` applied to the goal `(asl,g)` produces a justification
that creates a theorem `A |- g'`. If `A` a not a subset of `asl`, then
the tactic is invalid (and `VALID tac (asl,g)` fails, ie, raises an
exception). But `VALIDATE tac (asl,g)` produces a subgoal list augmented
by the members of `A` missing from `asl`.

If `g'` differs from `g`, both `VALID tac (asl,g)` and
`VALIDATE tac (asl,g)` fail.

### Failure

Fails by design if `tac`, when applied to a goal, produces a proof which
is invalid on account of proving a theorem whose conclusion differs from
that of the goal.

Also fails if `tac` fails when applied to the given goal.

### Example

For example, where theorem `uth'` is `[p'] |- q`

``` hol4
1 subgoal:
val it =

q
------------------------------------
  p
:
   proof

> e (ACCEPT_TAC uth') ;
OK..

Exception raised at Tactical.VALID:
Invalid tactic [...]

> e (VALIDATE (ACCEPT_TAC uth')) ;
OK..
1 subgoal:
val it =

p'
------------------------------------
  p
:
   proof
```

Given a goal with an implication in the assumptions, one can split it
into two subgoals.

``` hol4
1 subgoal:
val it =

r
------------------------------------
  p ==> q
:
   proof

> e (VALIDATE (POP_ASSUM (ASSUME_TAC o UNDISCH))) ;

OK..
2 subgoals:
val it =

r
------------------------------------
  q

p
------------------------------------
  p ==> q

2 subgoals
:
   proof
```

Meanwhile, to propose a term, prove it as a subgoal and then use it to
prove the goal, as is done using `SUBGOAL_THEN tm ASSUME_TAC`, can also
be done by `VALIDATE (ASSUME_TAC (ASSUME tm)))`

Where a tactic `tac` requires certain assumptions to be present in the
goal, which are not present but are capable of being proved,
`VALIDATE tac` will conveniently set up new subgoals to prove the
missing assumptions.

### See also

[`proofManagerLib.expand`](#proofManagerLib.expand),
[`Tactical.VALID`](#Tactical.VALID),
[`Tactical.GEN_VALIDATE`](#Tactical.GEN_VALIDATE),
[`Tactical.ADD_SGS_TAC`](#Tactical.ADD_SGS_TAC),
[`Tactical.SUBGOAL_THEN`](#Tactical.SUBGOAL_THEN)
