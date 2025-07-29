## `VALIDATE_LT`

``` hol4
Tactical.VALIDATE_LT : list_tactic -> list_tactic
```

------------------------------------------------------------------------

Makes a list-tactic valid if its invalidity is due to relying on
assumptions not present in one of the goals.

When list-tactic `ltac` is applied to a goal list `gl` it produces a new
goal list `gl'` and a justification. When the justification is applied
to a list `thl'` of theorems which are the new goals `gl'`, proved, it
should produce a list `thl` of theorems which are the goals `gl`,
proved.

A list-tactic can be invalid due to proving a theorem whose conclusion
differs from that of the corresponding goal, or due to proving a theorem
which contains extra assumptions relative to the corresponding goal. In
this latter case, `VALIDATE_LT ltac` makes the list-tactic valid by
returning extra subgoals to prove those extra assumptions.

See `VALID_LT` for more details.

### Failure

Fails by design if `ltac`, when applied to a goal list, produces a proof
which is invalid on account of proving a theorem whose conclusion
differs from that of the corresponding goal.

Also fails if `ltac` fails when applied to the given goals.

### Example

Where `uthr'` is `[p', q] |- r` and `uths'` is `[p, q'] |- s`

``` hol4
2 subgoals:
val it =

s
------------------------------------
  0.  p
  1.  q

r
------------------------------------
  0.  p
  1.  q

2 subgoals
:
   proof

> elt (ALLGOALS (FIRST (map ACCEPT_TAC [uthr', uths']))) ;
OK..

Exception raised at Tactical.VALID_LT:
Invalid list-tactic [...]

> elt (VALIDATE_LT (ALLGOALS (FIRST (map ACCEPT_TAC [uthr', uths'])))) ;
OK..
2 subgoals:
val it =

q'
------------------------------------
  0.  p
  1.  q

p'
------------------------------------
  0.  p
  1.  q

2 subgoals
:
   proof
```

Where a tactic `ltac` requires certain assumptions to be present in one
of the goals, which are not present but are capable of being proved,
`VALIDATE_LT ltac` will conveniently set up new subgoals to prove the
missing assumptions.

### See also

[`Tactical.VALID`](#Tactical.VALID),
[`Tactical.VALID_LT`](#Tactical.VALID_LT),
[`Tactical.VALIDATE`](#Tactical.VALIDATE),
[`proofManagerLib.elt`](#proofManagerLib.elt),
[`proofManagerLib.expand_list`](#proofManagerLib.expand_list)
