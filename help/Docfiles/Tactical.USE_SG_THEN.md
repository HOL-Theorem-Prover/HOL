## `USE_SG_THEN`

``` hol4
Tactical.USE_SG_THEN : thm_tactic -> int -> int -> list_tactic
```

------------------------------------------------------------------------

Allows the user to use one subgoal to prove another

In `USE_SG_THEN ttac nu np`, of the current goal list, subgoal number
`nu` can be used in proving subgoal number `np`. Subgoal number `nu` is
used as a lemma by `ttac` to simplify subgoal number `np`. That is, if
subgoal number `nu` is `A ?- u`, subgoal number `np` is `A1 ?- t1`, and

``` hol4
    A1 ?- t1
   ==========  ttac (u |- u)
    A2 ?- t2
```

then the list-tactic `USE_SG_THEN ttac nu np` gives this same result
(new subgoal(s)) for subgoal `np`.

This list-tactic will be invalid unless `A` is a subset of `A1`.

Note that in the interactive system, subgoals are printed in reverse
order of their numbering.

### Failure

`USE_SG_THEN` will fail `ttac (u |- u)` fails on subgoal number `np`, or
if indices `np` or `nu` are out of range. Note that the subgoals in the
current subgoal list are numbered starting from 1.

Where two subgoals are similar and not easy to prove, one can be used to
help prove the other.

### Example

Here subgoal 1 is assumed, so as to help in proving subgoal 2.

``` hol4
r \/ s
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

> elt (USE_SG_THEN ASSUME_TAC 1 2) ;
OK..
2 subgoals:
val it =

r \/ s
------------------------------------
  0.  p
  1.  q
  2.  r


r
------------------------------------
  0.  p
  1.  q

2 subgoals
:
   proof
```

Here is an example where the assumptions differ. Subgoal 2 is used to
solve subgoal 1, but the assumption `p'` of subgoal 2 remains to be
proved. Without `VALIDATE_LT`, the list-tactic would be invalid.

``` hol4
r
------------------------------------
  0.  p'
  1.  q


r
------------------------------------
  0.  p
  1.  q

2 subgoals
:
   proof

> elt (VALIDATE_LT (USE_SG_THEN ACCEPT_TAC 2 1)) ;
OK..
2 subgoals:
val it =

r
------------------------------------
  0.  p'
  1.  q


p'
------------------------------------
  0.  p
  1.  q

2 subgoals
:
   proof
```

### Comments

Some users may expect the generated tactic to be `ttac (A |- u)`, rather
than `ttac (u |- u)`.
