## `ADD_SGS_TAC`

``` hol4
Tactical.ADD_SGS_TAC : term list -> tactic -> tactic
```

------------------------------------------------------------------------

Adds extra sub-goals to the outcome of a tactic, as may be required to
make an invalid tactic valid.

Suppose `tac` applied to the goal `(asl,w)` produces new goal list `gl`.
Then `ADD_SGS_TAC tml tac (asl,w)` produces, as new goals, `gl` and,
additionally, `(asl,tm)` for each `tm` in `tml`.

Then, if the justification returned by `tac`, when applied to the proved
goals `gl`, gives a theorem which uses some additional assumption `tm`
in `tml`, then the proved goal `(asl,tm)` is used to remove `tm` from
the assumption list of that theorem.

### Failure

`ADD_SGS_TAC tml tac (asl,w)` fails if `tac (asl,w)` fails.

Where a tactic `tac` requires certain assumptions `tml` to be present in
the goal, which are not present but are capable of being proved,
`ADD_SGS_TAC tml tac` will conveniently set up new subgoals to prove the
missing assumptions.

### Comments

`VALIDATE tac` is similar and will usually be easier to use, but its
extra new subgoals may occur in an unpredictable order.

### Example

Given a goal with an implication in the assumptions, one can split it
into two subgoals, defining an auxiliary function

``` hol4
fun split_imp_asm th =
  let val (tm, thu) = UNDISCH_TM th ;
  in ADD_SGS_TAC [tm] (ASSUME_TAC thu) end ;
```

This can be used as follows:

``` hol4
1 subgoal:
val it =

r
------------------------------------
  p ==> q
:
   proof

> e (FIRST_X_ASSUM split_imp_asm) ;

OK..
2 subgoals:
val it =

r
------------------------------------
  q

p

2 subgoals
:
   proof
```

To propose a term, prove it as a subgoal and then use it to prove the
goal, as is done using `SUBGOAL_THEN tm ASSUME_TAC`, can also be done by
`ADD_SGS_TAC [tm] (ASSUME_TAC (ASSUME tm))`

### See also

[`Tactical.VALIDATE`](#Tactical.VALIDATE),
[`Tactical.GEN_VALIDATE`](#Tactical.GEN_VALIDATE)
