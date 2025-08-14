## `ASSUME_TAC`

``` hol4
Tactic.ASSUME_TAC : thm_tactic
```

------------------------------------------------------------------------

Adds an assumption to a goal.

Given a theorem `th` of the form `A' |- u`, and a goal, `ASSUME_TAC th`
adds `u` to the assumptions of the goal.

``` hol4
         A ?- t
    ==============  ASSUME_TAC (A' |- u)
     A u {u} ?- t
```

Note that unless `A'` is a subset of `A`, this tactic is invalid.

### Failure

Never fails.

### Example

Given a goal `g` of the form `{x = y, y = z} ?- P`, where `x`, `y` and
`z` have type `:'a`, the theorem `x = y, y = z |- x = z` can, first, be
inferred by forward proof

``` hol4
   let val eq1 = Term `(x:'a) = y`
       val eq2 = Term `(y:'a) = z`
   in
   TRANS (ASSUME eq1) (ASSUME eq2)
   end;
```

and then added to the assumptions. This process requires the explicit
text of the assumptions, as well as invocation of the rule `ASSUME`:

``` hol4
   let val eq1 = Term `(x:'a) = y`
       val eq2 = Term `(y:'a) = z`
       val goal = ([eq1,eq2],Parse.Term `P:bool`)
   in
   ASSUME_TAC (TRANS (ASSUME eq1) (ASSUME eq2)) goal
   end;

   val it = ([([`x = z`, `x = y`, `y = z`], `P`)], fn) : tactic_result
```

This is the naive way of manipulating assumptions; there are more
advanced proof styles (more elegant and less transparent) that achieve
the same effect, but this is a perfectly correct technique in itself.

Alternatively, the axiom `EQ_TRANS` could be added to the assumptions of
`g`:

``` hol4
   let val eq1 = Term `(x:'a) = y`
       val eq2 = Term `(y:'a) = z`
       val goal = ([eq1,eq2], Term `P:bool`)
   in
   ASSUME_TAC EQ_TRANS goal
   end;

   val it =
     ([([`!x y z. (x = y) /\ (y = z) ==> (x = z)`,
         `x = y`,`y = z`],`P`)],fn) : tactic_result
```

A subsequent resolution (see `RES_TAC`) would then be able to add the
assumption `x = z` to the subgoal shown above. (Aside from purposes of
example, it would be more usual to use `IMP_RES_TAC` than `ASSUME_TAC`
followed by `RES_TAC` in this context.)

`ASSUME_TAC` is the naive way of manipulating assumptions (i.e. without
recourse to advanced tacticals); and it is useful for enriching the
assumption list with lemmas as a prelude to resolution (`RES_TAC`,
`IMP_RES_TAC`), rewriting with assumptions (`ASM_REWRITE_TAC` and so
on), and other operations involving assumptions.

### See also

[`Tactic.ACCEPT_TAC`](#Tactic.ACCEPT_TAC),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC)
