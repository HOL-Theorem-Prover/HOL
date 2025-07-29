## `Cases`

``` hol4
bossLib.Cases : tactic
```

------------------------------------------------------------------------

Performs case analysis on the variable of the leading universally
quantified variable of the goal.

When applied to a universally quantified goal `?- !u. G`, `Cases`
performs a case-split, based on the cases theorem for the type of `u`
stored in the global `TypeBase` database.

The cases theorem for a type `ty` will be of the form:

``` hol4
   |- !v:ty. (?x11...x1n1. v = C1 x11 ... x1n1) \/ .... \/
             (?xm1...xmnm. v = Cm xm1 ... xmnm)
```

where there is no requirement for there to be more than one disjunct,
nor for there to be any particular number of existentially quantified
variables in any disjunct. For example, the cases theorem for natural
numbers initially in the `TypeBase` is:

``` hol4
   |- !n. (n = 0) \/ (?m. n = SUC m)
```

Case-splitting consists of specialising the cases theorem with the
variable from the goal and then generating as many sub-goals as there
are disjuncts in the cases theorem, where in each sub-goal (including
the assumptions) the variable has been replaced by an expression
involving the given 'constructor' (the `Ci`'s above) applied to as many
fresh variables as appropriate.

### Failure

Fails if the goal is not universally quantified, or if the type of the
universally quantified variable does not have a case theorem in the
`TypeBase`, as will happen, for example, with variable types.

### Example

If we have defined the following type:

``` hol4
   - Hol_datatype `foo = Bar of num | Baz of bool`;
   > val it = () : unit
```

and the following function:

``` hol4
   - val foofn_def = Define `(foofn (Bar n) = n + 10) /\
                             (foofn (Baz x) = 10)`;
   > val foofn_def =
       |- (!n. foofn (Bar n) = n + 10) /\
           !x. foofn (Baz x) = 10 : thm
```

then it is possible to make progress with the goal `!x. foofn x >= 10`
by applying the tactic `Cases`, thus:

``` hol4
                    ?- !x. foofn x >= 10
   ======================================================  Cases
    ?- foofn (Bar n) >= 10        ?- foofn (Baz b) >= 10
```

producing two new goals, one for each constructor of the type.

### See also

[`bossLib.Cases_on`](#bossLib.Cases_on),
[`bossLib.Induct`](#bossLib.Induct),
[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)
