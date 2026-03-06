## `PEXISTS_AND_CONV`

``` hol4
PairRules.PEXISTS_AND_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification inwards through a conjunction.

When applied to a term of the form `?p. t /\ u`, where variables in `p`
are not free in both `t` and `u`, `PEXISTS_AND_CONV` returns a theorem
of one of three forms, depending on occurrences of variables from `p` in
`t` and `u`. If `p` contains variables free in `t` but none in `u`, then
the theorem:

``` hol4
   |- (?p. t /\ u) = (?p. t) /\ u
```

is returned. If `p` contains variables free in `u` but none in `t`, then
the result is:

``` hol4
   |- (?p. t /\ u) = t /\ (?x. u)
```

And if `p` does not contain any variable free in either `t` nor `u`,
then the result is:

``` hol4
   |- (?p. t /\ u) = (?x. t) /\ (?x. u)
```

### Failure

`PEXISTS_AND_CONV` fails if it is applied to a term not of the form
`?p. t /\ u`, or if it is applied to a term `?p. t /\ u` in which
variables in `p` are free in both `t` and `u`.

### See also

[`Conv.EXISTS_AND_CONV`](#Conv.EXISTS_AND_CONV),
[`PairRules.AND_PEXISTS_CONV`](#PairRules.AND_PEXISTS_CONV),
[`PairRules.LEFT_AND_PEXISTS_CONV`](#PairRules.LEFT_AND_PEXISTS_CONV),
[`PairRules.RIGHT_AND_PEXISTS_CONV`](#PairRules.RIGHT_AND_PEXISTS_CONV)
