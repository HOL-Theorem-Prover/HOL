## `PRUNE_CONV`

``` hol4
unwindLib.PRUNE_CONV : conv
```

------------------------------------------------------------------------

Prunes all hidden variables.

`PRUNE_CONV "?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp"`
returns a theorem of the form:

``` hol4
   |- (?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp) =
      (t1 /\ ... /\ tp)
```

where each `eqni` has the form `"!y1 ... ym. li x1 ... xn = b"` and `li`
does not appear free in any of the other conjuncts or in `b`. The
conversion works if one or more of the `eqni`'s are not present, that is
if `li` is not free in any of the conjuncts, but does not work if `li`
appears free in more than one of the conjuncts. `p` may be zero, that
is, all the conjuncts may be `eqni`'s. In this case the result will be
simply `T` (true). Also, for each `eqni`, `m` and `n` may be zero.

### Failure

Fails if the argument term is not of the specified form or if any of the
`li`'s are free in more than one of the conjuncts or if the equation for
any `li` is recursive.

### Example

``` hol4
#PRUNE_CONV
# "?l2 l1.
#   (!(x:num). l1 x = F) /\ (!x. l2 x = ~(out x)) /\ (!(x:num). out x = T)";;
|- (?l2 l1. (!x. l1 x = F) /\ (!x. l2 x = ~out x) /\ (!x. out x = T)) =
   (!x. out x = T)
```

### See also

[`unwindLib.PRUNE_ONCE_CONV`](#unwindLib.PRUNE_ONCE_CONV),
[`unwindLib.PRUNE_ONE_CONV`](#unwindLib.PRUNE_ONE_CONV),
[`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV),
[`unwindLib.PRUNE_SOME_RIGHT_RULE`](#unwindLib.PRUNE_SOME_RIGHT_RULE),
[`unwindLib.PRUNE_RIGHT_RULE`](#unwindLib.PRUNE_RIGHT_RULE)
