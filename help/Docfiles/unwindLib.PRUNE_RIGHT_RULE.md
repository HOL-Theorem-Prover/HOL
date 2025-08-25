## `PRUNE_RIGHT_RULE`

``` hol4
unwindLib.PRUNE_RIGHT_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Prunes all hidden variables.

`PRUNE_RIGHT_RULE` behaves as follows:

``` hol4
    A |- !z1 ... zr.
          t = ?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp
   ---------------------------------------------------------------------
                   A |- !z1 ... zr. t = t1 /\ ... /\ tp
```

where each `eqni` has the form `"!y1 ... ym. li x1 ... xn = b"` and `li`
does not appear free in any of the other conjuncts or in `b`. The rule
works if one or more of the `eqni`'s are not present, that is if `li` is
not free in any of the conjuncts, but does not work if `li` appears free
in more than one of the conjuncts. `p` may be zero, that is, all the
conjuncts may be `eqni`'s. In this case the result will be simply `T`
(true). Also, for each `eqni`, `m` and `n` may be zero.

### Failure

Fails if the argument theorem is not of the specified form or if any of
the `li`'s are free in more than one of the conjuncts or if the equation
for any `li` is recursive.

### Example

``` hol4
#PRUNE_RIGHT_RULE
# (ASSUME
#   "!(in:num->bool) (out:num->bool).
#     DEV (in,out) =
#      ?(l1:num->bool) l2.
#       (!x. l1 x = F) /\ (!x. l2 x = ~(in x)) /\ (!x. out x = ~(in x))");;
. |- !in out. DEV(in,out) = (!x. out x = ~in x)
```

### See also

[`unwindLib.PRUNE_SOME_RIGHT_RULE`](#unwindLib.PRUNE_SOME_RIGHT_RULE),
[`unwindLib.PRUNE_ONCE_CONV`](#unwindLib.PRUNE_ONCE_CONV),
[`unwindLib.PRUNE_ONE_CONV`](#unwindLib.PRUNE_ONE_CONV),
[`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV),
[`unwindLib.PRUNE_CONV`](#unwindLib.PRUNE_CONV)
