## `PRUNE_SOME_RIGHT_RULE`

``` hol4
unwindLib.PRUNE_SOME_RIGHT_RULE : (string list -> thm -> thm)
```

------------------------------------------------------------------------

Prunes several hidden variables.

`` PRUNE_SOME_RIGHT_RULE [`li1`;...;`lik`] `` behaves as follows:

``` hol4
    A |- !z1 ... zr.
          t = ?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp
   -----------------------------------------------------------------------
           A |- !z1 ... zr. t = ?li(k+1) ... lir. t1 /\ ... /\ tp
```

where for `1 <= j <= k`, each `eqnij` has the form:

``` hol4
   "!y1 ... ym. lij x1 ... xn = b"
```

and `lij` does not appear free in any of the other conjuncts or in `b`.
The `li`'s are related by the equation:

``` hol4
   {{li1,...,lik}} u {{li(k+1),...,lir}} = {{l1,...,lr}}
```

The rule works if one or more of the `eqnij`'s are not present, that is
if `lij` is not free in any of the conjuncts, but does not work if `lij`
appears free in more than one of the conjuncts. `p` may be zero, that
is, all the conjuncts may be `eqnij`'s. In this case the conjunction
will be transformed to `T` (true). Also, for each `eqnij`, `m` and `n`
may be zero.

If there is more than one line with a specified name (but with different
types), the one that appears outermost in the existential
quantifications is pruned. If such a line name is mentioned twice in the
list, the two outermost occurrences of lines with that name will be
pruned, and so on.

### Failure

Fails if the argument theorem is not of the specified form or if any of
the `lij`'s are free in more than one of the conjuncts or if the
equation for any `lij` is recursive. The function also fails if any of
the specified lines are not one of the existentially quantified lines.

### Example

``` hol4
#PRUNE_SOME_RIGHT_RULE [`l1`;`l2`]
# (ASSUME
#   "!(in:num->bool) (out:num->bool).
#     DEV (in,out) =
#      ?(l1:num->bool) l2.
#       (!x. l1 x = F) /\ (!x. l2 x = ~(in x)) /\ (!x. out x = ~(in x))");;
. |- !in out. DEV(in,out) = (!x. out x = ~in x)
```

### See also

[`unwindLib.PRUNE_RIGHT_RULE`](#unwindLib.PRUNE_RIGHT_RULE),
[`unwindLib.PRUNE_ONCE_CONV`](#unwindLib.PRUNE_ONCE_CONV),
[`unwindLib.PRUNE_ONE_CONV`](#unwindLib.PRUNE_ONE_CONV),
[`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV),
[`unwindLib.PRUNE_CONV`](#unwindLib.PRUNE_CONV)
