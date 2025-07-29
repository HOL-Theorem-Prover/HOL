## `PRUNE_ONE_CONV`

``` hol4
unwindLib.PRUNE_ONE_CONV : (string -> conv)
```

------------------------------------------------------------------------

Prunes a specified hidden variable.

`` PRUNE_ONE_CONV `lj` `` when applied to the term:

``` hol4
   "?l1 ... lj ... lr. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp"
```

returns a theorem of the form:

``` hol4
   |- (?l1 ... lj ... lr. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp) =
      (?l1 ... l(j-1) l(j+1) ... lr. t1 /\ ... /\ ti /\ t(i+1) /\ ... /\ tp)
```

where `eq` has the form `"!y1 ... ym. lj x1 ... xn = b"` and `lj` does
not appear free in the `ti`'s or in `b`. The conversion works if `eq` is
not present, that is if `lj` is not free in any of the conjuncts, but
does not work if `lj` appears free in more than one of the conjuncts.
Each of `m`, `n` and `p` may be zero.

If there is more than one line with the specified name (but with
different types), the one that appears outermost in the existential
quantifications is pruned.

### Failure

Fails if the argument term is not of the specified form or if `lj` is
free in more than one of the conjuncts or if the equation for `lj` is
recursive. The function also fails if the specified line is not one of
the existentially quantified lines.

### Example

``` hol4
#PRUNE_ONE_CONV `l2` "?l2 l1. (!(x:num). l1 x = F) /\ (!x. l2 x = ~(l1 x))";;
|- (?l2 l1. (!x. l1 x = F) /\ (!x. l2 x = ~l1 x)) = (?l1. !x. l1 x = F)

#PRUNE_ONE_CONV `l1` "?l2 l1. (!(x:num). l1 x = F) /\ (!x. l2 x = ~(l1 x))";;
evaluation failed     PRUNE_ONE_CONV
```

### See also

[`unwindLib.PRUNE_ONCE_CONV`](#unwindLib.PRUNE_ONCE_CONV),
[`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV),
[`unwindLib.PRUNE_CONV`](#unwindLib.PRUNE_CONV),
[`unwindLib.PRUNE_SOME_RIGHT_RULE`](#unwindLib.PRUNE_SOME_RIGHT_RULE),
[`unwindLib.PRUNE_RIGHT_RULE`](#unwindLib.PRUNE_RIGHT_RULE)
