## `UNWIND_CONV`

``` hol4
unwindLib.UNWIND_CONV : ((term -> bool) -> conv)
```

------------------------------------------------------------------------

Unwinds device behaviour using selected line equations until no change.

`UNWIND_CONV p "t1 /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn"` returns
a theorem of the form:

``` hol4
   |- t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn =
      t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn'
```

where `ti'` (for `1 <= i <= n`) is `ti` rewritten with the equations
`eqni` (`1 <= i <= m`). These equations are the conjuncts for which the
predicate `p` is true. The `ti` terms are the conjuncts for which `p` is
false. The rewriting is repeated until no changes take place.

### Failure

Never fails but may loop indefinitely.

### Example

``` hol4
#UNWIND_CONV (\tm. mem (line_name tm) [`l1`;`l2`])
# "(!(x:num). l1 x = (l2 x) - 1) /\
#  (!x. f x = (l2 (x+1)) + (l1 (x+2))) /\
#  (!x. l2 x = 7)";;
|- (!x. l1 x = (l2 x) - 1) /\
   (!x. f x = (l2(x + 1)) + (l1(x + 2))) /\
   (!x. l2 x = 7) =
   (!x. l1 x = (l2 x) - 1) /\ (!x. f x = 7 + (7 - 1)) /\ (!x. l2 x = 7)
```

### See also

[`unwindLib.UNWIND_ONCE_CONV`](#unwindLib.UNWIND_ONCE_CONV),
[`unwindLib.UNWIND_ALL_BUT_CONV`](#unwindLib.UNWIND_ALL_BUT_CONV),
[`unwindLib.UNWIND_AUTO_CONV`](#unwindLib.UNWIND_AUTO_CONV),
[`unwindLib.UNWIND_ALL_BUT_RIGHT_RULE`](#unwindLib.UNWIND_ALL_BUT_RIGHT_RULE),
[`unwindLib.UNWIND_AUTO_RIGHT_RULE`](#unwindLib.UNWIND_AUTO_RIGHT_RULE)
