## `UNWIND_ALL_BUT_CONV`

``` hol4
unwindLib.UNWIND_ALL_BUT_CONV : (string list -> conv)
```

------------------------------------------------------------------------

Unwinds all lines of a device (except those in the argument list) as
much as possible.

`UNWIND_ALL_BUT_CONV l` when applied to the following term:

``` hol4
   "t1 /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn"
```

returns a theorem of the form:

``` hol4
   |- t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn =
      t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn'
```

where `ti'` (for `1 <= i <= n`) is `ti` rewritten with the equations
`eqni` (`1 <= i <= m`). These equations are those conjuncts with line
name not in `l` (and which are equations).

### Failure

Never fails but may loop indefinitely.

### Example

``` hol4
#UNWIND_ALL_BUT_CONV [`l2`]
# "(!(x:num). l1 x = (l2 x) - 1) /\
#  (!x. f x = (l2 (x+1)) + (l1 (x+2))) /\
#  (!x. l2 x = 7)";;
|- (!x. l1 x = (l2 x) - 1) /\
   (!x. f x = (l2(x + 1)) + (l1(x + 2))) /\
   (!x. l2 x = 7) =
   (!x. l1 x = (l2 x) - 1) /\
   (!x. f x = (l2(x + 1)) + ((l2(x + 2)) - 1)) /\
   (!x. l2 x = 7)
```

### See also

[`unwindLib.UNWIND_ONCE_CONV`](#unwindLib.UNWIND_ONCE_CONV),
[`unwindLib.UNWIND_CONV`](#unwindLib.UNWIND_CONV),
[`unwindLib.UNWIND_AUTO_CONV`](#unwindLib.UNWIND_AUTO_CONV),
[`unwindLib.UNWIND_ALL_BUT_RIGHT_RULE`](#unwindLib.UNWIND_ALL_BUT_RIGHT_RULE),
[`unwindLib.UNWIND_AUTO_RIGHT_RULE`](#unwindLib.UNWIND_AUTO_RIGHT_RULE)
