## `UNWIND_ALL_BUT_RIGHT_RULE`

``` hol4
unwindLib.UNWIND_ALL_BUT_RIGHT_RULE : (string list -> thm -> thm)
```

------------------------------------------------------------------------

Unwinds all lines of a device (except those in the argument list) as
much as possible.

`UNWIND_ALL_BUT_RIGHT_RULE l` behaves as follows:

``` hol4
    A |- !z1 ... zr.
          t =
          (?l1 ... lp. t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn)
   ---------------------------------------------------------------------
    A |- !z1 ... zr.
          t =
          (?l1 ... lp. t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn')
```

where `ti'` (for `1 <= i <= n`) is `ti` rewritten with the equations
`eqni` (`1 <= i <= m`). These equations are those conjuncts with line
name not in `l` (and which are equations).

### Failure

Fails if the argument theorem is not of the required form, though either
or both of `p` and `r` may be zero. May loop indefinitely.

### Example

``` hol4
#UNWIND_ALL_BUT_RIGHT_RULE [`l2`]
# (ASSUME
#   "!f. IMP(f) =
#     ?l2 l1.
#      (!(x:num). l1 x = (l2 x) - 1) /\
#      (!x. f x = (l2 (x+1)) + (l1 (x+2))) /\
#      (!x. l2 x = 7)");;
. |- !f.
      IMP f =
      (?l2 l1.
        (!x. l1 x = (l2 x) - 1) /\
        (!x. f x = (l2(x + 1)) + ((l2(x + 2)) - 1)) /\
        (!x. l2 x = 7))
```

### See also

[`unwindLib.UNWIND_AUTO_RIGHT_RULE`](#unwindLib.UNWIND_AUTO_RIGHT_RULE),
[`unwindLib.UNWIND_ALL_BUT_CONV`](#unwindLib.UNWIND_ALL_BUT_CONV),
[`unwindLib.UNWIND_AUTO_CONV`](#unwindLib.UNWIND_AUTO_CONV),
[`unwindLib.UNWIND_ONCE_CONV`](#unwindLib.UNWIND_ONCE_CONV),
[`unwindLib.UNWIND_CONV`](#unwindLib.UNWIND_CONV)
