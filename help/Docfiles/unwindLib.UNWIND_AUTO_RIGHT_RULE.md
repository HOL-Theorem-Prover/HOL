## `UNWIND_AUTO_RIGHT_RULE`

``` hol4
unwindLib.UNWIND_AUTO_RIGHT_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Automatic unwinding of equations defining wire values in a standard
device specification.

`UNWIND_AUTO_RIGHT_RULE` behaves as follows:

``` hol4
    A |- !z1 ... zr. t = ?l1 ... lm. t1  /\ ... /\ tn
   ----------------------------------------------------
    A |- !z1 ... zr. t = ?l1 ... lm. t1' /\ ... /\ tn'
```

where `tj'` is `tj` rewritten with equations selected from the `ti`'s.

The function decides which equations to use for rewriting by performing
a loop analysis on the graph representing the dependencies of the lines.
By this means the term can be unwound as much as possible without the
risk of looping. The user is left to deal with the recursive equations.

### Failure

Fails if there is more than one equation for any line variable, or if
the argument theorem is not of the required form, though either or both
of `m` and `r` may be zero.

### Example

``` hol4
#UNWIND_AUTO_RIGHT_RULE
# (ASSUME
#   "!f. IMP(f) =
#     ?l2 l1.
#      (!(x:num). l1 x = (l2 x) - 1) /\
#      (!x. f x = (l2 (x+1)) + (l1 (x+2))) /\
#      (!x. l2 x = 7)");;
. |- !f.
      IMP f =
      (?l2 l1.
        (!x. l1 x = 7 - 1) /\ (!x. f x = 7 + (7 - 1)) /\ (!x. l2 x = 7))
```

### See also

[`unwindLib.UNWIND_ALL_BUT_RIGHT_RULE`](#unwindLib.UNWIND_ALL_BUT_RIGHT_RULE),
[`unwindLib.UNWIND_AUTO_CONV`](#unwindLib.UNWIND_AUTO_CONV),
[`unwindLib.UNWIND_ALL_BUT_CONV`](#unwindLib.UNWIND_ALL_BUT_CONV),
[`unwindLib.UNWIND_ONCE_CONV`](#unwindLib.UNWIND_ONCE_CONV),
[`unwindLib.UNWIND_CONV`](#unwindLib.UNWIND_CONV)
