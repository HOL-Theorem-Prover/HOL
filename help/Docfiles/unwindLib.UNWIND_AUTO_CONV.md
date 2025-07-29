## `UNWIND_AUTO_CONV`

``` hol4
unwindLib.UNWIND_AUTO_CONV : conv
```

------------------------------------------------------------------------

Automatic unwinding of equations defining wire values in a standard
device specification.

`UNWIND_AUTO_CONV "?l1 ... lm. t1 /\ ... /\ tn"` returns a theorem of
the form:

``` hol4
   |- (?l1 ... lm. t1 /\ ... /\ tn) = (?l1 ... lm. t1' /\ ... /\ tn')
```

where `tj'` is `tj` rewritten with equations selected from the `ti`'s.

The function decides which equations to use for rewriting by performing
a loop analysis on the graph representing the dependencies of the lines.
By this means the term can be unwound as much as possible without the
risk of looping. The user is left to deal with the recursive equations.

### Failure

Fails if there is more than one equation for any line variable.

### Example

``` hol4
#UNWIND_AUTO_CONV
# "(!(x:num). l1 x = (l2 x) - 1) /\
#  (!x. f x = (l2 (x+1)) + (l1 (x+2))) /\
#  (!x. l2 x = 7)";;
|- (!x. l1 x = (l2 x) - 1) /\
   (!x. f x = (l2(x + 1)) + (l1(x + 2))) /\
   (!x. l2 x = 7) =
   (!x. l1 x = 7 - 1) /\ (!x. f x = 7 + (7 - 1)) /\ (!x. l2 x = 7)
```

### See also

[`unwindLib.UNWIND_ONCE_CONV`](#unwindLib.UNWIND_ONCE_CONV),
[`unwindLib.UNWIND_CONV`](#unwindLib.UNWIND_CONV),
[`unwindLib.UNWIND_ALL_BUT_CONV`](#unwindLib.UNWIND_ALL_BUT_CONV),
[`unwindLib.UNWIND_ALL_BUT_RIGHT_RULE`](#unwindLib.UNWIND_ALL_BUT_RIGHT_RULE),
[`unwindLib.UNWIND_AUTO_RIGHT_RULE`](#unwindLib.UNWIND_AUTO_RIGHT_RULE)
