## `UNWIND_ONCE_CONV`

``` hol4
unwindLib.UNWIND_ONCE_CONV : ((term -> bool) -> conv)
```

------------------------------------------------------------------------

Basic conversion for parallel unwinding of equations defining wire
values in a standard device specification.

`UNWIND_ONCE_CONV p tm` unwinds the conjunction `tm` using the equations
selected by the predicate `p`. `tm` should be a conjunction, equivalent
under associative-commutative reordering to:

``` hol4
   t1 /\ t2 /\ ... /\ tn
```

`p` is used to partition the terms `ti` for `1 <= i <= n` into two
disjoint sets:

``` hol4
   REW = {{ti | p ti}}
   OBJ = {{ti | ~p ti}}
```

The terms `ti` for which `p` is true are then used as a set of rewrite
rules (thus they should be equations) to do a single top-down parallel
rewrite of the remaining terms. The rewritten terms take the place of
the original terms in the input conjunction. For example, if `tm` is:

``` hol4
   t1 /\ t2 /\ t3 /\ t4
```

and `REW = {{t1,t3}}` then the result is:

``` hol4
   |- t1 /\ t2 /\ t3 /\ t4 = t1 /\ t2' /\ t3 /\ t4'
```

where `ti'` is `ti` rewritten with the equations `REW`.

### Failure

Never fails.

### Example

``` hol4
> UNWIND_ONCE_CONV (fn tm => mem (line_name tm) [`l1`,`l2`])
   “(!(x:num). l1 x = (l2 x) - 1) /\
    (!x. f x = (l2 (x+1)) + (l1 (x+2))) /\
    (!x. l2 x = 7)”;
|- (!x. l1 x = (l2 x) - 1) /\
   (!x. f x = (l2(x + 1)) + (l1(x + 2))) /\
   (!x. l2 x = 7) =
   (!x. l1 x = (l2 x) - 1) /\
   (!x. f x = 7 + ((l2(x + 2)) - 1)) /\
   (!x. l2 x = 7)
```

### See also

[`unwindLib.UNWIND_CONV`](#unwindLib.UNWIND_CONV),
[`unwindLib.UNWIND_ALL_BUT_CONV`](#unwindLib.UNWIND_ALL_BUT_CONV),
[`unwindLib.UNWIND_AUTO_CONV`](#unwindLib.UNWIND_AUTO_CONV),
[`unwindLib.UNWIND_ALL_BUT_RIGHT_RULE`](#unwindLib.UNWIND_ALL_BUT_RIGHT_RULE),
[`unwindLib.UNWIND_AUTO_RIGHT_RULE`](#unwindLib.UNWIND_AUTO_RIGHT_RULE)
