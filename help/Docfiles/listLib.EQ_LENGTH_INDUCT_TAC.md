## `EQ_LENGTH_INDUCT_TAC`

``` hol4
listLib.EQ_LENGTH_INDUCT_TAC : tactic
```

------------------------------------------------------------------------

Performs tactical proof by structural induction on two equal length
lists.

`EQ_LENGTH_INDUCT_TAC` reduces a goal
`!x y . (LENGTH x = LENGTH y) ==> t[x,y]`, where `x` and `y` range over
lists, to two subgoals corresponding to the base and step cases in a
proof by induction on the length of `x` and `y`. The induction
hypothesis appears among the assumptions of the subgoal for the step
case. The specification of `EQ_LENGTH_INDUCT_TAC` is:

``` hol4
         A ?- !x y . (LENGTH x = LENGTH y) ==> t[x,y]
   ====================================================  EQ_LENGTH_INDUCT_TAC
                            A ?- t[NIL/x][NIL/y]
    A u {{LENGTH x = LENGTH y, t[x'/x, y'/y]}} ?-
         !h h'. t[(CONS h x)/x, (CONS h' y)/y]
```

### Failure

`EQ_LENGTH_INDUCT_TAC g` fails unless the conclusion of the goal `g` has
the form

``` hol4
   !x y . (LENGTH x = LENGTH y) ==> t[x,y]
```

where the variables `x` and `y` have types `(xty)list` and `(yty)list`
for some types `xty` and `yty`. It also fails if either of the variables
`x` or `y` appear free in the assumptions.

Use this tactic to perform structural induction over two lists that have
identical length.

### See also

[`listLib.LIST_INDUCT_TAC`](#listLib.LIST_INDUCT_TAC),
[`listLib.SNOC_INDUCT_TAC`](#listLib.SNOC_INDUCT_TAC),
[`listLib.EQ_LENGTH_SNOC_INDUCT_TAC`](#listLib.EQ_LENGTH_SNOC_INDUCT_TAC)
