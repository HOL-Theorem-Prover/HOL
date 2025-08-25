## `PairCases_on`

``` hol4
pairLib.PairCases_on : term quotation -> tactic
```

------------------------------------------------------------------------

Recursively split variables of product type.

An application `PairCases_on q` first parses `q` in the context of the
goal to obtain `v`, which should be a variable of product type. Then, it
introduces new variables of the form `v`n, where n is a number,
representing the atomic components of `v` after all nested pair
structure is expanded away. Finally, all occurrences of `v` in the goal
(including in the assumptions) are replaced by the explicit pair
structure (with the new variables at its leaves).

The new variables are numbered from zero according to a depth-first
traversal. (Therefore, they should appear in increasing order from left
to right when the tree is pretty-printed.) Primed variants of the new
numbered variables are used if necessary (i.e. `v`n already occurs free
in the goal).

### Failure

Fails if `v` is not a variable of product type.

### Example

> val PairCases_on = pairLib.PairCases_on; g('(x = y) ==\>
> ((x:((bool#bool)#bool#(bool#((bool#bool)#bool))))=z)');

Initial goal:

(x = y) ==\> (x = z)

> e(DISCH_TAC); OK.. 1 subgoal:

## x = z

x = y

> e(PairCases_on 'y'); OK.. 1 subgoal:

## x = z

x = ((y0,y1),y2,y3,(y4,y5),y6)

> e(PairCases_on'x'); OK.. 1 subgoal:

## ((x0,x1),x2,x3,(x4,x5),x6) = z

((x0,x1),x2,x3,(x4,x5),x6) = ((y0,y1),y2,y3,(y4,y5),y6)

### See also

[`Tactic.FULL_STRUCT_CASES_TAC`](#Tactic.FULL_STRUCT_CASES_TAC),
[`Conv.RENAME_VARS_CONV`](#Conv.RENAME_VARS_CONV)
