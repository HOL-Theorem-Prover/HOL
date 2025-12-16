## `tactictoe`

``` hol4
tacticToe.tactictoe : term -> thm
```

------------------------------------------------------------------------

A call to the rule `tacticToe.tactictoe` on a term `tm` is equivalent to
a call to the tactic `tacticToe.ttt` on the goal `([],tm)`.

### See also

[`tacticToe.ttt`](#tacticToe.ttt)
