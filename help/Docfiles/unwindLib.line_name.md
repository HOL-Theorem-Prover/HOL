## `line_name`

``` hol4
unwindLib.line_name : (term -> string)
```

------------------------------------------------------------------------

Computes the line name of an equation.

`line_name "!y1 ... ym. f x1 ... xn = t"` returns the string `` `f` ``.

### Failure

Fails if the argument term is not of the specified form.

### See also

[`unwindLib.line_var`](#unwindLib.line_var)
