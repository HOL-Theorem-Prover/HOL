## `line_var`

``` hol4
unwindLib.line_var : (term -> term)
```

------------------------------------------------------------------------

Computes the line variable of an equation.

`line_var "!y1 ... ym. f x1 ... xn = t"` returns the variable `"f"`.

### Failure

Fails if the argument term is not of the specified form.

### See also

[`unwindLib.line_name`](#unwindLib.line_name)
