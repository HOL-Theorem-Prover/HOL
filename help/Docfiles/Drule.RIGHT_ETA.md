## `RIGHT_ETA`

``` hol4
Drule.RIGHT_ETA : thm -> thm
```

------------------------------------------------------------------------

Perform one step of eta-reduction on the right hand side of an
equational theorem.

``` hol4
    A |- M = (\x. (N x))
   ---------------------   x not free in N
    A |- M = N
```

### Failure

If the right hand side of the equation is not an eta-redex, or if the
theorem is not an equation.

### Example

``` hol4
- val INC_DEF = new_definition ("INC_DEF", Term`INC = \x. 1 + x`);
> val INC_DEF = |- INC = (\x. 1 + x) : thm

- RIGHT_ETA INC_DEF;
> val it = |- INC = $+ 1 : thm
```

### See also

[`Drule.ETA_CONV`](#Drule.ETA_CONV), [`Term.eta_conv`](#Term.eta_conv)
