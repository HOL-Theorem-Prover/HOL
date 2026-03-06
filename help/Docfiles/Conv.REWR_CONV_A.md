## `REWR_CONV_A`

``` hol4
Conv.REWR_CONV_A : (thm -> conv)
```

------------------------------------------------------------------------

Uses an instance of a given equation to rewrite a term.

`REWR_CONV_A th` behaves as `REWR_CONV th` except that it allows
substitution of variables or type variables which appear in the
hypotheses of `th`.

### Example

Consider the theorem `th`

``` hol4
   [0 < n] |- (a * n = b * (n : int)) <=> (a = b)
```

and the term `tm`

``` hol4
   f (a * m = b * (m : int)) x
```

Then `DEPTH_CONV (REWR_CONV_A th) tm` returns

``` hol4
   [0 < m] |- f (a * m = b * m) x <=> f (a = b) x
```

Likewise, when the goal is `tm` above,
`e (VALIDATE (CONV_TAC (DEPTH_CONV (REWR_CONV_A th))))` gives the two
subgoals:

``` hol4
      f (a = b) x

      0 < m
```

### See also

[`Conv.REWR_CONV`](#Conv.REWR_CONV),
[`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV),
[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV),
[`Tactic.CONV_TAC`](#Tactic.CONV_TAC),
[`Tactical.VALIDATE`](#Tactical.VALIDATE)
