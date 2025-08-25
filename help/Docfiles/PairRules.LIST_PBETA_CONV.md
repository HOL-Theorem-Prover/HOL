## `LIST_PBETA_CONV`

``` hol4
PairRules.LIST_PBETA_CONV : conv
```

------------------------------------------------------------------------

Performs an iterated paired beta-conversion.

The conversion `LIST_PBETA_CONV` maps terms of the form

``` hol4
   (\p1 p2 ... pn. t) q1 q2 ... qn
```

to the theorems of the form

``` hol4
   |- (\p1 p2 ... pn. t) q1 q2 ... qn = t[q1/p1][q2/p2] ... [qn/pn]
```

where `t[qi/pi]` denotes the result of substituting `qi` for all free
occurrences of `pi` in `t`, after renaming sufficient bound variables to
avoid variable capture.

### Failure

`LIST_PBETA_CONV tm` fails if `tm` does not have the form
`(\p1 ... pn. t) q1 ... qn` for `n` greater than 0.

### Example

``` hol4
- LIST_PBETA_CONV (Term `(\(a,b) (c,d) . a + b + c + d) (1,2) (3,4)`);
> val it = |- (\(a,b) (c,d). a + b + c + d) (1,2) (3,4) = 1 + 2 + 3 + 4 : thm
```

### See also

[`Drule.LIST_BETA_CONV`](#Drule.LIST_BETA_CONV),
[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`Conv.BETA_RULE`](#Conv.BETA_RULE),
[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`PairRules.RIGHT_PBETA`](#PairRules.RIGHT_PBETA),
[`PairRules.RIGHT_LIST_PBETA`](#PairRules.RIGHT_LIST_PBETA),
[`PairRules.LEFT_PBETA`](#PairRules.LEFT_PBETA),
[`PairRules.LEFT_LIST_PBETA`](#PairRules.LEFT_LIST_PBETA)
