## `COND_REWRITE1_CONV`

``` hol4
Cond_rewrite.COND_REWRITE1_CONV : thm list -> thm -> conv
```

------------------------------------------------------------------------

A simple conditional rewriting conversion.

`COND_REWRITE1_CONV` is a front end of the conditional rewriting
conversion `COND_REWR_CONV`. The input theorem should be in the
following form

``` hol4
   A |- !x11 ... . P1 ==> ... !xm1 ... . Pm ==> (!x ... . Q = R)
```

where each antecedent `Pi` itself may be a conjunction or disjunction.
This theorem is transformed to a standard form expected by
`COND_REWR_CONV` which carries out the actual rewriting. The
transformation is performed by `COND_REWR_CANON`. The search function
passed to `COND_REWR_CONV` is `search_top_down`. The effect of applying
the conversion `COND_REWRITE1_CONV ths th` to a term `tm` is to derive a
theorem

``` hol4
  A' |- tm = tm[R'/Q']
```

where the right hand side of the equation is obtained by rewriting the
input term `tm` with an instance of the conclusion of the input theorem.
The theorems in the list `ths` are used to discharge the assumptions
generated from the antecedents of the input theorem.

### Failure

`COND_REWRITE1_CONV ths th` fails if `th` cannot be transformed into the
required form by `COND_REWR_CANON`. Otherwise, it fails if no match is
found or the theorem cannot be instantiated.

### Example

The following example illustrates a straightforward use of
`COND_REWRITE1_CONV`. We use the built-in theorem `LESS_MOD` as the
input theorem.

``` hol4
   #LESS_MOD;;
   Theorem LESS_MOD autoloading from theory `arithmetic` ...
   LESS_MOD = |- !n k. k < n ==> (k MOD n = k)

   |- !n k. k < n ==> (k MOD n = k)

   #COND_REWRITE1_CONV [] LESS_MOD "2 MOD 3";;
   2 < 3 |- 2 MOD 3 = 2

   #let less_2_3 = REWRITE_RULE[LESS_MONO_EQ;LESS_0]
   #(REDEPTH_CONV num_CONV "2 < 3");;
   less_2_3 = |- 2 < 3

   #COND_REWRITE1_CONV [less_2_3] LESS_MOD "2 MOD 3";;
   |- 2 MOD 3 = 2
```

In the first example, an empty theorem list is supplied to
`COND_REWRITE1_CONV` so the resulting theorem has an assumption `2 < 3`.
In the second example, a list containing a theorem `|- 2 < 3` is
supplied, the resulting theorem has no assumptions.

### See also

[`Cond_rewrite.COND_REWR_TAC`](#Cond_rewrite.COND_REWR_TAC),
[`Cond_rewrite.COND_REWRITE1_TAC`](#Cond_rewrite.COND_REWRITE1_TAC),
[`Cond_rewrite.COND_REWR_CONV`](#Cond_rewrite.COND_REWR_CONV),
[`Cond_rewrite.COND_REWR_CANON`](#Cond_rewrite.COND_REWR_CANON),
[`Cond_rewrite.search_top_down`](#Cond_rewrite.search_top_down)
