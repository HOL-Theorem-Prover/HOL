## `COND_REWRITE1_TAC`

``` hol4
Cond_rewrite.COND_REWRITE1_TAC : thm_tactic
```

------------------------------------------------------------------------

A simple conditional rewriting tactic.

`COND_REWRITE1_TAC` is a front end of the conditional rewriting tactic
`COND_REWR_TAC`. The input theorem should be in the following form

``` hol4
   A |- !x11 ... . P1 ==> ... !xm1 ... . Pm ==> (!x ... . Q = R)
```

where each antecedent `Pi` itself may be a conjunction or disjunction.
This theorem is transformed to a standard form expected by
`COND_REWR_TAC` which carries out the actual rewriting. The
transformation is performed by `COND_REWR_CANON`. The search function
passed to `COND_REWR_TAC` is `search_top_down`. The effect of applying
this tactic is to substitute into the goal instances of the right hand
side of the conclusion of the input theorem `Ri'` for the corresponding
instances of the left hand side. The search is top-down left-to-right.
All matches found by the search function are substituted. New subgoals
corresponding to the instances of the antecedents which do not appear in
the assumption of the original goal are created. See manual page of
`COND_REWR_TAC` for details of how the instantiation and substitution
are done.

### Failure

`COND_REWRITE1_TAC th` fails if `th` cannot be transformed into the
required form by the function `COND_REWR_CANON`. Otherwise, it fails if
no match is found or the theorem cannot be instantiated.

### Example

The following example illustrates a straightforward use of
`COND_REWRITE1_TAC`. We use the built-in theorem `LESS_MOD` as the input
theorem.

``` hol4
   #LESS_MOD;;
   Theorem LESS_MOD autoloading from theory `arithmetic` ...
   LESS_MOD = |- !n k. k < n ==> (k MOD n = k)

   |- !n k. k < n ==> (k MOD n = k)
```

We set up a goal

``` hol4
   #g"2 MOD 3 = 2";;
   "2 MOD 3 = 2"

   () : void
```

and then apply the tactic

``` hol4
   #e(COND_REWRITE1_TAC LESS_MOD);;
   OK..
   2 subgoals
   "2 = 2"
       [ "2 < 3" ]

   "2 < 3"

   () : void
```

### See also

[`Cond_rewrite.COND_REWR_TAC`](#Cond_rewrite.COND_REWR_TAC),
[`Cond_rewrite.COND_REWRITE1_CONV`](#Cond_rewrite.COND_REWRITE1_CONV),
[`Cond_rewrite.COND_REWR_CONV`](#Cond_rewrite.COND_REWR_CONV),
[`Cond_rewrite.COND_REWR_CANON`](#Cond_rewrite.COND_REWR_CANON),
[`Cond_rewrite.search_top_down`](#Cond_rewrite.search_top_down)
