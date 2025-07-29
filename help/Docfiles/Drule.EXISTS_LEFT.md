## `EXISTS_LEFT`

``` hol4
Drule.EXISTS_LEFT : term list -> thm -> thm
```

------------------------------------------------------------------------

Existentially quantifes hypotheses of a theorem.

In this example, assume that `h1` and `h3` (only) involve the free
variable `x`.

``` hol4
      h1, h2, h3 |- t
   --------------------- EXISTS_LEFT [``x``]
   ?x. h1 /\ h3, h2 |- t
```

### Failure

`EXISTS_LEFT` will fail if the term list supplied does not consist only
of free variables

### Example

Where `th` is `[p, q, g x, h y, f x y] |- r`, and `fvx` and `fvy` are
``` ``x`` ``` and ``` ``y`` ```,

`EXISTS_LEFT [fvx, fvy] th` is
`[p, q, ?y. (?x. g x /\ f x y) /\ h y] |- r`

`EXISTS_LEFT [fvy, fvx] th` is
`[p, q, ?x. (?y. h y /\ f x y) /\ g x] |- r`

Where `EQ_TRANS` is `[] |- !x y z. (x = y) /\ (y = z) ==> (x = z)` and
the current goal is `a = b`, the tactic `MATCH_MP_TAC EQ_TRANS` gives a
new goal `?y. (a = y) /\ (y = b)` by virtue of the smart features built
into `MATCH_MP_TAC`.

Where `trans_thm` is `[] |- !x y z. (x = y) ==> (y = z) ==> (x = z)` the
same result could of course be achieved by rewriting it with
`AND_IMP_INTRO`. But more generally, `EXISTS_LEFT` could be used as a
building-block for a more flexible tactic. In this instance, one might
start with

``` hol4
val trans_thm_h = UNDISCH_ALL (SPEC_ALL trans_thm) ;
EXISTS_LEFT (thm_frees trans_thm_h) trans_thm_h ;
```

giving `[?y. (x = y) /\ (y = z)] |- x = z`

### See also

[`Drule.EXISTS_LEFT1`](#Drule.EXISTS_LEFT1),
[`Thm.CHOOSE`](#Thm.CHOOSE), [`Thm.EXISTS`](#Thm.EXISTS),
[`Tactic.CHOOSE_TAC`](#Tactic.CHOOSE_TAC),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
