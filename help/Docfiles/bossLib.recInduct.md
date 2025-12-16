## `recInduct`

``` hol4
bossLib.recInduct : thm -> tactic
```

------------------------------------------------------------------------

Performs recursion induction.

An invocation `recInduct thm` on a goal `g`, where `thm` is typically an
induction scheme returned from an invocation of `Define` or `Hol_defn`,
attempts to match the consequent of `thm` to `g` and, if successful,
then replaces `g` by the instantiated antecedents of `thm`. The order of
quantification of the goal should correspond with the order of
quantification in the conclusion of `thm`.

### Failure

`recInduct` fails if the goal is not universally quantified in a way
corresponding with the quantification of the conclusion of `thm`.

### Example

Suppose we had introduced a function for incrementing a number until it
no longer can be found in a given list:

``` hol4
   variant x L = if MEM x L then variant (x + 1) L else x
```

Typically `Hol_defn` would be used to make such a definition, and some
subsequent proof would be required to establish termination. Once that
work was done, the specified recursion equations would be available as a
theorem and, as well, a corresponding induction theorem would also be
generated. In the case of `variant`, the induction theorem `variant_ind`
is

``` hol4
   |- !P. (!x L. (MEM x L ==> P (x + 1) L) ==> P x L) ==> !v v1. P v v1
```

Suppose now that we wish to prove that the variant with respect to a
list is not in the list:

``` hol4
   ?- !x L. ~MEM (variant x L) L`,
```

One could try mathematical induction, but that won't work well, since
`x` gets incremented in recursive calls. Instead, induction with
'`variant`-induction' works much better. `recInduct` can be used to
apply such theorems in tactic proof. For our example,
`recInduct variant_ind` yields the goal

``` hol4
   ?- !x L. (MEM x L ==> ~MEM (variant (x + 1) L) L) ==> ~MEM (variant x L) L
```

A few simple tactic applications then prove this goal.

### See also

[`bossLib.Induct`](#bossLib.Induct),
[`bossLib.Induct_on`](#bossLib.Induct_on),
[`bossLib.completeInduct_on`](#bossLib.completeInduct_on),
[`bossLib.measureInduct_on`](#bossLib.measureInduct_on),
[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`bossLib.Cases`](#bossLib.Cases),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype),
[`proofManagerLib.g`](#proofManagerLib.g),
[`proofManagerLib.e`](#proofManagerLib.e)
