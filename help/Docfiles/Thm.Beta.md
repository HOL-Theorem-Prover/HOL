## `Beta`

``` hol4
Thm.Beta : thm -> thm
```

------------------------------------------------------------------------

Perform one step of beta-reduction on the right hand side of an
equational theorem.

`Beta` performs a single beta-reduction step on the right-hand side of
an equational theorem.

``` hol4
   A |- t = ((\x.M) N)
  --------------------- Beta
   A |- t = M [N/x]
```

### Failure

If the theorem is not an equation, or if the right hand side of the
equation is not a beta-redex.

### Example

``` hol4
val th = REFL (Term `(K:'a ->'b->'a) x`);
> val th = |- K x = K x : thm

- SUBS_OCCS [([2],combinTheory.K_DEF)] th;
> val it = |- K x = (\x y. x) x : thm

- Beta it;
> val it = |- K x = (\y. x) : thm
```

### Comments

`Beta` is equivalent to `RIGHT_BETA` but faster.

### See also

[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA),
[`Drule.ETA_CONV`](#Drule.ETA_CONV)
