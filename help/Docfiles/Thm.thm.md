## `thm`

``` hol4
Thm.type thm
```

------------------------------------------------------------------------

Type of theorems of the HOL logic.

The abstract type `thm` represents the theorems derivable by inference
in the HOL logic. The type of theorems can be viewed as the inductive
closure of the axioms of the HOL logic by the primitive inference rules
of HOL. Robin Milner had the brilliant insight to implement this view by
encapsulating the primitive rules of inference for a logic as the
constructors for an abstract type of theorems. This implementation
technique is adopted in HOL.

### See also

[`Thm.dest_thm`](#Thm.dest_thm), [`Thm.hyp`](#Thm.hyp),
[`Thm.concl`](#Thm.concl), [`Thm.tag`](#Thm.tag),
[`Thm.ASSUME`](#Thm.ASSUME), [`Thm.REFL`](#Thm.REFL),
[`Thm.BETA_CONV`](#Thm.BETA_CONV), [`Thm.ABS`](#Thm.ABS),
[`Thm.DISCH`](#Thm.DISCH), [`Thm.MP`](#Thm.MP),
[`Thm.SUBST`](#Thm.SUBST), [`Thm.INST_TYPE`](#Thm.INST_TYPE)
