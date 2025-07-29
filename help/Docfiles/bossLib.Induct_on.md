## `Induct_on`

``` hol4
bossLib.Induct_on : term quotation -> tactic
```

------------------------------------------------------------------------

Performs structural induction, using the type of the given term.

Given a term `M`, `Induct_on` attempts to perform an induction based on
the type of `M`. The induction theorem to be used is extracted from the
`TypeBase` database, which holds useful facts about the system's defined
types.

`Induct_on` can be used to specify variables that are buried in the
quantifier prefix, i.e., not the leading quantified variable.
`Induct_on` can also perform induction on non-variable terms. If `M` is
a non-variable term that does not occur bound in the goal, then
`Induct_on` equates `M` to a new variable `v` (one not occurring in the
goal), moves all hypotheses in which free variables of `M` occur to the
conclusion of the goal, adds the antecedent `v = M`, and quantifies all
free variables of `M` before universally quantifying `v` and then
finally inducting on `v`.

`Induct_on` may also be used to apply an induction theorem coming from
declaration of a mutually recursive datatype.

### Failure

`Induct_on` fails if an induction theorem corresponding to the type of
`M` is not found in the `TypeBase` database.

### Example

If attempting to prove

``` hol4
   !x. LENGTH (REVERSE x) = LENGTH x
```

one can apply `` Induct_on `x` `` to begin a proof by induction on the
list structure of `x`. In this case, `Induct_on` serves as an explicit
version of `Induct`.

### See also

[`bossLib.Induct`](#bossLib.Induct),
[`bossLib.completeInduct_on`](#bossLib.completeInduct_on),
[`bossLib.measureInduct_on`](#bossLib.measureInduct_on),
[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`bossLib.Cases`](#bossLib.Cases),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype),
[`proofManagerLib.g`](#proofManagerLib.g),
[`proofManagerLib.e`](#proofManagerLib.e)
