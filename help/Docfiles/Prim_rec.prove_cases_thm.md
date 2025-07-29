## `prove_cases_thm`

``` hol4
Prim_rec.prove_cases_thm : (thm -> thm)
```

------------------------------------------------------------------------

Proves a structural cases theorem for an automatically-defined concrete
type.

`prove_cases_thm` takes as its argument a structural induction theorem,
in the form returned by `prove_induction_thm` for an
automatically-defined concrete type. When applied to such a theorem,
`prove_cases_thm` automatically proves and returns a theorem which
states that every value the concrete type in question is denoted by the
value returned by some constructor of the type.

### Failure

Fails if the argument is not a theorem of the form returned by
`prove_induction_thm`

### Example

Given the following structural induction theorem for labelled binary
trees:

``` hol4
   |- !P. (!x. P(LEAF x)) /\ (!b1 b2. P b1 /\ P b2 ==> P(NODE b1 b2)) ==>
          (!b. P b)
```

`prove_cases_thm` proves and returns the theorem:

``` hol4
   |- !b. (?x. b = LEAF x) \/ (?b1 b2. b = NODE b1 b2)
```

This states that every labelled binary tree `b` is either a leaf node
with a label `x` or a tree with two subtrees `b1` and `b2`.

### See also

[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition),
[`Prim_rec.prove_constructors_distinct`](#Prim_rec.prove_constructors_distinct),
[`Prim_rec.prove_constructors_one_one`](#Prim_rec.prove_constructors_one_one),
[`Prim_rec.prove_induction_thm`](#Prim_rec.prove_induction_thm),
[`Prim_rec.prove_rec_fn_exists`](#Prim_rec.prove_rec_fn_exists)
