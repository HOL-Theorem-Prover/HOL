## `prove_constructors_distinct`

``` hol4
Prim_rec.prove_constructors_distinct : (thm -> thm)
```

------------------------------------------------------------------------

Proves that the constructors of an automatically-defined concrete type
yield distinct values.

`prove_constructors_distinct` takes as its argument a primitive
recursion theorem, in the form returned by `define_type` for an
automatically-defined concrete type. When applied to such a theorem,
`prove_constructors_distinct` automatically proves and returns a theorem
which states that distinct constructors of the concrete type in question
yield distinct values of this type.

### Failure

Fails if the argument is not a theorem of the form returned by
`define_type`, or if the concrete type in question has only one
constructor.

### Example

Given the following primitive recursion theorem for labelled binary
trees:

``` hol4
   |- !f0 f1.
        ?! fn.
        (!x. fn(LEAF x) = f0 x) /\
        (!b1 b2. fn(NODE b1 b2) = f1(fn b1)(fn b2)b1 b2)
```

`prove_constructors_distinct` proves and returns the theorem:

``` hol4
   |- !x b1 b2. ~(LEAF x = NODE b1 b2)
```

This states that leaf nodes are different from internal nodes. When the
concrete type in question has more than two constructors, the resulting
theorem is just conjunction of inequalities of this kind.

### See also

[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition),
[`Prim_rec.prove_cases_thm`](#Prim_rec.prove_cases_thm),
[`Prim_rec.prove_constructors_one_one`](#Prim_rec.prove_constructors_one_one),
[`Prim_rec.prove_induction_thm`](#Prim_rec.prove_induction_thm),
[`Prim_rec.prove_rec_fn_exists`](#Prim_rec.prove_rec_fn_exists)
