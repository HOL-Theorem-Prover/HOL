## `prove_constructors_one_one`

``` hol4
Prim_rec.prove_constructors_one_one : (thm -> thm)
```

------------------------------------------------------------------------

Proves that the constructors of an automatically-defined concrete type
are injective.

`prove_constructors_one_one` takes as its argument a primitive recursion
theorem, in the form returned by `define_type` for an
automatically-defined concrete type. When applied to such a theorem,
`prove_constructors_one_one` automatically proves and returns a theorem
which states that the constructors of the concrete type in question are
injective (one-to-one). The resulting theorem covers only those
constructors that take arguments (i.e. that are not just constant
values).

### Failure

Fails if the argument is not a theorem of the form returned by
`define_type`, or if all the constructors of the concrete type in
question are simply constants of that type.

### Example

Given the following primitive recursion theorem for labelled binary
trees:

``` hol4
   |- !f0 f1.
        ?! fn.
        (!x. fn(LEAF x) = f0 x) /\
        (!b1 b2. fn(NODE b1 b2) = f1(fn b1)(fn b2)b1 b2)
```

`prove_constructors_one_one` proves and returns the theorem:

``` hol4
   |- (!x x'. (LEAF x = LEAF x') = (x = x')) /\
      (!b1 b2 b1' b2'.
        (NODE b1 b2 = NODE b1' b2') = (b1 = b1') /\ (b2 = b2'))
```

This states that the constructors `LEAF` and `NODE` are both injective.

### See also

[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition),
[`Prim_rec.prove_cases_thm`](#Prim_rec.prove_cases_thm),
[`Prim_rec.prove_constructors_distinct`](#Prim_rec.prove_constructors_distinct),
[`Prim_rec.prove_induction_thm`](#Prim_rec.prove_induction_thm),
[`Prim_rec.prove_rec_fn_exists`](#Prim_rec.prove_rec_fn_exists)
