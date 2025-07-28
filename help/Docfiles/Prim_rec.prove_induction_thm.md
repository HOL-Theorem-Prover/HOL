## `prove_induction_thm` {#Prim_rec.prove_induction_thm}


```
prove_induction_thm : (thm -> thm)
```



Derives structural induction for an automatically-defined concrete type.


`prove_induction_thm` takes as its argument a primitive recursion theorem, in
the form returned by `define_type` for an automatically-defined concrete type.
When applied to such a theorem, `prove_induction_thm` automatically proves and
returns a theorem that states a structural induction principle for the concrete
type described by the argument theorem. The theorem returned by
`prove_induction_thm` is in a form suitable for use with the general structural
induction tactic `INDUCT_THEN`.

### Failure

Fails if the argument is not a theorem of the form returned by `define_type`.

### Example

Given the following primitive recursion theorem for labelled binary trees:
    
       |- !f0 f1.
            ?! fn.
            (!x. fn(LEAF x) = f0 x) /\
            (!b1 b2. fn(NODE b1 b2) = f1(fn b1)(fn b2)b1 b2)
    
`prove_induction_thm` proves and returns the theorem:
    
       |- !P. (!x. P(LEAF x)) /\ (!b1 b2. P b1 /\ P b2 ==> P(NODE b1 b2)) ==>
              (!b. P b)
    
This theorem states the principle of structural induction on labelled
binary trees: if a predicate `P` is true of all leaf nodes, and if whenever it
is true of two subtrees `b1` and `b2` it is also true of the tree `NODE b1 b2`,
then `P` is true of all labelled binary trees.

### See also

[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN), [`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition), [`Prim_rec.prove_cases_thm`](#Prim_rec.prove_cases_thm), [`Prim_rec.prove_constructors_distinct`](#Prim_rec.prove_constructors_distinct), [`Prim_rec.prove_constructors_one_one`](#Prim_rec.prove_constructors_one_one), [`Prim_rec.prove_rec_fn_exists`](#Prim_rec.prove_rec_fn_exists)

