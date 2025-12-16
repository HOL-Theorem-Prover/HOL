## `prove_rep_fn_onto`

``` hol4
Drule.prove_rep_fn_onto : thm -> thm
```

------------------------------------------------------------------------

Proves that a type representation function is onto (surjective).

If `th` is a theorem of the form returned by the function
`define_new_type_bijections`:

``` hol4
   |- (!a. abs(rep a) = a) /\ (!r. P r = (rep(abs r) = r))
```

then `prove_rep_fn_onto th` proves from this theorem that the function
`rep` is onto the set of values that satisfy `P`, returning the theorem:

``` hol4
   |- !r. P r = (?a. r = rep a)
```

### Failure

Fails if applied to a theorem not of the form shown above.

### See also

[`Definition.new_type_definition`](#Definition.new_type_definition),
[`Drule.define_new_type_bijections`](#Drule.define_new_type_bijections),
[`Drule.prove_abs_fn_one_one`](#Drule.prove_abs_fn_one_one),
[`Drule.prove_abs_fn_onto`](#Drule.prove_abs_fn_onto),
[`Drule.prove_rep_fn_one_one`](#Drule.prove_rep_fn_one_one)
