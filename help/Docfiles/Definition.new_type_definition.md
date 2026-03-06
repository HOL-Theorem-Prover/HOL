## `new_type_definition`

``` hol4
Definition.new_type_definition : string * thm -> thm
```

------------------------------------------------------------------------

Defines a new type constant or type operator.

The ML function `new_type_definition` implements the primitive HOL rule
of definition for introducing new type constants or type operators into
the logic. If `t` is a term of type `ty->bool` containing `n` distinct
type variables, then evaluating:

``` hol4
   new_type_definition (tyop, |- ?x. t x)
```

results in `tyop` being declared as a new `n`-ary type operator in the
current theory and returned by the call to `new_type_definition`. This
new type operator is characterized by a definitional axiom of the form:

``` hol4
   |- ?rep:('a,...,'n)op->tyop. TYPE_DEFINITION t rep
```

which is stored as a definition in the current theory segment under the
automatically-generated name `op_TY_DEF`. The arguments to the new type
operator occur in the order given by an alphabetic ordering of the name
of the corresponding type variables. The constant `TYPE_DEFINITION` in
this axiomatic characterization of `tyop` is defined by:

``` hol4
   |- TYPE_DEFINITION (P:'a->bool) (rep:'b->'a) =
         (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\
         (!x. P x = (?x'. x = rep x'))
```

Thus `|- ?rep. TYPE_DEFINITION P rep` asserts that there is a bijection
between the newly defined type `('a,...,'n)tyop` and the set of values
of type `ty` that satisfy `P`.

### Failure

Executing `new_type_definition(tyop,th)` fails if `th` is not an
assumption-free theorem of the form `|- ?x. t x`, if the type of `t` is
not of the form `ty->bool`, or if there are free variables in the term
`t`.

### Example

In this example, a type containing three elements is defined. The
predicate defining the type is over the type `bool # bool`.

``` hol4
   app load ["PairedLambda", "Q"]; open PairedLambda pairTheory;

   - val tyax =
      new_type_definition ("three",
        Q.prove(`?p. (\(x,y). ~(x /\ y)) p`,
                Q.EXISTS_TAC `(F,F)` THEN GEN_BETA_TAC THEN REWRITE_TAC []));

   > val tyax = |- ?rep. TYPE_DEFINITION (\(x,y). ~(x /\ y)) rep : thm
```

### Comments

Usually, once a type has been defined, maps between the representation
type and the new type need to be proved. This may be accomplished using
`define_new_type_bijections`. In the example, the two functions are
named `abs3` and `rep3`.

``` hol4
   - val three_bij = define_new_type_bijections
                      {name="three_tybij", ABS="abs3", REP="rep3", tyax=tyax};
   > val three_bij =
       |- (!a. abs3 (rep3 a) = a) /\
          (!r. (\(x,y). ~(x /\ y)) r = (rep3 (abs3 r) = r))
```

Properties of the maps may be conveniently proved with
`prove_abs_fn_one_one`, `prove_abs_fn_onto`, `prove_rep_fn_one_one`, and
`prove_rep_fn_onto`. In this case, we need only `prove_abs_fn_one_one`.

``` hol4
   - val abs_11 = GEN_BETA_RULE (prove_abs_fn_one_one three_bij);

   > val abs_11 =
       |- !r r'.
            ~(FST r /\ SND r) ==>
            ~(FST r' /\ SND r') ==>
            ((abs3 r = abs3 r') = (r = r')) : thm
```

Now we address how to define constants designating the three elements of
our example type. We will use `new_specification` to create these
constants (say `e1`, `e2`, and `e3`) and their characterizing property,
which is

``` hol4
   ~(e1 = e2) /\ ~(e2 = e3) /\ ~(e3 = e1)
```

A simple lemma stating that the abstraction function doesn't confuse any
of the representations is required:

``` hol4
   - val abs_distinct =
       REWRITE_RULE (PAIR_EQ::pair_rws)
         (LIST_CONJ (map (C Q.SPECL abs_11)
                         [[`(F,F)`,`(F,T)`],
                          [`(F,T)`,`(T,F)`],
                          [`(T,F)`,`(F,F)`]]));

   > val abs_distinct =
      |- ~(abs3 (F,F) = abs3 (F,T)) /\
         ~(abs3 (F,T) = abs3 (T,F)) /\
         ~(abs3 (T,F) = abs3 (F,F)) : thm
```

Finally, we can introduce the constants and their property.

``` hol4
   - val THREE = new_specification
       ("THREE", ["e1", "e2", "e3"],
        PROVE [abs_distinct]
         (Term`?x y z:three. ~(x=y) /\ ~(y=z) /\ ~(z=x)`));

   > val THREE = |- ~(e1 = e2) /\ ~(e2 = e3) /\ ~(e3 = e1) : thm
```

### See also

[`Drule.define_new_type_bijections`](#Drule.define_new_type_bijections),
[`Prim_rec.prove_abs_fn_one_one`](#Prim_rec.prove_abs_fn_one_one),
[`Prim_rec.prove_abs_fn_onto`](#Prim_rec.prove_abs_fn_onto),
[`Drule.prove_rep_fn_one_one`](#Drule.prove_rep_fn_one_one),
[`Drule.prove_rep_fn_onto`](#Drule.prove_rep_fn_onto),
[`Definition.new_specification`](#Definition.new_specification)
