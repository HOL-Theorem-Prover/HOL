## `define_new_type_bijections`

``` hol4
Drule.define_new_type_bijections :
  {name:string, ABS:string, REP:string, tyax:thm} -> thm
```

------------------------------------------------------------------------

Introduces abstraction and representation functions for a defined type.

The result of making a type definition using `new_type_definition` is a
theorem of the following form:

``` hol4
   |- ?rep:nty->ty. TYPE_DEFINITION P rep
```

which asserts only the existence of a bijection from the type it defines
(in this case, `nty`) to the corresponding subset of an existing type
(here, `ty`) whose characteristic function is specified by `P`. To
automatically introduce constants that in fact denote this bijection and
its inverse, the ML function `define_new_type_bijections` is provided.

`name` is the name under which the constant definition (a constant
specification, in fact) made by `define_new_type_bijections` will be
stored in the current theory segment. `tyax` must be a definitional
axiom of the form returned by `new_type_definition`. `ABS` and `REP` are
the user-specified names for the two constants that are to be defined.
These constants are defined so as to denote mutually inverse bijections
between the defined type, whose definition is given by `tyax`, and the
representing type of this defined type.

If `th` is a theorem of the form returned by `new_type_definition`:

``` hol4
   |- ?rep:newty->ty. TYPE_DEFINITION P rep
```

then evaluating:

``` hol4
   define_new_type_bijections{name="name",ABS="abs",REP="rep",tyax=th} th
```

automatically defines two new constants `abs:ty->newty` and
`rep:newty->ty` such that:

``` hol4
   |- (!a. abs(rep a) = a) /\ (!r. P r = (rep(abs r) = r))
```

This theorem, which is the defining property for the constants `abs` and
`rep`, is stored under the name `name` in the current theory segment. It
is also the value returned by `define_new_type_bijections`. The theorem
states that `abs` is the left inverse of `rep` and, for values
satisfying `P`, that `rep` is the left inverse of `abs`.

### Failure

A call `define_new_type_bijections{name,ABS,REP,tyax}` fails if `tyax`
is not a theorem of the form returned by `new_type_definition`.

### See also

[`Definition.new_type_definition`](#Definition.new_type_definition),
[`Drule.prove_abs_fn_one_one`](#Drule.prove_abs_fn_one_one),
[`Drule.prove_abs_fn_onto`](#Drule.prove_abs_fn_onto),
[`Drule.prove_rep_fn_one_one`](#Drule.prove_rep_fn_one_one),
[`Drule.prove_rep_fn_onto`](#Drule.prove_rep_fn_onto)
