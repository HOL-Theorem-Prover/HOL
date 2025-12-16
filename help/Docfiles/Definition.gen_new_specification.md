## `gen_new_specification`

``` hol4
Definition.gen_new_specification : string * thm -> thm
```

------------------------------------------------------------------------

Introduce a constant or constants satisfying a given property.

The ML function `gen_new_specification` implements the generalised
primitive rule of constant specification for the HOL logic.

Evaluating:

``` hol4
   gen_new_specification (name, [x1=t1,...,xn=tn] |- t)
```

simultaneously introduces new constants named `x1`,...,`xn` satisfying
the property:

``` hol4
   |- t
```

where the variables `x1`,...,`xn` in `t` are replaced by the new
constants.

This theorem is stored, with name `name`, as a definition in the current
theory segment. It is also returned by the call to
`gen_new_specification`.

### Failure

`gen_new_specification` fails if any of the hypotheses of the input
theorem are not of the right form: they must be equations each with a
variable on the left-hand side and no free variables on the right-hand
side. It also fails if the supplied variables (equivalently, the desired
constant names) `x1`,...,`xn` are not distinct. Finally, failure occurs
if the type of some `ti` does not contain all the type variables
occurring in the term `ti` itself.

### Comments

The generalised version is described in Rob Arthan's ITP 2014 paper, HOL
Constant Definition Done Right, available from
`http://www.lemma-one.com/papers/hcddr.pdf`.

### See also

[`Definition.new_specification`](#Definition.new_specification)
