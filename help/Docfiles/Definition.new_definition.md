## `new_definition`

``` hol4
Definition.new_definition : string * term -> thm
```

------------------------------------------------------------------------

Declare a new constant and install a definitional axiom in the current
theory.

The function `new_definition` provides a facility for definitional
extensions to the current theory. It takes a pair argument consisting of
the name under which the resulting definition will be saved in the
current theory segment, and a term giving the desired definition. The
value returned by `new_definition` is a theorem which states the
definition requested by the user.

Let `v_1`,...,`v_n` be tuples of distinct variables, containing the
variables `x_1,...,x_m`. Evaluating
`new_definition (name, c v_1 ... v_n = t)`, where `c` is not already a
constant, declares the sequent `({},\v_1 ... v_n. t)` to be a definition
in the current theory, and declares `c` to be a new constant in the
current theory with this definition as its specification. This constant
specification is returned as a theorem with the form

``` hol4
   |- !x_1 ... x_m. c v_1 ... v_n = t
```

and is saved in the current theory under `name`. Optionally, the
definitional term argument may have any of its variables universally
quantified.

### Failure

`new_definition` fails if `t` contains free variables that are not in
`x_1`, ..., `x_m` (this is equivalent to requiring `\v_1 ... v_n. t` to
be a closed term). Failure also occurs if any variable occurs more than
once in `v_1, ..., v_n`. Finally, failure occurs if there is a type
variable in `v_1`, ..., `v_n` or `t` that does not occur in the type of
`c`.

### Example

A NAND relation can be defined as follows.

``` hol4
   - new_definition (
       "NAND2",
       Term`NAND2 (in_1,in_2) out = !t:num. out t = ~(in_1 t /\ in_2 t)`);

   > val it =
       |- !in_1 in_2 out.
              NAND2 (in_1,in_2) out = !t. out t = ~(in_1 t /\ in_2 t)
       : thm
```

### See also

[`Definition.new_specification`](#Definition.new_specification),
[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition),
[`boolSyntax.new_infixl_definition`](#boolSyntax.new_infixl_definition),
[`boolSyntax.new_infixr_definition`](#boolSyntax.new_infixr_definition),
[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition),
[`TotalDefn.Define`](#TotalDefn.Define)
