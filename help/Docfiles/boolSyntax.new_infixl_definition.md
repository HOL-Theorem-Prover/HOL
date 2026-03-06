## `new_infixl_definition`

``` hol4
boolSyntax.new_infixl_definition : string * term * int -> thm
```

------------------------------------------------------------------------

Declares a new left associative infix constant and installs a definition
in the current theory.

The function `new_infix_definition` provides a facility for definitional
extensions to the current theory. It takes a triple consisting of the
name under which the resulting definition will be saved in the current
theory segment, a term giving the desired definition and an integer
giving the precedence of the infix. The value returned by
`new_infix_definition` is a theorem which states the definition
requested by the user.

Let `v_1` and `v_2` be tuples of distinct variables, containing the
variables `x_1,...,x_m`. Evaluating
`new_infix_definition (name, ix v_1 v_2 = t)` declares the sequent
`({},\v_1 v_2. t)` to be a definition in the current theory, and
declares `ix` to be a new constant in the current theory with this
definition as its specification. This constant specification is returned
as a theorem with the form

``` hol4
   |- !x_1 ... x_m. v_1 ix v_2 = t
```

and is saved in the current theory under (the name) `name`. Optionally,
the definitional term argument may have any of its variables universally
quantified. The constant `ix` has infix status only after the infix
declaration has been processed. It is therefore necessary to use the
constant in normal prefix position when making the definition.

### Failure

`new_infixl_definition` fails if `t` contains free variables that are
not in either of the variable structures `v_1` and `v_2` (this is
equivalent to requiring `\v_1 v_2. t` to be a closed term); or if any
variable occurs more than once in `v_1, v_2`. It also fails if the
precedence level chosen for the infix is already home to parsing rules
of a different form of fixity (infixes associating in a different way,
or suffixes, prefixes etc). Finally, failure occurs if there is a type
variable in `v_1`, ..., `v_n` or `t` that does not occur in the type of
`ix`.

### Example

The nand function can be defined as follows.

``` hol4
   - new_infix_definition
    ("nand", “$nand in_1 in_2 = ~(in_1 /\ in_2)”, 500);;
   > val it = |- !in_1 in_2. in_1 nand in_2 = ~(in_1 /\ in_2) : thm
```

### Comments

It is a common practice among HOL users to write a `$` before the
constant being defined as an infix to indicate that after the definition
is made, it will have a special syntactic status; ie. to write:

``` hol4
   new_infixl_definition("ix_DEF", Term `$ix m n = ... `)
```

This use of `$` is not necessary; but after the definition has been made
`$` must, of course, be used if the syntactic status needs to be
suppressed.

In releases of hol98 past Taupo 1, `new_infixl_definition` and its
sister `new_infixr_definition` replace the old `new_infix_definition`,
which has been superseded. Its behaviour was to define a right
associative infix, so can be freely replaced by `new_infixr_definition`.

### See also

[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition),
[`Definition.new_definition`](#Definition.new_definition),
[`Definition.new_specification`](#Definition.new_specification),
[`boolSyntax.new_infixr_definition`](#boolSyntax.new_infixr_definition),
[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition),
[`TotalDefn.Define`](#TotalDefn.Define)
