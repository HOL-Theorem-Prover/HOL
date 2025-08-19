## `new_constant`

``` hol4
Theory.new_constant : string * hol_type -> unit
```

------------------------------------------------------------------------

Declares a new constant in the current theory.

A call `new_constant(n,ty)` installs a new constant named `n` in the
current theory. Note that `new_constant` does not specify a value for
the constant, just a name and type. The constant may have a polymorphic
type, which can be used in arbitrary instantiations.

### Failure

Never fails, but issues a warning if the name is not a valid constant
name. It will overwrite an existing constant with the same name in the
current theory.

### See also

[`Theory.constants`](#Theory.constants),
[`boolSyntax.new_infix`](#boolSyntax.new_infix),
[`boolSyntax.new_binder`](#boolSyntax.new_binder),
[`Definition.new_definition`](#Definition.new_definition),
[`Definition.new_type_definition`](#Definition.new_type_definition),
[`Definition.new_specification`](#Definition.new_specification),
[`Theory.new_axiom`](#Theory.new_axiom),
[`boolSyntax.new_infixl_definition`](#boolSyntax.new_infixl_definition),
[`boolSyntax.new_infixr_definition`](#boolSyntax.new_infixr_definition),
[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition)
