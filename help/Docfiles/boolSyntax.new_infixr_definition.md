## `new_infixr_definition`

``` hol4
boolSyntax.new_infixr_definition : string * term * int -> thm
```

------------------------------------------------------------------------

Declares a new right associative infix constant and installs a
definition in the current theory.

The function `new_infixr_definition` has exactly the same effect as
`new_infixl_definition` except that the infix constant defined will
associate to the right.

### See also

[`Definition.new_definition`](#Definition.new_definition),
[`Definition.new_specification`](#Definition.new_specification),
[`boolSyntax.new_infix`](#boolSyntax.new_infix),
[`boolSyntax.new_infixl_definition`](#boolSyntax.new_infixl_definition)
