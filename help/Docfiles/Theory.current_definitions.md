## `current_definitions`

``` hol4
Theory.current_definitions : unit -> (string * thm) list
```

------------------------------------------------------------------------

Return the definitions in the current theory segment.

An invocation `current_definitions()` returns the list of definitions
stored in the current theory segment. Every definition is automatically
stored in the current segment by the primitive definition principles.

Advanced definition principles are built in terms of the primitives, so
they also store their results in the cuurent segment. However, the
definitions may be quite far removed from the user input, and they may
also store some consequences of the definition as theorems.

### Failure

Never fails. If no definitions have been made, the empty list is
returned.

### See also

[`Theory.current_theory`](#Theory.current_theory),
[`Theory.new_theory`](#Theory.new_theory),
[`Theory.current_axioms`](#Theory.current_axioms),
[`Theory.current_theorems`](#Theory.current_theorems),
[`Theory.constants`](#Theory.constants),
[`Theory.types`](#Theory.types), [`Theory.parents`](#Theory.parents),
[`Definition.new_definition`](#Definition.new_definition),
[`Definition.new_specification`](#Definition.new_specification),
[`Definition.new_type_definition`](#Definition.new_type_definition),
[`TotalDefn.Define`](#TotalDefn.Define),
[`IndDefLib.Hol_reln`](#IndDefLib.Hol_reln)
