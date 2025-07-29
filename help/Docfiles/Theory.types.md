## `types`

``` hol4
Theory.types : string -> (string * int) list
```

------------------------------------------------------------------------

Lists the types in the named theory.

The function `types` should be applied to a string which is the name of
an ancestor theory (including the current theory; the special string
`"-"` is always interpreted as the current theory). It returns a list of
all the type constructors declared in the named theory, in the form of
arity-name pairs.

### Failure

Fails unless the named theory is an ancestor, or the current theory.

### Example

``` hol4
- load "bossLib";
> val it = () : unit

- itlist union (map types (ancestry "-")) [];
> val it =
    [("one", 0), ("option", 1), ("prod", 2), ("sum", 2),
     ("fun", 2), ("ind", 0), ("bool", 0), ("num", 0),
     ("recspace", 1), ("list", 1)] : (string * int) list
```

### See also

[`Theory.constants`](#Theory.constants),
[`Theory.current_axioms`](#Theory.current_axioms),
[`Theory.current_definitions`](#Theory.current_definitions),
[`Theory.current_theorems`](#Theory.current_theorems),
[`Theory.new_type`](#Theory.new_type),
[`Definition.new_type_definition`](#Definition.new_type_definition),
[`Theory.parents`](#Theory.parents),
[`Theory.ancestry`](#Theory.ancestry)
