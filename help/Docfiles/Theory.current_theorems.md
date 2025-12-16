## `current_theorems`

``` hol4
Theory.current_theorems : unit -> (string * thm) list
```

------------------------------------------------------------------------

Return the theorems stored in the current theory segment.

An invocation `current_theorems ()` returns the list of theorems stored
in the current theory segment.

### Failure

Never fails. If no theorems have been stored, the empty list is
returned.

### See also

[`Theory.current_theory`](#Theory.current_theory),
[`Theory.new_theory`](#Theory.new_theory),
[`Theory.current_definitions`](#Theory.current_definitions),
[`Theory.current_theorems`](#Theory.current_theorems),
[`Theory.constants`](#Theory.constants),
[`Theory.types`](#Theory.types), [`Theory.parents`](#Theory.parents)
