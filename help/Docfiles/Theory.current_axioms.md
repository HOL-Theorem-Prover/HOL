## `current_axioms`

``` hol4
Theory.current_axioms : unit -> (string * thm) list
```

------------------------------------------------------------------------

Return the axioms in the current theory segment.

An invocation `current_axioms()` returns a list of the axioms asserted
in the current theory segment.

### Failure

Never fails. If no axioms have been asserted, the empty list is
returned.

### See also

[`Theory.current_theory`](#Theory.current_theory),
[`Theory.new_theory`](#Theory.new_theory),
[`Theory.current_definitions`](#Theory.current_definitions),
[`Theory.current_theorems`](#Theory.current_theorems),
[`Theory.constants`](#Theory.constants),
[`Theory.types`](#Theory.types), [`Theory.parents`](#Theory.parents)
