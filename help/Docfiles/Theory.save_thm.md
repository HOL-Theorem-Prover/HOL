## `save_thm`

``` hol4
Theory.save_thm : string * thm -> thm
```

------------------------------------------------------------------------

Stores a theorem in the current theory segment.

The call `save_thm(name, th)` adds the theorem `th` to the current
theory segment under the name `name`. The theorem is also the return
value of the call. When the current segment `thy` is exported, things
are arranged in such a way that, if `thyTheory` is loaded into a later
session, the ML variable `thyTheory.name` will have `th` as its value.

### Failure

If `th` is out-of-date, then `save_thm` will fail. If `name` is not a
valid ML alphanumeric identifier, `save_thm` will not fail, but
`export_theory` will (printing an informative error message first).

### Example

``` hol4
- val foo = save_thm("foo", REFL (Term `x:bool`));
> val foo = |- x = x : thm

- current_theorems();
> val it = [("foo", |- x = x)] : (string * thm) list
```

### Comments

If a theorem is already saved under `name` in the current theory
segment, it will be overwritten.

The results of `new_axiom`, and definition principle (such as
`new_definition`, `new_type_definition`, and `new_specification`) are
automatically stored in the current theory: one does not have to call
`save_thm` on them.

Saving important theorems for eventual export. Binding the result of
`save_thm` to an ML variable makes it easy to access the theorem in the
remainder of the current session.

### See also

[`Theory.new_theory`](#Theory.new_theory),
[`Tactical.store_thm`](#Tactical.store_thm), [`DB.fetch`](#DB.fetch),
[`DB.thy`](#DB.thy),
[`Theory.current_definitions`](#Theory.current_definitions),
[`Theory.current_theorems`](#Theory.current_theorems),
[`Theory.uptodate_thm`](#Theory.uptodate_thm),
[`Theory.new_axiom`](#Theory.new_axiom),
[`Definition.new_type_definition`](#Definition.new_type_definition),
[`Definition.new_definition`](#Definition.new_definition),
[`Definition.new_specification`](#Definition.new_specification)
