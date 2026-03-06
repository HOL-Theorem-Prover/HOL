## `parents`

``` hol4
Theory.parents : string -> string list
```

------------------------------------------------------------------------

Lists the parent theories of a named theory.

If `s` is the name of the current theory or an ancestor of the current
theory, the call `parents s` returns a list of strings that identify the
parent theories of `s`. The shorthand `"-"` may be used to denote the
name of the current theory segment.

### Failure

Fails if the named theory is not an ancestor of the current theory.

### Example

``` hol4
- parents "bool";
> val it = ["min"] : string list

- parents "min";
> val it = [] : string list

- current_theory();
> val it = "scratch" : string

- parents "-";
> val it = ["list", "option"] : string list
```

### See also

[`Theory.ancestry`](#Theory.ancestry),
[`Theory.current_theory`](#Theory.current_theory)
