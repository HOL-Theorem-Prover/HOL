## `ancestry`

``` hol4
Theory.ancestry : string -> string list
```

------------------------------------------------------------------------

Returns the (proper) ancestry of a theory in a list.

A call to `ancestry thy` returns a list of all the proper ancestors
(i.e. parents, parents of parents, etc.) of the theory `thy`. The
shorthand `"-"` may be used to denote the name of the current theory
segment.

### Failure

Fails if `thy` is not an ancestor of the current theory.

### Example

``` hol4
- load "bossLib";
> val it = () : unit

- current_theory();
> val it = "scratch" : string

- ancestry "-";
> val it =
    ["one", "option", "pair", "sum", "combin", "relation", "min", "bool",
     "num", "prim_rec", "arithmetic", "numeral", "ind_type", "list"] :
  string list
```

### See also

[`Theory.parents`](#Theory.parents)
