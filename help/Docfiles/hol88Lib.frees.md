## `frees`

``` hol4
hol88Lib.frees : term -> term list
```

------------------------------------------------------------------------

Returns a list of the variables which are free in a term.

`frees` is equivalent to `rev o Term.free_vars`.

### Failure

Never fails.

### Comments

Superseded by `Term.free_vars`.

### See also

[`hol88Lib.freesl`](#hol88Lib.freesl),
[`Term.free_vars`](#Term.free_vars)
