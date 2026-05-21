## `permahide`

``` hol4
Parse.permahide : term -> unit
```

------------------------------------------------------------------------

Hide a constant so that its name doesn't overload to it.

A call to `permahide c` where `c` is a constant removes any mapping from
`c`'s name to that string in the overloading map. This is done by
calling `remove_ovl_mapping`, which see.

### Failure

Fails if the term argument is not a constant.

### Comments

This is a convenience wrapper for `remove_ovl_mapping`. It is not the
same as a "permanent" form of the related `hide` function. A call to
`hide s`, with `s` a string, clears all overloads to the string `s`,
making that string parse to a variable when name resolution is
performed. By contrast, `permahide c` only adjusts the overloading maps
to and from `c`.

The intention is that `permahide` can be used in theory developments
where a constant is needed but contaminating the namespace with that
constant's name is not desired.

### See also

[`Parse.hide`](#Parse.hide),
[`Parse.remove_ovl_mapping`](#Parse.remove_ovl_mapping)
