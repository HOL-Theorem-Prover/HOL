## `remove_ovl_mapping`

``` hol4
Parse.remove_ovl_mapping: string -> {Name:string,Thy:string} -> unit
```

------------------------------------------------------------------------

Removes an overloading mapping between the string and constant
specified.

Each grammar maintains two maps internally. One is from strings to
non-empty lists of terms, and the other is from terms to strings. The
first map is used to resolve overloading when parsing. A string will
eventually be turned into one of the terms in the list that it maps to.
When printing a constant, the map in the opposite direction is used to
turn a term into a string.

A call to `remove_ovl_mapping s {Name,Thy}`, maps the `Name`-`Thy`
record to a constant `c`, and removes the `c`-`s` pair from both maps.

### Failure

Never fails. If the given pair is not in either map, the function
silently does nothing.

To prune the overloading maps of unwanted possibilities.

### Comments

Note that removing a print-mapping for a constant will result in that
constant always printing fully qualified as `thy$name`. This situation
will persist until that constant is given a name to map to (either with
`overload_on` or `update_overload_maps`).

As with other parsing functions, there is a sister function,
`temp_remove_ovl_mapping` that does the same thing, but whose effect is
not saved to a theory file.

### See also

[`Parse.clear_overloads_on`](#Parse.clear_overloads_on),
[`Parse.overload_on`](#Parse.overload_on),
[`Parse.update_overload_maps`](#Parse.update_overload_maps)
