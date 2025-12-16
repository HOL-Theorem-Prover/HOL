## `update_overload_maps`

``` hol4
Parse.update_overload_maps :
  string -> ({Name : string, Thy : string} list *
             {Name : string, Thy : string} list) -> unit
```

------------------------------------------------------------------------

Adds to the parser's overloading maps.

The parser/pretty-printer for terms maintains two maps between constants
and strings. From strings to terms, the map is from one string to a set
of terms. Each term represents a possible overloading for the string. In
the other direction, a term maps to just one string, its preferred
representation.

The function `update_overload_maps` adds to (potentially overriding old
mappings in) both of these maps. Its first parameter, a string, is the
string involved in both directions. The two lists of `Name`-`Thy`
records specify terms for the two maps. The first component of the
tuple, specifies terms that the string will be overloaded to. (Note that
it is perfectly reasonable to "overload" to just one term, and that this
is the default situation for newly defined constants.)

The second component of the tuple sets the given string as the preferred
identifier for the given terms.

### Failure

Fails if any of the `Name`-`Thy` pairs doesn't correspond to an actual
constant.

### See also

[`Parse.clear_overloads_on`](#Parse.clear_overloads_on),
[`Parse.hide`](#Parse.hide), [`Parse.overload_on`](#Parse.overload_on),
[`Parse.remove_ovl_mapping`](#Parse.remove_ovl_mapping),
[`Parse.reveal`](#Parse.reveal)
