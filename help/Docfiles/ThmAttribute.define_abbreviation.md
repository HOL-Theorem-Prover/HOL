## `define_abbreviation`

``` hol4
ThmAttribute.define_abbreviation : {
  abbrev : string,
  expansion : (string * string list) list
} -> unit
```

------------------------------------------------------------------------

Defines an abbreviation expanding to multiple attributes

A call to `define_abbreviation{abbrev=a,expansion=e}` modifies the
handling of theorem attributes so that when attributes attached to
theorem names are parsed, the string `a` will be replaced by the
expansion `e`. If the abbreviation string is accompanied by arguments,
these are silently dropped.

### Failure

A call to `define_abbreviation{abbrev,expansion}` will fail if the
`abbrev` name is already in use as an attribute or reserved word.

### Comments

These abbreviations do not persist; they are meant to be a transient
convenience.

### See also

[`ThmAttribute.register_attribute`](#ThmAttribute.register_attribute)
