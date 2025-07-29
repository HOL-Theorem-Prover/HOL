## `==`

``` hol4
Parse.== : hol_type quotation -> 'a -> hol_type
```

------------------------------------------------------------------------

Parses a quotation into a HOL type.

An invocation `` ==` ... `== `` is identical to `` Type ` ... ` ``.

### Failure

As for `Parse.Type`.

Turns strings into types.

### See also

[`Parse.Term`](#Parse.Term)
