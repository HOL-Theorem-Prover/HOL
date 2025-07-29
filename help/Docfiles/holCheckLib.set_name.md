## `set_name`

``` hol4
holCheckLib.set_name : string -> model -> model
```

------------------------------------------------------------------------

Sets the name given to the formal model HolCheck constructs internally.

### Failure

Fails if the first argument does not follow the naming rules for
constants.

### Comments

This information is optional when constructing HolCheck models. It
should be set if more than one model is being used in the same session,
to avoid name clashes.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.empty_model`](#holCheckLib.empty_model),
[`holCheckLib.get_name`](#holCheckLib.get_name)
