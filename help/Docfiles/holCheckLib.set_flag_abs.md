## `set_flag_abs`

``` hol4
holCheckLib.set_flag_abs : bool -> model -> model
```

------------------------------------------------------------------------

Sets a flag telling HolCheck whether to attempt abstraction.

HolCheck uses a simple heuristic analysis of the model to determine
whether it would be worthwhile to do abstraction. This flag can be used
to override the default.

### Comments

This information is optional when constructing HolCheck models. The
default is true.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.empty_model`](#holCheckLib.empty_model),
[`holCheckLib.get_flag_abs`](#holCheckLib.get_flag_abs)
