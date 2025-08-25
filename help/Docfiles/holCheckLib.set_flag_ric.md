## `set_flag_ric`

``` hol4
holCheckLib.set_flag_ric : bool -> model -> model
```

------------------------------------------------------------------------

Sets a HolCheck model to be synchronous if the first argument is true,
asynchronous otherwise.

ric stands for "relation is conjunctive". This information is used by
HolCheck to decide if the transitions of the model occur simultaneously
(conjunctive, synchronous) or interleaved (disjunctive, asynchronous).

### Comments

This information must be set for a HolCheck model.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.empty_model`](#holCheckLib.empty_model),
[`holCheckLib.get_flag_ric`](#holCheckLib.get_flag_ric)
