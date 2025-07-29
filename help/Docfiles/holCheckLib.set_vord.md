## `set_vord`

``` hol4
holCheckLib.set_vord : string list -> model -> model
```

------------------------------------------------------------------------

Sets the BDD variable ordering used by HolCheck for the given model.

The first argument specifies the ordering of variables. This ordering
must contain all current- and next-state variables specified by set_init
and set_trans. In particular, if either set_init or set_trans use a
variable v, then v' must be mentioned in the ordering. Likewise for
unprimed versions of primed variables.

### Comments

This information is optional when constructing HolCheck models. By
default, HolCheck constructs its own heuristic-based variable ordering.
The heuristic used is a rather primitive one, at the moment. It just
interleaves next- and current-state variables.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.empty_model`](#holCheckLib.empty_model),
[`holCheckLib.get_vord`](#holCheckLib.get_vord)
