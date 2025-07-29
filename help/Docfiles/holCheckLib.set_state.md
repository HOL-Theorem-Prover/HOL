## `set_state`

``` hol4
holCheckLib.set_state : term -> model -> model
```

------------------------------------------------------------------------

Sets the state tuple used internally by the formal model contructed by
HolCheck.

### Comments

This information is optional when constructing HolCheck models. By
default, HolCheck will construct the state tuple itself. In practice
however, a user nearly always needs to supply the state tuple, since it
is almost always required when specifying properties.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.mk_state`](#holCheckLib.mk_state),
[`holCheckLib.get_state`](#holCheckLib.get_state)
