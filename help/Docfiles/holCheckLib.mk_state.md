## `mk_state`

``` hol4
holCheckLib.mk_state : term -> (string,term) list -> term
```

------------------------------------------------------------------------

Given the initial states and transition system of a HolCheck model,
constructs a state tuple that can be used to specify HolCheck
properites.

HolCheck models atomic propositions in properties as functions on the
state. Thus we need a representation of the state to specify properties.
This function is used to create such a representative. Its return value
is also passed to holCheckLib.set_state to ensure that the properties
and the model use the same state tuple.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.set_state`](#holCheckLib.set_state)
