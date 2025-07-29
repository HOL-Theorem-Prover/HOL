## `set_init`

``` hol4
holCheckLib.set_init : term -> model -> model
```

------------------------------------------------------------------------

Sets the initial set of states of a HolCheck model.

The supplied term should be a term of propositional logic over the state
variables, with no primed variables.

### Failure

Fails if the supplied term is not a quantified boolean formula (QBF).

### Example

For a mod-8 counter, we need three boolean variables to encode the
state. If the counter starts at 0, the set of initial states of the
model would be set as follows (assuming holCheckLib has been loaded):

``` hol4
- val m = holCheckLib.set_init ``~v0 /\ ~v1 /\ ~v2`` holCheckLib.empty_model;
> val m = <model> : model
```

where empty_model can be replaced by whatever model the user is
building.

### Comments

This information must be set for a HolCheck model.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.empty_model`](#holCheckLib.empty_model),
[`holCheckLib.get_init`](#holCheckLib.get_init)
