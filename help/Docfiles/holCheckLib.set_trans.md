## `set_trans`

``` hol4
holCheckLib.set_trans : (string * Term.term) list -> model -> model
```

------------------------------------------------------------------------

Sets the transition system for a HolCheck model.

The transition system is supplied as list of (transition label,
transition relation) pairs. Each label must be a unique string. Each
relation must be a propositional term, in which primed variables
represent values in the next state. The transition label "." is
internally used as a wildcard that is expected to match all transitions,
and is thus not allowed as a transition label, unless there is only one
transition.

### Failure

Fails if the transition labels are not unique, or the transition list is
empty, or the wildcard label is used with a non-singleton transition
list, or any of the relation terms is not a quantified boolean formula
(QBF).

### Example

For a mod-8 counter, we need three boolean variables to encode the
state. The single transition relation can then be set as follows
(assuming holCheckLib has been loaded):

``` hol4
- val m = holCheckLib.set_trans [("v0", ``v0' = ~v0``), ("v1", ``v1' = (v0 \/ v1) /\ ~(v0 = v1)``),
                 ("v2", ``v2' = (v0 /\ v1 \/ v2) /\ ~(v0 /\ v1 = v2)``)] holCheckLib.empty_model;
> val m = <model> : model
```

where empty_model can be replaced by whatever model the user is
building.

### Comments

This information must be set for a HolCheck model.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.empty_model`](#holCheckLib.empty_model),
[`holCheckLib.get_trans`](#holCheckLib.get_trans),
[`holCheckLib.set_flag_ric`](#holCheckLib.set_flag_ric)
