## `set_props` {#holCheckLib.set_props}


```
set_props :  (string * term) list -> model -> model
```



Sets the properties to be checked for the supplied HolCheck model.


The first argument is a list of (property_name, property) pair, where the name is a string and the property is a well-formed CTL or mu-calculus property. The list must not be empty. Names must be unique.

In the properties, care must be taken to model atomic propositions as functions on the state. At the moment, only boolean variables are allowed as atomic propositions.

### Failure

Fails if the property list is empty, or the names violate HOL constant naming rules, or names are unique. Also fails if any atomic proposition is not a paired abstraction of the form `\state. boolvar`.

### Example

Specifing a CTL property for a mod-8 counter assuming holCheckLib has been loaded (there exists a future in which the most significant bit will go high) :

    
    - val m = holCheckLib.set_props [("ef_msb_high",``C_EF (C_BOOL (B_PROP  (\(v0,v1,v2). v2))``)] holCheckLib.empty_model
    > val m = <model> : model
    

### Comments

This information must be set for a HolCheck model. For more details on how to specify properties, see the examples in the src/HolCheck/examples directory; the mod8 and amba_apb examples are good starting points.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck), [`holCheckLib.empty_model`](#holCheckLib.empty_model), [`holCheckLib.get_props`](#holCheckLib.get_props), [`holCheckLib.get_results`](#holCheckLib.get_results), [`holCheckLib.set_state`](#holCheckLib.set_state), [`holCheckLib.prove_model`](#holCheckLib.prove_model)

