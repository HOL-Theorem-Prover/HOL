## `get_results`

``` hol4
holCheckLib.get_results : model -> (term_bdd * thm option * term list option) list option
```

------------------------------------------------------------------------

Returns the results of model checking the HolCheck model, if the model
has been checked.

The order of results in the list corresponds to the order of properties
in the list of properties to be checked for the model. The latter list
can be recovered via holCheckLib.get_props.

Each result is a triple. the first component contains the BDD
representation of the set of states satisfying the property. If the
check succeeded, the second component contains a theorem certifying that
the property holds in the model i.e. it holds in the initial states. The
third component contains a counterexample or witness trace, if one could
be recovered.

### Example

For the mod-8 counter example used as a running example in the online
reference, we obtain the following results for the property that the
most significant bit eventually goes high:

``` hol4
- holCheckLib.get_results m;
> val it =
    SOME [(<term_bdd>,
      SOME|- CTL_MODEL_SAT ctlKS (C_EF (C_BOOL (B_PROP (\(v0,v1,v2). v2)))),
      SOME [``(F,F,F)``, ``(T,F,F)``, ``(F,T,F)``, ``(T,T,F)``, ``(F,F,T)``])]
     : (term_bdd * thm option * term list option) list option
```

The first component contains the BDD representation of the set of states
satisfying the property. The second component contains a formal theorem
certifying the property. The third component contains a witness trace
that counts up to 4.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck),
[`holCheckLib.set_props`](#holCheckLib.set_props),
[`holCheckLib.prove_model`](#holCheckLib.prove_model)
