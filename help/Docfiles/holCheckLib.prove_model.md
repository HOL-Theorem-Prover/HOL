## `prove_model` {#holCheckLib.prove_model}


```
prove_model : model -> model
```



Attempts to discharge all assumptions to the term_bdd’s and theorems in the results list of the HolCheck model.


HolCheck uses postponed proof verification to speed up the model checking work-flow. Any success theorems and term_bdd’s thus end up with several undischarged assumptions. The idea is that the time-consuming proof verification can be postponed to a later time, when the user is otherwise occupied (e.g. asleep).

### Failure

Fails if not called in the same HOL session that generated the results. This is because the required proof tactics are accumulated in memory as closures. Moscow ML (in which HOL is implemented) cannot persist closures.

### Comments

Other than the failure scenario documented above, a failure in the proof verification points to a bug in the HolCheck proof verification machinery; it does not invalidate the result.

### See also

[`holCheckLib.holCheck`](#holCheckLib.holCheck), [`holCheckLib.get_results`](#holCheckLib.get_results)

