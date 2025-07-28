## `srw_ss` {#bossLib.srw_ss}


```
srw_ss : unit -> simpset
```



Returns the "stateful rewriting" system’s underlying `simpset`.


A call to `srw_ss()` returns a `simpset` value that is internally
maintained and updated by the system.  Its value changes as new types
enter the `TypeBase`, and as theories are loaded.  For this reason, it
can’t be accessed as a simple value, but is instead hidden behind a
function.

The value behind `srw_ss()` can change in three ways.  Firstly, whenever
a type enters the `TypeBase`, the type’s associated simplification
theorems (accessible directly using the function `TypeBase.simpls_of`)
are all added to the `simpset`.  This ensures that the "obvious"
rewrite theorems for a type (such as the disjointness of constructors)
need never be explicitly specified.

Secondly, users can interactively add `simpset` fragments to the
`srw_ss()` value by using the function `augment_srw_ss`.  This
function might be used after a definition is made to ensure that a
particular constant always has its definition expanded.  (Whether or
not a constant warrants this is something that needs to be determined
on a case-by-case basis.)

Thirdly, theories can augment the `srw_ss()` value as they load.  This
is set up in a theory’s script file with the function
`export_rewrites`.  This causes a list of appropriate theorems to be
added when the theory loads.  It is up to the author of the theory to
ensure that the theorems added to the `simpset` are sensible.

### Failure

Never fails.

### See also

[`bossLib.augment_srw_ss`](#bossLib.augment_srw_ss), [`BasicProvers.export_rewrites`](#BasicProvers.export_rewrites), [`bossLib.SRW_TAC`](#bossLib.SRW_TAC)

