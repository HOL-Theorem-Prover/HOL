## `thy_ssfrag`

``` hol4
BasicProvers.thy_ssfrag : string -> simpLib.ssfrag
```

------------------------------------------------------------------------

Returns simplifier fragment for a theory

Returns the simpset fragment recorded for the given theory. This
consists of the rewrites passed to `export_rewrites`.

### Failure

Fails if the theory was not found, or did not export any theorems.

### See also

[`BasicProvers.export_rewrites`](#BasicProvers.export_rewrites)
