## `register_frag`

``` hol4
simpLib.register_frag : ssfrag -> ssfrag
```

------------------------------------------------------------------------

Registers a simpset fragment for later use with `SF`.

A call to `simpLib.register_frag sfrag` records a mapping from the name
of `sfrag` to the `sfrag` value. This internal database is then used by
simplification tactics when they see theorems created with calls to
`SF`.

### Failure

Fails is the fragment `sfrag` is anonymous.

### See also

[`bossLib.SF`](#bossLib.SF)
