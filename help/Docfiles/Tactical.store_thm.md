## `store_thm`

``` hol4
Tactical.store_thm : string * term * tactic -> thm
```

------------------------------------------------------------------------

Proves and then stores a theorem in the current theory segment.

The call `store_thm(name, t, tac)` is equivalent to
`save_thm(name, prove(t, tac))`.

### Failure

Whenever `prove` fails to prove the given term.

Saving theorems for retrieval in later sessions. Binding the result of
`store_thm` to an ML variable makes it easy to access the theorem in the
current terminal session.

### See also

[`Tactical.prove`](#Tactical.prove),
[`Theory.save_thm`](#Theory.save_thm)
