## `emit_MESG`

``` hol4
Feedback.emit_MESG : bool ref
```

------------------------------------------------------------------------

Flag controlling output of `HOL_MESG` function.

The boolean flag `emit_MESG` is consulted by `HOL_MESG` when it attempts
to print its argument. This flag is not commonly used, and it may
disappear or change in the future.

The default value of `emit_MESG` is `true`.

### Example

``` hol4
- HOL_MESG "Joy to the world.";
<<HOL message: Joy to the world.>>

- emit_MESG := false;
> val it = () : unit

- HOL_MESG "Peace on Earth.";
> val it = () : unit
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_MESG`](#Feedback.HOL_MESG),
[`Feedback.emit_ERR`](#Feedback.emit_ERR),
[`Feedback.emit_WARNING`](#Feedback.emit_WARNING)
