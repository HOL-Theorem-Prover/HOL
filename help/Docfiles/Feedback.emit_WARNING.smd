## `emit_WARNING`

``` hol4
Feedback.emit_WARNING : bool ref
```

------------------------------------------------------------------------

Flag controlling output of `HOL_WARNING` function.

The boolean flag `emit_WARNING` is consulted by `HOL_WARNING` when it
attempts to print its argument. This flag is not commonly used, and it
may disappear or change in the future.

The default value of `emit_WARNING` is `true`.

### Example

``` hol4
- HOL_WARNING "Clock" "watcher" "Time is running out.";
<<HOL warning: Clock.watcher: Time is running out.>>
> val it = () : unit

- emit_WARNING := false;
> val it = () : unit

- HOL_WARNING "Clock" "watcher" "Time is running out.";
> val it = () : unit
```

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_WARNING`](#Feedback.HOL_WARNING),
[`Feedback.emit_ERR`](#Feedback.emit_ERR),
[`Feedback.emit_MESG`](#Feedback.emit_MESG)
