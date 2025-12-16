## `register_btrace`

``` hol4
Feedback.register_btrace : string * bool ref -> unit
```

------------------------------------------------------------------------

Registers a trace variable for a boolean reference.

A call to `register_btrace(nm, bref)` registers a trace variable called
`nm` that can take on two different values (0 and 1), which correspond
to the state of the boolean variable `bref`.

### Failure

Fails if the given name is already in use as a trace variable.

### Comments

This function uses `register_ftrace` to make a boolean variable appear
as an integer value.

### See also

[`Feedback`](#Feedback),
[`Feedback.current_trace`](#Feedback.current_trace),
[`Feedback.register_trace`](#Feedback.register_trace),
[`Feedback.register_ftrace`](#Feedback.register_ftrace),
[`Feedback.set_trace`](#Feedback.set_trace),
[`Feedback.trace`](#Feedback.trace),
[`Feedback.traces`](#Feedback.traces)
