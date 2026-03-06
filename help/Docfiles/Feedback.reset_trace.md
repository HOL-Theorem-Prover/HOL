## `reset_trace`

``` hol4
Feedback.reset_trace : string -> unit
```

------------------------------------------------------------------------

Resets a tracing variable to its default value.

A call to `reset_trace n` resets the tracing variable associated with
the name `n` to its default value, i.e., the value of the expression
`!r` when `n` was registered with `register_trace n r`.

### Failure

Fails if the name given is not associated with a registered tracing
variable, or if a `set` function associated with a "functional" trace
(see `register_ftrace`) fails.

### See also

[`Feedback`](#Feedback),
[`Feedback.register_trace`](#Feedback.register_trace),
[`Feedback.set_trace`](#Feedback.set_trace),
[`Feedback.reset_traces`](#Feedback.reset_traces),
[`Feedback.trace`](#Feedback.trace),
[`Feedback.traces`](#Feedback.traces)
