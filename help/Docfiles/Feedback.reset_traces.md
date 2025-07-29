## `reset_traces`

``` hol4
Feedback.reset_traces : unit -> unit
```

------------------------------------------------------------------------

Resets all registered tracing variables to their default values.

### Failure

Fails if a `set` function associated with a "functional" trace (see
`register_ftrace`) fails.

### See also

[`Feedback`](#Feedback), [`Feedback.set_trace`](#Feedback.set_trace),
[`Feedback.register_trace`](#Feedback.register_trace),
[`Feedback.reset_trace`](#Feedback.reset_trace),
[`Feedback.trace`](#Feedback.trace),
[`Feedback.traces`](#Feedback.traces)
