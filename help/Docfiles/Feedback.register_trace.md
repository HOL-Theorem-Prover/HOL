## `register_trace`

``` hol4
Feedback.register_trace : (string * int ref * int) -> unit
```

------------------------------------------------------------------------

Registers a new tracing variable.

A call to `register_trace(n, r, m)` registers the integer reference
variable `r` as a tracing variable associated with name `n`. The integer
`m` is its maximum value. Its value at the time of registration is
considered its default value, which will be restored by a call to
`reset_trace n` or `reset_traces`.

### Failure

Fails if there is already a tracing variable registered under the name
given, or if either the maximum value or the value in the reference is
less than zero.

### See also

[`Feedback`](#Feedback),
[`Feedback.register_btrace`](#Feedback.register_btrace),
[`Feedback.register_ftrace`](#Feedback.register_ftrace),
[`Feedback.reset_trace`](#Feedback.reset_trace),
[`Feedback.reset_traces`](#Feedback.reset_traces),
[`Feedback.trace`](#Feedback.trace),
[`Feedback.traces`](#Feedback.traces)
