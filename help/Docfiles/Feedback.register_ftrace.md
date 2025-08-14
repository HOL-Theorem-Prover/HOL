## `register_ftrace`

``` hol4
Feedback.register_ftrace :
  (string * ((unit -> int) * (int -> unit)) * int) -> unit
```

------------------------------------------------------------------------

Registers a trace that is accessed by a set/get pair of functions.

A call to `register_ftrace(nm, (g,s), m)` registers an integer-valued
trace variable that is updated with the `s` function and whose value is
read with the `g` function. The variable is given the name `nm` and the
variable's maximum allowed value is `m`. The trace's default is the
value of `g()`, which is called just once as part of the registration
procedure.

### Failure

Fails if the given name is already in use as a trace variable, or if the
maximum or the default value (returned by `g()`) is less than zero.

### Comments

The two functions provide a more general way of accessing something that
may not be actually be an integer reference, even though this is the
interface that the various trace functions present.

### See also

[`Feedback`](#Feedback),
[`Feedback.current_trace`](#Feedback.current_trace),
[`Feedback.register_trace`](#Feedback.register_trace),
[`Feedback.register_btrace`](#Feedback.register_btrace),
[`Feedback.set_trace`](#Feedback.set_trace),
[`Feedback.trace`](#Feedback.trace),
[`Feedback.traces`](#Feedback.traces)
