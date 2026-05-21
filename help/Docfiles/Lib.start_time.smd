## `start_time`

``` hol4
Lib.start_time : unit -> Timer.cpu_timer
```

------------------------------------------------------------------------

Set a timer running.

An application `start_time ()` creates a timer and starts it. A later
invocation `end_time t`, where `t` is a timer, will need to be called to
get the elapsed time between the two function calls.

### Failure

Never fails.

### Example

``` hol4
- val clock = start_time ();
> val clock = <cpu_timer> : cpu_timer
```

### Comments

Multiple timers may be started without any interfering with the others.

Further operations associated with the type `cpu_timer` may be found in
the Standard ML Basis Library structures `Timer` and `Time`.

### See also

[`Lib.end_time`](#Lib.end_time), [`Lib.time`](#Lib.time)
