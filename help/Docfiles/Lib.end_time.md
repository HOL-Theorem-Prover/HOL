## `end_time`

``` hol4
Lib.end_time : Timer.cpu_timer -> unit
```

------------------------------------------------------------------------

Check a running timer, and print out how long it has been running.

An application `end_time timer` looks to see how long `timer` has been
running, and prints out the elapsed runtime, garbage collection time,
and system time.

### Failure

Never fails.

### Example

``` hol4
- val clock = start_time();
> val clock = <cpu_timer> : cpu_timer

- use "foo.sml";
> ... output omitted ...

- end_time clock;
runtime: 525.996s,    gctime: 0.000s,     systime: 525.996s.
> val it = () : unit
```

### Comments

A `start_time` ... `end_time` pair is for use when calling `time` would
be clumsy, e.g., when multiple function applications are to be timed.

### See also

[`Lib.start_time`](#Lib.start_time), [`Lib.time`](#Lib.time)
