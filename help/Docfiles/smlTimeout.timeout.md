## `timeout`

``` hol4
smlTimeout.timeout : real -> ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Interrupts a function `f` after a time limit.

In case the limit is reached, the exception FunctionTimeout is raised,
otherwise it behaves in the same way as a call to "f" on its argument.

### Failure

Fails when the call to `f` exceeds the time limit or if `f` fails.

### Example

``` hol4
- load "smlTimeout"; open smlTimeout;
(* output omitted *)
> val it = () : unit

- timeout 0.1 (fn (x:int) => (raise Match):int) 5;
> Exception- Match raised

- timeout 0.2 OS.Process.sleep (Time.fromReal 2.0);
> Exception- FunctionTimeout raised

- timeout 1.0 (fn x => x) 5;
> val it = 5: int
```

### Comments

Relies on a conditional variable to decide if and when to send an
Interrupt signal to the worker thread in which the function `f` is
called. In the case an interrupt is needed, a bit of time is given to
the function `f` to catch the Interrupt and return a result. This last
step has been implemented with a busy waiting loop that has
experimentally been determined to be more efficient than relying on an
additional condition variable.
