## `set_trace`

``` hol4
Feedback.set_trace : string -> int -> unit
```

------------------------------------------------------------------------

Set a tracing level for a registered trace.

Invoking `set_trace n i` sets the level of the tracing mechanism
registered under `n` to be `i`. These settings control the verboseness
of various tools within the system. This can be useful both when
debugging proofs (with the simplifier for example), and also as a guide
to how an automatic proof is proceeding (with `mesonLib` for example).

There is no single interpretation of what activity a tracing level
should evoke: each tool registered for tracing can treat its trace level
in its own way.

### Failure

A call to `set_trace n i` fails if `n` has not previously been
registered via `register_trace`. It also fails if `i` is less than zero,
or if it is greater than the trace's specified maximum value.

### Example

``` hol4
   - set_trace "Rewrite" 1;

   - PURE_REWRITE_CONV [AND_CLAUSES] (Term `x /\ T /\ y`);

   <<HOL message: Rewrite:
   |- T /\ y = y.>>

   > val it = |- x /\ T /\ y = x /\ y : thm
```

### See also

[`Feedback`](#Feedback),
[`Feedback.register_trace`](#Feedback.register_trace),
[`Feedback.reset_trace`](#Feedback.reset_trace),
[`Feedback.reset_traces`](#Feedback.reset_traces),
[`Feedback.trace`](#Feedback.trace),
[`Feedback.traces`](#Feedback.traces)
