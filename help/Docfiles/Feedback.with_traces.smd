## `with_traces`

``` hol4
Feedback.with_traces : (string * int) list -> ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Invoke a function with specified levels for traces.

The `with_traces` function is used to set values of a collection of
tracing variables for the duration of one top-level function call.

In a state where trace variables designated by `nm_1,...,nm_k` have
corresponding values `i_1,...,i_k`, a call
```
with_traces [(nm_1,j_1),...,(nm_k,j_k)] f x
```
first sets the trace variables designated by `nm_1,...,nm_k` to the
corresponding values `j_1,...,j_k`. Then the call evaluates `f x` and
returns the result, but only after restoring the original
`i_1,...,i_k` values for the trace variables.

### Failure

Fails if any of the designations fails to be associated with a
registered tracing variable. Also fails if an attempt is made to set a
trace variable outside of its specified range of values.  Also fails
if the function invocation fails.

### Example

First we define a convenience function.
``` hol4
> fun pr_thm th = (print_thm th; print "\n");
val pr_thm = fn: thm -> unit
```

Now we examine a theorem with and without traces set to local values.

``` hol4
> map current_trace ["assumptions", "types"] ;
val it = [0, 0]: int list

> pr_thm EQ_SYM_EQ;
⊢ ∀x y. x = y ⇔ y = x
val it = (): unit

> with_traces [("assumptions",1), ("types",1)] pr_thm EQ_SYM_EQ;
 [] ⊢ ∀(x :α) (y :α). x = y ⇔ y = x
val it = (): unit

> map current_trace ["assumptions", "types"] ;
val it = [0, 0]: int list
```

### See also

[`Feedback`](#Feedback),
[`Feedback.traces`](#Feedback.traces),
[`Feedback.register_trace`](#Feedback.register_trace),
[`Feedback.reset_trace`](#Feedback.reset_trace),
[`Feedback.reset_traces`](#Feedback.reset_traces),
[`Feedback.set_trace`](#Feedback.set_trace),
[`Feedback.trace`](#Feedback.trace),
[`Lib.with_flag`](#Lib.with_flag)
