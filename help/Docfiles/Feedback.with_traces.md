## `with_traces`

``` hol4
Feedback.with_traces : (string * int) list -> ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Invoke a function with specified levels for traces.

The `with_traces` function is used to set values for a collection of
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

In the following we make a recursive definition, temporarily setting
some traces so that aspects of the internal workings of the definition
mechanism are printed out. First we find the present values of the
trace variables:

``` hol4
> map current_trace
      ["Definition.TC extraction",
       "Definition.termination candidates"];
val it = [0, 0]: int list   (* default values *)
```
Now we make the definition while locally setting the trace values:
``` hol4
> with_traces [("Definition.TC extraction", 3),
               ("Definition.termination candidates",2)]
  Define
 `fact n = if n = 0 then 1 else n * fact (n-1)`;

# # # #
------------------------
TC extraction on clause:

fact n = if n = 0 then 1 else n * RESTRICT fact R n (n − 1)

Extracting from:

   n = 0

push_context:
   n = 0

Extracting from:

   1

push_context:
   n ≠ 0

Extracting from:

   n * RESTRICT fact R n (n − 1)

TC Capture:
 [n ≠ 0, n ≠ 0 ⇒ R (n − 1) n] ⊢ RESTRICT fact R n (n − 1) = fact (n − 1)

Termination conditions: 1
Candidate termination relations generated: 2
Termination proof successful with candidate 1:
  inv_image $< (λx. x)

Equations stored under "fact_def".
Induction stored under "fact_ind".
val it = ⊢ ∀n. fact n = if n = 0 then 1 else n * fact (n − 1): thm
```

And the trace values have been restored:
``` hol4
> map current_trace
      ["Definition.TC extraction",
       "Definition.termination candidates"]
val it = [0, 0]: int list   (* back to default values *)
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
