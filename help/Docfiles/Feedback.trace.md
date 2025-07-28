## `trace` {#Feedback.trace}


```
trace : string * int -> ('a -> 'b) -> 'a -> 'b
```



Invoke a function with a specified level of tracing.


The `trace` function is used to set the value of a tracing variable
for the duration of one top-level function call.

A call to `trace (nm,i) f x` attempts to set the tracing variable
associated with the string `nm` to value `i`.  Then it evaluates
`f x` and returns the resulting value after restoring the
trace level of `nm`.

### Failure

Fails if the name given is not associated with a registered tracing
variable. Also fails if the function invocation fails.

### Example

    
    - load "mesonLib";
    
    - trace ("meson",2) prove
         (concl SKOLEM_THM,mesonLib.MESON_TAC []);
    
    0 inferences so far. Searching with maximum size 0.
    0 inferences so far. Searching with maximum size 1.
    Internal goal solved with 2 MESON inferences.
    0 inferences so far. Searching with maximum size 0.
    0 inferences so far. Searching with maximum size 1.
    Internal goal solved with 2 MESON inferences.
    0 inferences so far. Searching with maximum size 0.
    0 inferences so far. Searching with maximum size 1.
    Internal goal solved with 2 MESON inferences.
    0 inferences so far. Searching with maximum size 0.
    0 inferences so far. Searching with maximum size 1.
    Internal goal solved with 2 MESON inferences.
      solved with 2 MESON inferences.
    
    > val it = |- !P. (!x. ?y. P x y) = ?f. !x. P x (f x) : thm
    
    - traces();
    
    > val it =
        [{default = 1, name = "meson", trace_level = 1},
         {default = 10, name = "Subgoal number", trace_level = 10},
         {default = 0, name = "Rewrite", trace_level = 0},
         {default = 0, name = "Ho_Rewrite", trace_level = 0}]
    



### See also

[`Feedback`](#Feedback), [`Feedback.register_trace`](#Feedback.register_trace), [`Feedback.reset_trace`](#Feedback.reset_trace), [`Feedback.reset_traces`](#Feedback.reset_traces), [`Feedback.set_trace`](#Feedback.set_trace), [`Feedback.traces`](#Feedback.traces), [`Lib.with_flag`](#Lib.with_flag)

