## `message_of`

``` hol4
   message_of : hol_error -> string
```

------------------------------------------------------------------------

Extract message from a `hol_error`.

An invocation `message_of holerr` returns the message component of `holerr`.

### Example

``` hol4
   > message_of (mk_hol_error "Foo" "bar" locn.Loc_Unknown "bad input");
   val it = "bad input": string
```

### Failure

Never fails.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.origins_of`](#Feedback.origins_of),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_function_of`](#Feedback.top_function_of)
