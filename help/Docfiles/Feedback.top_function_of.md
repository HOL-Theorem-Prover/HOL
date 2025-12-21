## `top_function_of`

``` hol4
   top_function_of : hol_error -> string
```

------------------------------------------------------------------------

Extract last function name added to a `hol_error`.

An invocation `top_function_of holerr` returns the function name of
the top `origin` element held in `holerr`.

### Example

``` hol4
   > top_function_of
       (mk_hol_error "Foo" "bar" locn.Loc_Unknown "bad input")
   val it = "bar": string
```

### Failure

The call fails if the `origin` stack of the `hol_error` is empty.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.origins_of`](#Feedback.origins_of),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_location_of`](#Feedback.top_location_of),
[`Feedback.set_top_function`](#Feedback.set_top_function)
