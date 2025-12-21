## `top_structure_of`

``` hol4
   top_structure_of : hol_error -> string
```

------------------------------------------------------------------------

Extract last structure name added to a `hol_error`.

An invocation `top_structure_of holerr` returns the structure name of
the top `origin` element held in `holerr`.

### Example

``` hol4
   > top_structure_of
       (mk_hol_error "Foo" "bar" locn.Loc_Unknown "bad input")
   val it = "Foo": string
```

### Failure

The call fails if the `origin` stack of the `hol_error` is empty.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.origins_of`](#Feedback.origins_of),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.top_function_of`](#Feedback.top_function_of),
[`Feedback.top_location_of`](#Feedback.top_location_of),
[`Feedback.set_top_structure`](#Feedback.set_top_structure)
