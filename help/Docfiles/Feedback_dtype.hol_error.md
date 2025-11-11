## `hol_error`

``` hol4
   type Feedback.origin =
      {origin_structure:string,
       origin_function:string,
       source_location : locn.locn}

   datatype Feedback.hol_error =
      HOL_ERROR of
        {origins : origin list,
         message : string}
```

------------------------------------------------------------------------

Payload of `HOL_ERR`.

The payload of the `HOL_ERR` exception, `hol_error`, is a single
constructor datatype that groups a list of "origins" with a
message. An `origin` provides information about where (host structure,
calling function, source location) an exception has been raised. Since
exceptions can be re-raised, the `origin` list can be used to
construct a useful backtrace to help track down program errors.

### Example

A `hol_error` can be directly constructed but it is preferable to use
the higher level entrypoint `mk_hol_error`:

``` hol4
   > val holerr =
       mk_hol_error "Struct" "Fn" locn.Loc_Unknown "<Msg>"
   # val holerr = at Struct.Fn: <Msg>: hol_error
```

A builtin prettyprinter is used to display `hol_error` values.

### Accessing `hol_error` components

The message and origins of a `hol_error` value can be obtained via
`message_of` and `origins_of`. The subcomponents of the head of the
`origins` list can be obtained with `top_structure_of`,
`top_function_of`, and `top_location_of`

### Changing `hol_error` components

To augment an existing `hol_error` with new origin information, use
`wrap_hol_error`. However, it is usually preferable to use
`wrap_exn`. To set the message to a new value, use `set_message`, and
to set the function component of the head origin, use
`set_top_function`.

### Comment

For obscure reasons, `hol_error` is defined in structure
`Feedback_dtype` and duplicated in `Feedback`.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_function_of`](#Feedback.top_function_of),
[`Feedback.top_location_of`](#Feedback.top_location_of),
[`Feedback.origins_of`](#Feedback.origins_of),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.set_message`](#Feedback.set_message),
[`Feedback.set_top_function`](#Feedback.set_top_function),
[`Feedback.wrap_exn`](#Feedback.wrap_exn)
