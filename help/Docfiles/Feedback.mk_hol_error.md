## `mk_hol_error`

``` hol4
   mk_hol_error : string -> string -> locn.locn -> string -> hol_error
```

------------------------------------------------------------------------

Create a `hol_error` value.

An invocation `mk_hol_error sname fname loc m` builds an initial
`hol_error` value where `sname` is the enclosing module name, `fname`
is the enclosing function name, `loc` is the location in the file
where the error is detected, and `m` is the error message.

`hol_error` values are used to build `HOL_ERR` exceptions.

### Example

``` hol4
   > val holerr =
       mk_hol_error "Foo" "bar" locn.Loc_Unknown "unexpected input"
   val holerr = at Foo.bar: unexpected input: hol_error

   > val holexn = HOL_ERR holerr;
   val holexn = HOL_ERR (at Foo.bar: unexpected input): exn
```

### Representation

The representation of the `hol_error` type includes

- a message
- a list of `origin` elements.

Each `origin` value includes source information such as the enclosing
SML module and function, plus the source location where the error
originated. The list of origins is typically used as a stack, and can
be used to provide a backtrace facility. The function `wrap_hol_error`
is used to push an origin onto the existing origins of a `hol_error`,
however it is more common to use `wrap_exn` on `HOL_ERR` values.

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ER),
[`Feedback.origins_of`](#Feedback.origins_of),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_function_of`](#Feedback.top_function_of),
[`Feedback.top_location_of`](#Feedback.top_location_of),
[`Feedback.set_top_function`](#Feedback.set_top_function),
[`Feedback.set_message`](#Feedback.set_message),
[`Feedback.wrap_hol_error`](#Feedback.wrap_hol_error)
