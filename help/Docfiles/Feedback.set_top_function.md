## `set_top_function`

``` hol4
   set_top_function : string -> hol_error -> hol_error
```

------------------------------------------------------------------------

Overwrite last function name added to a `hol_error`.

An invocation `set_top_function holerr` replaces the function name of
the top `origin` element held in `holerr`.

### Example

``` hol4
   > set_top_function "new_name"
       (mk_hol_error "Foo" "bar" locn.Loc_Unknown "bad input");
   val it = at Foo.new_name: bad input: hol_error
```

### Failure

The call fails if the `origin` stack of the `hol_error` is empty.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.top_function_of`](#Feedback.top_function_of),
[`Feedback.set_message`](#Feedback.set_messsage)
