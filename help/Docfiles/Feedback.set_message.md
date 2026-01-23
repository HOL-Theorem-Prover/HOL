## `set_message`

``` hol4
   set_message : string -> hol_error -> hol_error
```

------------------------------------------------------------------------

Overwrite message component of a `hol_error` value.

### Example

``` hol4
   > set_message "BIG problem!"
       (mk_hol_error "Foo" "bar" locn.Loc_Unknown "bad input");
   val it = at Foo.bar: BIG problem!: hol_error
```

### Failure

Never fails.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.set_top_function`](#Feedback.set_top_function)
