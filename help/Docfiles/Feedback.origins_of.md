## `origins_of`

``` hol4
   origins_of : hol_error -> origin list
```

------------------------------------------------------------------------

Extract `origin` stack from a `hol_error`.

An invocation `origins_of holerr` returns the list of `origin`
elements held in `holerr`.

### Example

``` hol4
   > origins_of (mk_hol_error "Foo" "bar" locn.Loc_Unknown "bad input");
   val it =
      [{origin_function = "bar", origin_structure = "Foo",
        source_location = <??>}]: origin list
```

### Failure

Never fails.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_function_of`](#Feedback.top_function_of)
