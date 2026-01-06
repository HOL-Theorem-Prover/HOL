## `top_location_of`

``` hol4
   top_location_of : hol_error -> locn.locn
```

------------------------------------------------------------------------

Extract last location added to a `hol_error`.

An invocation `top_location_of holerr` returns the location of
the top `origin` element held in `holerr`.

### Example

``` hol4
   > val exloc = let open locn in Loc (LocA(0,0), LocA(3,42)) end;
   val exloc = 1:0-4:42: locn.locn

   > top_location_of (mk_hol_error "Foo" "bar" exloc "bad input");
   val it = 1:0-4:42: locn.locn
```

### Failure

The call fails if the `origin` stack of the `hol_error` is empty.

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.origins_of`](#Feedback.origins_of),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_function_of`](#Feedback.top_function_of)
