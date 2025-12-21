## `wrap_hol_error`

``` hol4
   wrap_hol_error : string -> string -> locn.locn -> hol_error -> hol_error
```

------------------------------------------------------------------------

Add supplementary information to a `hol_error` value.

`wrap_hol_error s1 s2 loc holerr` where `s1` is typically the name of
a structure and `s2` is typically the name of a function and `loc` is
a location, augments `holerr` by pushing `(s1,s2,loc)` on to the stack of
`origin` elements held in `holerr`.

### Failure

Never fails.

### Example

``` hol4
   > val orig = mk_hol_error "Foo" "bar" locn.Loc_Unknown "mucho badness";
   val orig = at Foo.bar: mucho badness: hol_error

   > wrap_hol_error "Fred" "barney" locn.Loc_Unknown orig;
   val it =
      at Fred.barney:
      at Foo.bar: mucho badness: hol_error
```

### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error)
