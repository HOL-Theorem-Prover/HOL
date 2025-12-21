## `HOL_ERR`

``` hol4
   HOL_ERR : hol_error -> exn
```

------------------------------------------------------------------------

Standard HOL exception.

`HOL_ERR` is the exception that HOL functions are expected to raise
when they encounter an anomalous situation.

### Example

A `HOL_ERR` value is built from a `hol_error` value, which is
typically created with `mk_hol_error`.

``` hol4
   > val test_exn =
       HOL_ERR (mk_hol_error "Foo" "bar"
                    locn.Loc_Unknown "unexpected input")

   > raise test_exn;
   Exception- HOL_ERR (at Foo.Bar: unexpected input) raised
```

`HOL_ERR` values can also be directly constructed by `mk_HOL_ERR` or
`mk_HOL_ERRloc`.

``` hol4
   > val test_exn_again =
       mk_HOL_ERR "Foo" "bar" "unexpected input"

   > raise test_exn_again;
   Exception- HOL_ERR (at Foo.Bar: unexpected input) raised
```

### Usage patterns

#### Constructing backtraces

Information can be added to a `HOL_ERR` with `wrap_exn`:

``` hol4
   > raise wrap_exn "structA" "fnB" test_exn;
   Exception-
      HOL_ERR
        (at structA.fnB:
           at Foo.bar: unexpected input) raised
```

Location information can be included with `wrap_exn_loc`.

A common HOL programming idiom using `wrap_exn` has the following
pattern (assume function `bar` is being defined in structure `Foo`):

``` hol4
   fun bar x y =
     let val z = ...
     in
        ...
     end
     handle e as HOL_ERR _ => raise wrap_exn "Foo" "bar" e
```

If `HOL_ERR <holerr>` happens to be raised inside an invocation of
`bar`, the handler will extend the `origins` of `holerr` with `Foo`
and `bar` and raise the augmented `HOL_ERR`.

#### Scrutinizing and setting the payload

The payload of a `HOL_ERR` can be accessed by pattern matching and the
contents accessed by functions over `hol_error` such as
`top_structure_of`, `top_function_of`, and `message_of`:

``` hol4
   > val HOL_ERR holerr = test_exn

   > val (s,f,m) = (top_structure_of holerr,
                    top_function_of holerr,
                    message_of holerr)
   val f = "bar": string
   val m = "unexpected input": string
   val s = "Foo": string
```

Portions of the payload can also be set by `set_top_function` and
`set_message`.

#### Branching on the interaction mode

The variable `Globals.interactive` is used by programs to tell whether
the HOL4 system is running interactively (i.e. is in the
Read-Eval-Print loop) or not (is running in batch mode under
`Holmake`). In the REPL, an uncaught `HOL_ERR` propagates to the top
level and gets prettyprinted. In batch mode, in contrast, uncaught
exceptions are not prettyprinted and can be rendered quite
messily. The function `render_exn` can be used to write code that
displays `HOL_ERR` properly in either mode.


### See also

[`Feedback`](#Feedback),
[`Feedback.mk_hol_error`](#Feedback.mk_hol_error),
[`Feedback.mk_HOL_ERR`](#Feedback.mk_HOL_ERR),
[`Feedback.mk_HOL_ERRloc`](#Feedback.mk_HOL_ERRloc),
[`Feedback.wrap_exn`](#Feedback.wrap_exn),
[`Feedback.top_structure_of`](#Feedback.top_structure_of),
[`Feedback.top_function_of`](#Feedback.top_function_of),
[`Feedback.top_location_of`](#Feedback.top_location_of),
[`Feedback.message_of`](#Feedback.message_of),
[`Feedback.set_top_function`](#Feedback.set_top_function),
[`Feedback.set_message`](#Feedback.set_message),
[`Globals.interactive`](#Globals.interactive),
[`Feedback.render_exn`](#Feedback.render_exn)
