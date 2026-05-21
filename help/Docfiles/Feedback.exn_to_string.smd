## `exn_to_string`

``` hol4
Feedback.exn_to_string : exn -> string
```

------------------------------------------------------------------------

Map an exception into a string.

The function `exn_to_string` maps an exception to a string. However, in
the case of the `Interrupt` exception, it is not mapped to a string, but
is instead raised. This avoids the possibility of suppressing the
propagation of `Interrupt` to the top level.

### Failure

Never fails.

### Example

``` hol4
- exn_to_string Interrupt;
> Interrupted.

- exn_to_string Div;
> val it = "Div" : string

- print
   (exn_to_string (mk_HOL_ERR "Foo" "bar" "incomprehensible input"));

Exception raised at Foo.bar:
incomprehensible input
> val it = () : unit
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.ERR_to_string`](#Feedback.ERR_to_string)
