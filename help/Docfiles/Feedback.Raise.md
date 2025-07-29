## `Raise`

``` hol4
Feedback.Raise : exn -> 'a
```

------------------------------------------------------------------------

Print an exception before re-raising it.

The `Raise` function prints out information about its argument exception
before re-raising it. It uses the value of `ERR_to_string` to format the
message, and prints the information on the `outstream` held in
`ERR_outstream`.

### Failure

Never fails, since it always succeeds in raising the supplied exception.

### Example

``` hol4
- Raise (mk_HOL_ERR "Foo" "bar" "incomprehensible input");

Exception raised at Foo.bar:
incomprehensible input
! Uncaught exception:
! HOL_ERR
```

### See also

[`Feedback`](#Feedback),
[`Feedback.ERR_to_string`](#Feedback.ERR_to_string),
[`Feedback.ERR_outstream`](#Feedback.ERR_outstream),
[`Lib.try`](#Lib.try), [`Lib.trye`](#Lib.trye)
