## `wrap_exn`

``` hol4
Feedback.wrap_exn : string -> string -> exn -> exn
```

------------------------------------------------------------------------

Adds supplementary information to an application of `HOL_ERR`.

`wrap_exn s1 s2 (HOL_ERR{origin_structure,origin_function,source_location,message})`
where `s1` typically denotes a structure and `s2` typically denotes a
function, returns

`HOL_ERR{origin_structure=s1,origin_function=s2,source_location,message}`

where `origin_structure` and `origin_function` have been added to the
`message` field. This can be used to achieve a kind of backtrace when an
error occurs.

In MoscowML, the `interrupt` signal in Unix is mapped into the
`Interrupt` exception. If `wrap_exn` were to translate an interrupt into
a `HOL_ERR` exception, crucial information might be lost. For this
reason, `wrap_exn s1 s2 Interrupt` raises the `Interrupt` exception.

Every other exception is mapped into an application of `HOL_ERR` by
`wrap_exn`.

### Failure

Never fails.

### Example

In the following example, the original `HOL_ERR` is from `Foo.bar`.
After `wrap_exn` is called, the `HOL_ERR` is from `Fred.barney` and its
message field has been augmented to reflect the original source of the
exception.

``` hol4
    - val test_exn = mk_HOL_ERR "Foo" "bar" "incomprehensible input";
    > val test_exn = HOL_ERR : exn

    - wrap_exn "Fred" "barney" test_exn;
    > val it = HOL_ERR : exn

    - print(exn_to_string it);

    Exception raised at Fred.barney:
    Foo.bar - incomprehensible input
```

The following example shows how `wrap_exn` treats the `Interrupt`
exception.

``` hol4
    - wrap_exn "Fred" "barney" Interrupt;
    > Interrupted.
```

The following example shows how `wrap_exn` translates all exceptions
that aren't either `HOL_ERR` or `Interrupt` into applications of
`HOL_ERR`.

``` hol4
    - wrap_exn "Fred" "barney" Div;
    > val it = HOL_ERR : exn

    - print(exn_to_string it);

    Exception raised at Fred.barney:
    Div
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR)
