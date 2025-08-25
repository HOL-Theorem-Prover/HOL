## `format_ERR`

``` hol4
Feedback.format_ERR : error_record -> string
```

------------------------------------------------------------------------

Maps argument record of `HOL_ERR` to a string.

The `format_ERR` function maps the argument of an application of
`HOL_ERR` to a string. It is the default function used by
`ERR_to_string`.

### Failure

Never fails.

### Example

``` hol4
- print
   (format_ERR {origin_structure = "Foo",
                origin_function = "bar",
                message = "incomprehensible input"});

Exception raised at Foo.bar:
incomprehensible input
> val it = () : unit
```

### See also

[`Feedback`](#Feedback),
[`Feedback.ERR_to_string`](#Feedback.ERR_to_string),
[`Feedback.format_MESG`](#Feedback.format_MESG),
[`Feedback.format_WARNING`](#Feedback.format_WARNING)
