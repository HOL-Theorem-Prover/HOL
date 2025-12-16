## `format_MESG`

``` hol4
Feedback.format_MESG : string -> string
```

------------------------------------------------------------------------

Maps argument of `HOL_MESG` to a string.

The `format_MESG` function maps a string to a string. Usually, the input
string is the argument of an invocation of `HOL_MESG`. `format_MESG` is
the default function used by `MESG_to_string`.

### Failure

Never fails.

### Example

``` hol4
- print (format_MESG "Hello world.");
<<HOL message: Hello world.>>
```

### See also

[`Feedback`](#Feedback),
[`Feedback.MESG_to_string`](#Feedback.MESG_to_string),
[`Feedback.format_ERR`](#Feedback.format_ERR),
[`Feedback.format_WARNING`](#Feedback.format_WARNING)
