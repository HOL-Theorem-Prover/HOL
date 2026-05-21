## `format_WARNING`

``` hol4
Feedback.format_WARNING : string -> string -> string -> string
```

------------------------------------------------------------------------

Maps arguments of `HOL_WARNING` to a string.

The `format_WARNING` function maps three strings to a string. Usually,
the input strings are the arguments to an invocation of `HOL_WARNING`.
`format_WARNING` is the default function used by `WARNING_to_string`.

### Failure

Never fails.

### Example

``` hol4
- print (format_WARNING "Module" "function" "Gadzooks!");
<<HOL warning: Module.function: Gadzooks!>>
```

### See also

[`Feedback`](#Feedback),
[`Feedback.WARNING_to_string`](#Feedback.WARNING_to_string),
[`Feedback.format_ERR`](#Feedback.format_ERR),
[`Feedback.format_MESG`](#Feedback.format_MESG)
