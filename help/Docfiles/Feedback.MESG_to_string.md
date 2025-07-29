## `MESG_to_string`

``` hol4
Feedback.MESG_to_string : (string -> string) ref
```

------------------------------------------------------------------------

Alterable function for formatting `HOL_MESG`.

`MESG_to_string` is a reference to a function for formatting the
argument to an application of `HOL_MESG`.

The default value of `MESG_to_string` is `format_MESG`.

### Example

``` hol4
    - fun alt_MESG_report s = String.concat["Dear HOL user: ", s, "\n"];

    - MESG_to_string := alt_MESG_report;

    - HOL_MESG "Hi there."

    Dear HOL user: Hi there.
    > val it = () : unit
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_MESG`](#Feedback.HOL_MESG),
[`Feedback.format_MESG`](#Feedback.format_MESG),
[`Feedback.ERR_to_string`](#Feedback.ERR_to_string),
[`Feedback.WARNING_to_string`](#Feedback.WARNING_to_string)
