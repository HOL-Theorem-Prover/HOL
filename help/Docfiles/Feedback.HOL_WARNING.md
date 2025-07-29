## `HOL_WARNING`

``` hol4
Feedback.HOL_WARNING : string -> string -> string -> unit
```

------------------------------------------------------------------------

Prints out a message in a special format.

There are three kinds of informative messages that the `Feedback`
structure supports: errors, warnings, and messages. Errors are signalled
by the raising of an exception built from `HOL_ERR`; warnings, which are
printed by `HOL_WARNING`, are less severe than errors, and lead only to
a formatted message being printed; finally, messages have no pejorative
weight at all, and may be freely employed, via `HOL_MESG`, to keep users
informed in the normal course of processing.

`HOL_WARNING` prints out its arguments after formatting them. The
formatting is controlled by the function held in `WARNING_to_string`,
which is `format_WARNING` by default. The output stream that the message
is printed on is controlled by `WARNING_outstream`, and is
`TextIO.stdOut` by default.

A call `HOL_WARNING s1 s2 s3` is formatted with the assumption that `s1`
and `s2` are the names of the module and function, respectively, from
which the warning is emitted. The string `s3` is the actual warning
message.

### Failure

The invocation fails if the formatting or output routines fail.

### Example

``` hol4
- HOL_WARNING "Module" "function" "stern message.";
<<HOL warning: Module.function: stern message.>>
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.Raise`](#Feedback.Raise),
[`Feedback.HOL_MESG`](#Feedback.HOL_MESG),
[`Feedback.WARNING_to_string`](#Feedback.WARNING_to_string),
[`Feedback.format_WARNING`](#Feedback.format_WARNING),
[`Feedback.WARNING_outstream`](#Feedback.WARNING_outstream)
