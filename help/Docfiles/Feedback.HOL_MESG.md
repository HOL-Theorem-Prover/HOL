## `HOL_MESG`

``` hol4
Feedback.HOL_MESG : string -> unit
```

------------------------------------------------------------------------

Prints out a message in a special format.

`HOL_MESG` prints out its argument after formatting it a bit. The
formatting is controlled by the function held in `MESG_to_string`, which
is `format_MESG` by default. The output stream that the message is
printed on is controlled by `MESG_outstream`, and is `TextIO.stdOut` by
default.

There are three kinds of informative messages that the `Feedback`
structure supports: errors, warnings, and messages. Errors are signalled
by the raising of an exception built from `HOL_ERR`; warnings, which are
printed by `HOL_WARNING`, are less severe than errors, and lead to a
warning message being printed; finally, messages have no pejorative
weight at all, and may be freely employed, via `HOL_MESG`, to keep users
informed in the normal course of processing.

### Failure

The invocation fails if the formatting or output routines fail.

### Example

``` hol4
    - HOL_MESG "Ack.";
    <<HOL message: Ack.>>
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.Raise`](#Feedback.Raise),
[`Feedback.HOL_WARNING`](#Feedback.HOL_WARNING),
[`Feedback.MESG_to_string`](#Feedback.MESG_to_string),
[`Feedback.format_MESG`](#Feedback.format_MESG),
[`Feedback.MESG_outstream`](#Feedback.MESG_outstream)
