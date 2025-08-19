## `WARNING_outstream`

``` hol4
Feedback.WARNING_outstream : TextIO.outstream ref
```

------------------------------------------------------------------------

Controlling output stream used when printing `HOL_WARNING`

The value of reference cell `WARNING_outstream` controls where
`HOL_WARNING` prints its argument.

The default value of `WARNING_outstream` is `TextIO.stdOut`.

### Example

``` hol4
- val ostrm = TextIO.openOut "foo";
> val ostrm = <outstream> : outstream

- WARNING_outstream := ostrm;
> val it = () : unit

- HOL_WARNING "Module" "Function" "Sufferin' Succotash!";
> val it = () : unit

- TextIO.closeOut ostrm;
> val it = () : unit

- val istrm = TextIO.openIn "foo";
> val istrm = <instream> : instream

- print (TextIO.inputAll istrm);
<<HOL warning: Module.Function: Sufferin' Succotash!>>
```

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_WARNING`](#Feedback.HOL_WARNING),
[`Feedback.ERR_outstream`](#Feedback.ERR_outstream),
[`Feedback.MESG_outstream`](#Feedback.MESG_outstream),
[`Feedback.emit_WARNING`](#Feedback.emit_WARNING)
