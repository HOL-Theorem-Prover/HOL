## `MESG_outstream`

``` hol4
Feedback.MESG_outstream : TextIO.outstream ref
```

------------------------------------------------------------------------

Reference to output stream used when printing `HOL_MESG`.

The value of reference cell `MESG_outstream` controls where `HOL_MESG`
prints its argument.

The default value of `MESG_outstream` is `TextIO.stdOut`.

### Example

``` hol4
- val ostrm = TextIO.openOut "foo";
> val ostrm = <outstream> : outstream

- MESG_outstream := ostrm;
> val it = () : unit

- HOL_MESG "Nattering nabobs of negativity.";
> val it = () : unit

- TextIO.closeOut ostrm;
> val it = () : unit

- val istrm = TextIO.openIn "foo";
> val istrm = <instream> : instream

- print (TextIO.inputAll istrm);
<<HOL message: Nattering nabobs of negativity.>>
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_MESG`](#Feedback.HOL_MESG),
[`Feedback.ERR_outstream`](#Feedback.ERR_outstream),
[`Feedback.WARNING_outstream`](#Feedback.WARNING_outstream),
[`Feedback.emit_MESG`](#Feedback.emit_MESG)
