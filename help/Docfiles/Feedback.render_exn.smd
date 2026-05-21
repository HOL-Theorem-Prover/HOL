## `render_exn`

``` hol4
   Feedback.render_exn : exn -> 'a
```

------------------------------------------------------------------------

Print `HOL_ERR` exception then recover, or not, according to
`Globals.interactive`.

The variable `Globals.interactive` is used by programs to tell whether
the HOL4 system is running interactively (i.e. is in the
Read-Eval-Print loop) or not (is running in batch mode under
`Holmake`). When the contents of `Globals.interactive` is `true`
`render_exn` raises the given exception. If the exception is not
otherwise dealt with in user code, the REPL will handle it and print
the message contents before resuming the top-level loop.

When the contents of `Globals.interactive` is `false`, `render_exn`
prints a message derived from the contents of its argument exception
then exits to the host operating system.

### Example

``` hol4
   > val () = render_exn (mk_HOL_ERR "S" "f" "-");
   Exception- HOL_ERR (at S.f: -) raised

   > Globals.interactive := false; (* for example purposes only! *)
   val it = (): unit

   > val () = render_exn (mk_HOL_ERR "S" "f" "-");
   Exception raised at S.f: -

   Process HOL exited abnormally with code 1
```

### Comment

`render_exn` attempts to display non-`HOL_ERR` exceptions sensibly.

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Globals.interactive`](#Globals.interactive)
