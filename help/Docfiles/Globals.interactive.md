## `interactive`

``` hol4
   Globals.interactive : bool ref
```

------------------------------------------------------------------------

Variable specifying whether system is in interaction mode or batch mode.

The HOL system is either running via the "Read-Eval-Print" loop of the
host SML system, or it is running in batch mode, for example via
`Holmake`. Some system facilities, for example error handling, need
to access this knowledge.

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.render_exn`](#Feedback.render_exn)
