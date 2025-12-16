## `cv_auto_trans_pre`

``` hol4
cv_transLib.cv_auto_trans_pre : string -> thm -> thm
```

------------------------------------------------------------------------

Translates functional definitions to the `cv_compute` subset of HOL.

This is a recursive version of `cv_transLib.cv_trans_pre`. During
translation of the given HOL function, `cv_transLib.cv_auto_trans_pre`
will call itself recursively on the definitions of any
not-yet-translated constants it encounters.

As with all `auto` variants, `cv_transLib.cv_auto_trans_pre` can
sometimes translate uses of higher-order functions, such as `MAP`.

### Failure

When the translation produces a precondition that
`cv_transLib.cv_auto_trans_pre` cannot prove automatically, or
`cv_transLib.cv_termination_tac` fails to prove the termination goal of
either a recursively translated function or the top-level
translator-defined `:cv` function. For a failure on the top-level
function, the termination goal is pushed onto the goal stack.

### Example

See `cv_transLib.cv_auto_trans` and `cv_transLib.cv_trans_pre` for
relevant examples.

### Comments

Designed to produce definitions suitable for evaluation by
`cv_transLib.cv_eval`.

### See also

[`cv_transLib.cv_trans`](#cv_transLib.cv_trans),
[`cv_transLib.cv_trans_pre`](#cv_transLib.cv_trans_pre),
[`cv_transLib.cv_trans_pre_rec`](#cv_transLib.cv_trans_pre_rec),
[`cv_transLib.cv_trans_rec`](#cv_transLib.cv_trans_rec),
[`cv_transLib.cv_auto_trans`](#cv_transLib.cv_auto_trans),
[`cv_transLib.cv_auto_trans_pre_rec`](#cv_transLib.cv_auto_trans_pre_rec),
[`cv_transLib.cv_auto_trans_rec`](#cv_transLib.cv_auto_trans_rec),
[`cv_transLib.cv_eval`](#cv_transLib.cv_eval),
[`cv_transLib.cv_termination_tac`](#cv_transLib.cv_termination_tac)
