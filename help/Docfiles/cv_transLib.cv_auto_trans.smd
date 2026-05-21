## `cv_auto_trans`

``` hol4
cv_transLib.cv_auto_trans : thm -> unit
```

------------------------------------------------------------------------

Translates functional definitions to the `cv_compute` subset of HOL.

This is a recursive version of `cv_transLib.cv_trans`. During
translation of the given HOL function, `cv_transLib.cv_auto_trans` will
call itself recursively on the definitions of any not-yet-translated
constants it encounters.

As with all `auto` variants, `cv_transLib.cv_auto_trans` can sometimes
translate uses of higher-order functions, such as `MAP`.

### Failure

When the translation produces a precondition that
`cv_transLib.cv_auto_trans` cannot prove automatically, or
`cv_transLib.cv_termination_tac` fails to prove the termination goal of
either a recursively translated function or the top-level
translator-defined `:cv` function. For a failure on the top-level
function, the termination goal is pushed onto the goal stack.

### Example

``` hol4
> Definition list_add1_def:
    list_add1 xs = MAP SUC xs
  End
Definition has been stored under "list_add1_def"
val list_add1_def = ⊢ ∀xs. list_add1 xs = MAP SUC xs: thm
> cv_auto_trans list_add1_def;
Equations stored under "cv_MAP_SUC_def".
Induction stored under "cv_MAP_SUC_ind".
Finished translating MAP_SUC, stored in cv_MAP_SUC_thm
Finished translating list_add1, stored in cv_list_add1_thm
val it = (): unit
> cv_eval “list_add1 [5; 6; 7]”;
val it = ⊢ list_add1 [5; 6; 7] = [6; 7; 8]: thm
```

### Comments

Designed to produce definitions suitable for evaluation by
`cv_transLib.cv_eval`.

### See also

[`cv_transLib.cv_trans`](#cv_transLib.cv_trans),
[`cv_transLib.cv_trans_pre`](#cv_transLib.cv_trans_pre),
[`cv_transLib.cv_trans_pre_rec`](#cv_transLib.cv_trans_pre_rec),
[`cv_transLib.cv_trans_rec`](#cv_transLib.cv_trans_rec),
[`cv_transLib.cv_auto_trans_pre`](#cv_transLib.cv_auto_trans_pre),
[`cv_transLib.cv_auto_trans_pre_rec`](#cv_transLib.cv_auto_trans_pre_rec),
[`cv_transLib.cv_auto_trans_rec`](#cv_transLib.cv_auto_trans_rec),
[`cv_transLib.cv_eval`](#cv_transLib.cv_eval),
[`cv_transLib.cv_termination_tac`](#cv_transLib.cv_termination_tac)
