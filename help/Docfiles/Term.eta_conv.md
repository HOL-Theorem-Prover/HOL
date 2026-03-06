## `eta_conv`

``` hol4
Term.eta_conv : term -> term
```

------------------------------------------------------------------------

Performs one step of eta-reduction.

Eta-reduction is an important operation in the lambda calculus. A step
of eta-reduction may be performed by `eta_conv M`, where `M` is a lambda
abstraction of the following form: `\v. (N v)`, i.e., a lambda
abstraction whose body is an application of a term `N` to the bound
variable `v`. Moreover, `v` must not occur free in `M`. If this proviso
is met, an invocation `eta_conv (\v. (N v))` is equal to `N`.

### Failure

If `M` is not of the specified form, or if `v` occurs free in `N`.

### Example

``` hol4
- eta_conv (Term `\n. PRE n`);
> val it = `PRE` : term
```

### Comments

Eta-reduction embodies the principle of extensionality, which is basic
to the HOL logic.

### See also

[`Drule.ETA_CONV`](#Drule.ETA_CONV),
[`Drule.RIGHT_ETA`](#Drule.RIGHT_ETA)
