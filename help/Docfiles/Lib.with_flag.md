## `with_flag`

``` hol4
Lib.with_flag : 'a ref * 'a -> ('b -> 'c) -> 'b -> 'c
```

------------------------------------------------------------------------

Apply a function under a particular flag setting.

An invocation `with_flag (r,v) f x` sets the reference variable `r` to
the value `v`, then evaluates `f x`, then resets `r` to its original
value, and returns the value of `f x`.

### Failure

Fails if `f x` fails. In that case, `r` is reset to its original value
before raising the exception from `f x`.

### Example

``` hol4
- fun print_term_nl tm = (print_term tm; print "\n");
> val print_term_nl = fn : term -> unit

- with_flag (show_types, true) print_term_nl (concl T_DEF);
T = ((\(x :bool). x) = (\(x :bool). x))
> val it = () : unit

- print_term_nl (concl T_DEF);
T = ((\(x. x) = (\x. x))
> val it = () : unit
```

### See also

[`Feedback.traces`](#Feedback.traces),
[`Feedback.register_btrace`](#Feedback.register_btrace),
[`Feedback.trace`](#Feedback.trace), [`Lib.time`](#Lib.time)
