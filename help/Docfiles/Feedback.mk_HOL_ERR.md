## `mk_HOL_ERR`

``` hol4
Feedback.mk_HOL_ERR : string -> string -> string -> exn
```

------------------------------------------------------------------------

Creates an application of `HOL_ERR`.

`mk_HOL_ERR` provides a curried interface to the standard `HOL_ERR`
exception; experience has shown that this is often more convenient.

### Failure

Never fails.

### Example

``` hol4
- mk_HOL_ERR "Module" "function" "message"

> val it = HOL_ERR : exn

- print(exn_to_string it);

Exception raised at Module.function:
message
> val it = () : unit
```

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.error_record`](#Feedback.error_record)
