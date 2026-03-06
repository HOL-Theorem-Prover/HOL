## `mk_HOL_ERR`

``` hol4
   Feedback.mk_HOL_ERR : string -> string -> string -> exn
```

------------------------------------------------------------------------

Creates an application of `HOL_ERR`.

`mk_HOL_ERR` provides a curried version of the `HOL_ERR`
exception.

### Failure

Never fails.

### Example

``` hol4
   > mk_HOL_ERR "<Module>" "<function>" "<message>";
   val it = HOL_ERR (at <Module>.<function>: <message>): exn
```

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.mk_HOL_ERRloc`](#Feedback.mk_HOL_ERRloc)
