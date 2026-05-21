## `mk_HOL_ERRloc`

``` hol4
   Feedback.mk_HOL_ERRloc : string -> string -> locn.locn -> string -> exn
```

------------------------------------------------------------------------

Creates an application of `HOL_ERR` with location information.

`mk_HOL_ERRloc` provides a curried version of the `HOL_ERR`
exception including spcified location information.

### Failure

Never fails.

### Example

``` hol4
> val exloc = let open locn in Loc (LocA(0,0), LocA(3,42)) end;
val exloc = 1:0-4:42: locn.locn

> mk_HOL_ERRloc "<Module>" "<function>" exloc "<message>";
val it =
   HOL_ERR
     (at <Module>.<function>:
          between line 1, character 0 and line 4, character 42: <message>):
   exn
```

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.mk_HOL_ERR`](#Feedback.mk_HOL_ERR)
