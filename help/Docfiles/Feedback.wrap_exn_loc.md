## `wrap_exn_loc`

``` hol4
   Feedback.wrap_exn_loc : string -> string -> locn.locn -> exn -> exn
```

------------------------------------------------------------------------

Adds supplementary information to a `HOL_ERR` exception, with location.

`wrap_exn_loc s1 s2 loc holerr` behaves like `wrap_exn` except that it
includes the given location information with the other data pushed on
to the `origins` stack.

### Failure

Raises the exception argument when the exception argument is
`Interrupt`.

### Example

In the following example, the original `HOL_ERR` is from `Foo.bar`.
After `wrap_exn_loc` is called, the `HOL_ERR` is from `Fred.barney` and its
message field has been augmented to reflect the original source of the
exception.

``` hol4
   > val orig_exn = mk_HOL_ERR "Foo" "bar" "incomprehensible input";
   val orig_exn = HOL_ERR (at Foo.bar: incomprehensible input): exn

   > val exloc = let open locn in Loc (LocA(0,0), LocA(3,42)) end;
   val exloc = 1:0-4:42: locn.locn

   > wrap_exn_loc "Fred" "barney" exloc orig_exn;
   val it =
      HOL_ERR
        (at Fred.barney: between line 1, character 0 and line 4, character 42:
           at Foo.bar: incomprehensible input): exn

```

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.wrap_exn`](#Feedback.wrap_exn)
