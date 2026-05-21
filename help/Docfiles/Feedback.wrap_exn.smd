## `wrap_exn`

``` hol4
   Feedback.wrap_exn : string -> string -> exn -> exn
```

------------------------------------------------------------------------

Adds supplementary information to a `HOL_ERR` exception.

`wrap_exn s1 s2 (HOL_ERR e)` where `s1` is typically the name of a
structure and `s2` is typically the name of a function, augments `e`
by pushing `(s1,s2)` on to the stack of `origin` elements held in
`e`. This can be used to achieve a kind of backtrace when an error
occurs. `wrap_exn` can be applied to any exception.

Almost every non-`HOL_ERR` exception is mapped into an application of
`HOL_ERR` by `wrap_exn`, but there is one special case: interrupts. A
Unix `interrupt` signal is mapped into the `Interrupt` exception. If
`wrap_exn` were to translate an `Interrupt` exception into a `HOL_ERR`
exception, crucial information might be lost. For this reason,
`wrap_exn s1 s2 Interrupt` raises the `Interrupt` exception.

### Failure

Raises the exception argument when the exception argument is
`Interrupt`.

### Example

In the following example, the original `HOL_ERR` is from `Foo.bar`.
After `wrap_exn` is called, the `HOL_ERR` is from `Fred.barney` and its
message field has been augmented to reflect the original source of the
exception.

``` hol4
   > val orig_exn = mk_HOL_ERR "Foo" "bar" "incomprehensible input";
   val orig_exn = HOL_ERR (at Foo.bar: incomprehensible input): exn

   > wrap_exn "Fred" "barney" orig_exn;
   val it =
      HOL_ERR
        (at Fred.barney:
           at Foo.bar: incomprehensible input): exn
```

The following example shows how `wrap_exn` treats the `Interrupt`
exception.

``` hol4
   > wrap_exn "Fred" "barney" Interrupt;
   Exception- Interrupt raised
```

The following example shows how `wrap_exn` translates all exceptions
that aren't either `HOL_ERR` or `Interrupt` into applications of
`HOL_ERR`.

``` hol4
   > wrap_exn "Fred" "barney" Div;
   val it = HOL_ERR (at Fred.barney: Div): exn
```

### See also

[`Feedback`](#Feedback),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.wrap_exn_loc`](#Feedback.wrap_exn_loc)
