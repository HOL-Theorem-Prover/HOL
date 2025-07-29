## `try`

``` hol4
Lib.try : ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Apply a function and print any exceptions.

The application `try f x` evaluates `f x`; if this evaluation raises an
exception `e`, then `e` is examined and some information about it is
printed before `e` is re-raised. If `f x` evaluates to `y`, then `y` is
returned.

Often, a `HOL_ERR` exception can propagate all the way to the top level.
Unfortunately, the information held in the exception is not then
printed. `try` can often display this information.

### Failure

When application of the first argument to the second raises an
exception.

### Example

``` hol4
- mk_comb (T,F);
! Uncaught exception:
! HOL_ERR

- try mk_comb (T,F);

Exception raised at Term.mk_comb:
incompatible types
! Uncaught exception:
! HOL_ERR
```

Evaluation order can be significant. ML evaluates `try M N` by
evaluating `M` (yielding `f` say) and `N` (yielding `x` say), and then
`f` is applied to `x`. Any exceptions raised in the course of evaluating
`M` or `N` will not be detected by `try`. In such cases it is better to
use `Raise`. In the following example, the erroneous construction of an
abstraction is not detected by `try` and the exception propagates all
the way to the top level; however, `Raise` does handle the exception.

``` hol4
    - try mk_comb (T, mk_abs(T,T));
    ! Uncaught exception:
    ! HOL_ERR

    - mk_comb (T, mk_abs(T,T)) handle e => Raise e;

    Exception raised at Term.mk_abs:
    Bvar not a variable
    ! Uncaught exception:
    ! HOL_ERR
```

### See also

[`Feedback.Raise`](#Feedback.Raise), [`Lib.trye`](#Lib.trye)
