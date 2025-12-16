## `fst`

``` hol4
Lib.fst : ('a * 'b) -> 'a
```

------------------------------------------------------------------------

Extracts the first component of a pair.

`fst (x,y)` returns `x`.

### Failure

Never fails. However, notice that `fst (x,y,z)` fails to typecheck,
since `(x,y,z)` is not a pair.

### Example

``` hol4
- fst (1, "foo");
> val it = 1 : int

- fst (1, "foo", []);
! Toplevel input:
! fst (1, "foo", []);
!     ^^^^^^^^^^^^^^
! Type clash: expression of type
!   'g * 'h * 'i
! cannot have type
!   'j * 'k
! because the tuple has the wrong number of components

- fst (1, ("foo", []));
> val it = 1 : int
```

### See also

[`Lib.snd`](#Lib.snd)
