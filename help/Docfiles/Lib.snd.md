## `snd`

``` hol4
Lib.snd : ('a * 'b) -> 'b
```

------------------------------------------------------------------------

Extracts the second component of a pair.

`snd (x,y)` returns `y`.

### Failure

Never fails. However, notice that `snd (x,y,z)` fails to typecheck,
since `(x,y,z)` is not a pair.

### Example

``` hol4
    - snd (1, "foo");
    > val it = "foo" : string

    - snd (1, "foo", []);
    ! Toplevel input:
    ! snd (1, "foo", []);
    !     ^^^^^^^^^^^^^^
    ! Type clash: expression of type
    !   'g * 'h * 'i
    ! cannot have type
    !   'j * 'k
    ! because the tuple has the wrong number of components

    - snd (1, ("foo", ()));
    > val it = ("foo", ()) : string * unit
```

### See also

[`Lib`](#Lib), [`Lib.fst`](#Lib.fst)
