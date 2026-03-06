## `tryfind`

``` hol4
Lib.tryfind : ('a -> 'b) -> 'a list -> 'b
```

------------------------------------------------------------------------

Returns the result of the first successful application of a function to
the elements of a list.

`tryfind f [x1,...,xn]` returns `(f xi)` for the first `xi` in the list
for which application of `f` does not raise an exception. However, if
`Interrupt` is raised in the course of some application of `f xi`, then
`tryfind f [x1,...,xn]` raises `Interrupt`.

### Failure

Fails if the application of `f` fails for all elements in the list. This
will always be the case if the list is empty.

### See also

[`Lib.first`](#Lib.first), [`Lib.mem`](#Lib.mem),
[`Lib.exists`](#Lib.exists), [`Lib.all`](#Lib.all),
[`Lib.assoc`](#Lib.assoc), [`Lib.rev_assoc`](#Lib.rev_assoc),
[`Lib.assoc1`](#Lib.assoc1), [`Lib.assoc2`](#Lib.assoc2)
