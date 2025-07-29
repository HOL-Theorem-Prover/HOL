## `W`

``` hol4
Lib.W : ('a -> 'a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Duplicates function argument : `W f x` equals `f x x`.

The `W` combinator can be understood as a planner: in the application
`f x x`, the function `f` can scrutinize `x` and generate a function
that then gets applied to `x`.

### Failure

`W f` never fails. `W f x` fails if `f x` fails or if `f x x` fails.

### Example

``` hol4
- load "tautLib";
- tautLib.TAUT_PROVE (Term `(a = b) = (~a = ~b)`);
> val it = |- (a = b) = (~a = ~b) : thm

- W (GENL o free_vars o concl) it;
> val it = |- !b a. (a = b) = (~a = ~b) : thm
```

### See also

[`Lib.##`](#Lib..IAD), [`Lib.C`](#Lib.C), [`Lib.I`](#Lib.I),
[`Lib.K`](#Lib.K), [`Lib.S`](#Lib.S)
