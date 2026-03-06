## `##`

``` hol4
op Lib.## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
```

------------------------------------------------------------------------

Infix combinator for applying two functions to the two projections of a
pair.

An application `(f ## g) (x,y)` is equal to `(f x, g y)`.

### Failure

If `f x` or `g y` fails.

### Example

``` hol4
- (I ## dest_imp) (strip_forall (Term `!x y z. x /\ y ==> z /\ p`));
> val it = ([`x`, `y`, `z`], (`x /\ y`, `z /\ p`))
```

### Comments

The `##` combinator can be thought of as a map operation for pairs. It
is declared as a right associative infix.

### See also

[`Lib.pair`](#Lib.pair)
