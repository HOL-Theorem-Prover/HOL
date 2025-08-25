## `|>`

``` hol4
op Lib.|> : 'a -> ('a -> 'b) -> 'b
```

------------------------------------------------------------------------

Infix operator for writing function application.

The expression `x |> f` is equal to `f x`. This way of writing
application has two advantages, both apparent when multiple functions
are being applied. Without using `|>`, one might write `f (g (h x))`.
With it, one writes `x |> h |> g |> f`. The latter form needs fewer
parentheses, and also makes the order in which functions will operate
correspond to a left-to-right reading.

### Failure

Never fails.
