## `$`

``` hol4
Lib.$ : ('a -> 'b) * 'a -> 'b
```

------------------------------------------------------------------------

Right-associated infix function application operator

Writing `f $ x` is another way of writing `f x`.

### Failure

Fails if `f x` would fail.

### Comments

Because `$` is right-associated, this can be a convenient way to avoid
parentheses. For example,

``` hol4
   first_x_assum $ qspec_then ‘m’ $ qx_choose_then ‘z’ strip_assume_tac
```

instead of

``` hol4
   first_x_assum (qspec_then ‘m’ (qx_choose_then ‘z’ strip_assume_tac))
```

Note also that `$` is tighter than the various `THEN` infixes, so a
tactic such as the one above can be used in a proof without needing
protection by extra parentheses.
