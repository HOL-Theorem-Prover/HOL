## `definitions`

``` hol4
DB.definitions : string -> (string * thm) list
```

------------------------------------------------------------------------

All the definitions stored in the named theory.

An invocation `definitions thy`, where `thy` is the name of a currently
loaded theory segment, will return a list of the definitions stored in
that theory. Each definition is paired with its name in the result. The
string `"-"` may be used to denote the current theory segment.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment, the empty list is returned.

### Example

``` hol4
- definitions "combin";
> val it =
    [("C_DEF", |- combin$C = (\f x y. f y x)),
     ("I_DEF", |- I = S K K),
     ("K_DEF", |- K = (\x y. x)),
     ("o_DEF", |- !f g. f o g = (\x. f (g x))),
     ("S_DEF", |- S = (\f g x. f x (g x))),
     ("W_DEF", |- W = (\f x. f x x))] : (string * thm) list
```

### See also

[`DB.thy`](#DB.thy), [`DB.fetch`](#DB.fetch), [`DB.thms`](#DB.thms),
[`DB.theorems`](#DB.theorems), [`DB.axioms`](#DB.axioms),
[`DB.listDB`](#DB.listDB)
