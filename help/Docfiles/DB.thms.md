## `thms`

``` hol4
DB.thms : string -> (string * thm) list
```

------------------------------------------------------------------------

All the theorems, definitions, and axioms stored in the named theory.

An invocation `thms thy`, where `thy` is the name of a currently loaded
theory segment, will return a list of the theorems, definitions, and
axioms stored in that theory. Each theorem is paired with its name in
the result. The string `"-"` may be used to denote the current theory
segment.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment, the empty list is returned.

### Example

``` hol4
- thms "combin";
> val it =
    [("C_DEF", |- combin$C = (\f x y. f y x)),
     ("C_THM", |- !f x y. combin$C f x y = f y x), ("I_DEF", |- I = S K K),
     ("I_o_ID", |- !f. (I o f = f) /\ (f o I = f)), ("I_THM", |- !x. I x = x),
     ("K_DEF", |- K = (\x y. x)), ("K_THM", |- !x y. K x y = x),
     ("o_ASSOC", |- !f g h. f o g o h = (f o g) o h),
     ("o_DEF", |- !f g. f o g = (\x. f (g x))),
     ("o_THM", |- !f g x. (f o g) x = f (g x)),
     ("S_DEF", |- S = (\f g x. f x (g x))),
     ("S_THM", |- !f g x. S f g x = f x (g x)),
     ("W_DEF", |- W = (\f x. f x x)), ("W_THM", |- !f x. W f x = f x x)] :
  (string * thm) list
```

### See also

[`DB.thy`](#DB.thy), [`DB.theorems`](#DB.theorems),
[`DB.axioms`](#DB.axioms), [`DB.definitions`](#DB.definitions),
[`DB.fetch`](#DB.fetch), [`DB.listDB`](#DB.listDB)
