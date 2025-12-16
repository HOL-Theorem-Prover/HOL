## `theorems`

``` hol4
DB.theorems : string -> (string * thm) list
```

------------------------------------------------------------------------

All the theorems stored in the named theory.

An invocation `theorems thy`, where `thy` is the name of a currently
loaded theory segment, will return a list of the theorems stored in that
theory. Axioms and definitions are excluded. Each theorem is paired with
its name in the result. The string `"-"` may be used to denote the
current theory segment.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment, the empty list is returned.

### Example

``` hol4
- theorems "combin";
> val it =
    [("I_o_ID", |- !f. (I o f = f) /\ (f o I = f)), ("I_THM", |- !x. I x = x),
     ("W_THM", |- !f x. W f x = f x x),
     ("C_THM", |- !f x y. combin$C f x y = f y x),
     ("S_THM", |- !f g x. S f g x = f x (g x)), ("K_THM", |- !x y. K x y = x),
     ("o_ASSOC", |- !f g h. f o g o h = (f o g) o h),
     ("o_THM", |- !f g x. (f o g) x = f (g x))] : (string * thm) list
```

### See also

[`DB.thy`](#DB.thy), [`DB.fetch`](#DB.fetch), [`DB.thms`](#DB.thms),
[`DB.definitions`](#DB.definitions), [`DB.axioms`](#DB.axioms),
[`DB.listDB`](#DB.listDB)
