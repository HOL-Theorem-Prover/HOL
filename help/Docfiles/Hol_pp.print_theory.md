## `print_theory`

``` hol4
Hol_pp.print_theory : string -> unit
```

------------------------------------------------------------------------

Print a theory on the standard output.

An invocation `print_theory s` will display the contents of the theory
segment `s` on the standard output. The string `"-"` may be used to
denote the current theory segment.

### Failure

If `s` is not the name of a loaded theory.

### Example

``` hol4
- print_theory "combin";
Theory: combin

Parents:
    bool

Term constants:
    C    :('a -> 'b -> 'c) -> 'b -> 'a -> 'c
    I    :'a -> 'a
    K    :'a -> 'b -> 'a
    S    :('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
    W    :('a -> 'a -> 'b) -> 'a -> 'b
    o    :('c -> 'b) -> ('a -> 'c) -> 'a -> 'b

Definitions:
    K_DEF  |- K = (\x y. x)
    S_DEF  |- S = (\f g x. f x (g x))
    I_DEF  |- I = S K K
    C_DEF  |- combin$C = (\f x y. f y x)
    W_DEF  |- W = (\f x. f x x)
    o_DEF  |- !f g. f o g = (\x. f (g x))

Theorems:
    o_THM  |- !f g x. (f o g) x = f (g x)
    o_ASSOC  |- !f g h. f o g o h = (f o g) o h
    K_THM  |- !x y. K x y = x
    S_THM  |- !f g x. S f g x = f x (g x)
    C_THM  |- !f x y. combin$C f x y = f y x
    W_THM  |- !f x. W f x = f x x
    I_THM  |- !x. I x = x
    I_o_ID  |- !f. (I o f = f) /\ (f o I = f)
> val it = () : unit
```

### See also

[`DB.dest_theory`](#DB.dest_theory), [`DB.thy`](#DB.thy)
