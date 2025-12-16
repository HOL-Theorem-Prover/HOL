## `new_infix`

``` hol4
boolSyntax.new_infix : string * hol_type * int -> unit
```

------------------------------------------------------------------------

Declares a new infix constant in the current theory.

A call `new_infix ("i", ty, n)` makes `i` a right associative infix
constant in the current theory. It has binding strength of `n`, the
larger this number, the more tightly the infix will attempt to "grab"
arguments to its left and right. Note that the call to `new_infix` does
not specify the value of the constant. The constant may have a
polymorphic type, which may be arbitrarily instantiated. Like any other
infix or binder, its special parse status may be suppressed by preceding
it with a dollar sign.

### Comments

Infixes defined with `new_infix` associate to the right, i.e.,
`A <op> B <op> C` is equivalent to `A op (B <op> C)`. Some standard
infixes, with their precedences and associativities in the system are:

``` hol4
          $,  ---> 50     RIGHT
          $=  ---> 100    NONASSOC
        $==>  ---> 200    RIGHT
         $\/  ---> 300    RIGHT
         $/\  ---> 400    RIGHT
      $>, $<  ---> 450    RIGHT
    $>=, $<=  ---> 450    RIGHT
      $+, $-  ---> 500    LEFT
    $*, $DIV  ---> 600    LEFT
        $MOD  ---> 650    LEFT
        $EXP  ---> 700    RIGHT
        $o    ---> 800    RIGHT
```

Note that the arithmetic operators `+`, `-`, `*`, `DIV` and `MOD` are
left associative in hol98 releases from Taupo onwards. Non-associative
infixes (`=` above, for example) will cause parse errors if an attempt
is made to group them (e.g., `x = y = z`).

### Failure

Fails if the name is not a valid constant name.

### Example

The following shows the use of the infix and the prefix form of an infix
constant. It also shows binding resolution between infixes of different
precedence.

``` hol4
   - new_infix("orelse", Type`:bool->bool->bool`, 50);
   val it = () : unit

   - Term`T \/ T orelse F`;
   val it = `T \/ T orelse F` : term

   - “$orelse T F”;
   val it = `T orelse F` : term

   - dest_comb “T \/ T orelse F”;
   > val it = (`$orelse (T \/ T)`,  `F`) : term * term
```

### See also

[`Parse.add_infix`](#Parse.add_infix),
[`Theory.constants`](#Theory.constants),
[`Theory.new_constant`](#Theory.new_constant),
[`boolSyntax.new_binder`](#boolSyntax.new_binder),
[`Definition.new_definition`](#Definition.new_definition),
[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition)
