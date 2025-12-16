## `add_infix`

``` hol4
Parse.add_infix : string * int * HOLgrammars.associativity -> unit
```

------------------------------------------------------------------------

Adds a string as an infix with the given precedence and associativity to
the term grammar.

This function adds the given string to the global term grammar such that
the string

``` hol4
   <str1> s <str2>
```

will be parsed as

``` hol4
   s <t1> <t2>
```

where `<str1>` and `<str2>` have been parsed to two terms `<t1>` and
`<t2>`. The parsing process does not pay any attention to whether or not
`s` corresponds to a constant or not. This resolution happens later in
the parse, and will result in either a constant or a variable with name
`s`. In fact, if this name is overloaded, the eventual term generated
may have a constant of quite a different name again; the resolution of
overloading comes as a separate phase (see the entry for `overload_on`).

### Failure

`add_infix` fails if the precedence level chosen for the new infix is
the same as a different type of grammar rule (e.g., suffix or binder),
or if the specified precedence level has infixes already but of a
different associativity.

It is also possible that the choice of string `s` will result in an
ambiguous grammar. This will be marked with a warning. The parser may
behave in strange ways if it encounters ambiguous phrases, but will work
normally otherwise.

### Example

Though we may not have `+` defined as a constant, we can still define it
as an infix for the purposes of printing and parsing:

``` hol4
   - add_infix ("+", 500, HOLgrammars.LEFT);
   > val it = () : unit

   - val t = Term`x + y`;
   <<HOL message: inventing new type variable names: 'a, 'b, 'c.>>
   > val t = `x + y` : term
```

We can confirm that this new infix has indeed been parsed that way by
taking the resulting term apart:

``` hol4
   - dest_comb t;
   > val it = (`$+ x`, `y`) : term * term
```

With its new status, `+` has to be "quoted" with a dollar-sign if we
wish to use it in a position where it is not an infix, as in the binding
list of an abstraction:

``` hol4
   - Term`\$+. x + y`;
   <<HOL message: inventing new type variable names: 'a, 'b, 'c.>>
   > val it = `\$+. x + y` : term
   - dest_abs it;
   > val it = (`$+`,`x + y`) : term * term
```

The generation of three new type variables in the examples above
emphasises the fact that the terms in the first example and the body of
the second are really no different from `f x y` (where `f` is a
variable), and don't have anything to do with the constant for addition
from `arithmeticTheory`. The new `+` infix is left associative:

``` hol4
   - Term`x + y + z`;
   <<HOL message: inventing new type variable names: 'a, 'b.>>
   > val it = `x + y + z` : term

   - dest_comb it;
   > val it = (`$+ (x + y)`, `z`) : term * term
```

It is also more tightly binding than `/\` (which has precedence 400 by
default):

``` hol4
   - Term`p /\ q + r`;
   <<HOL message: inventing new type variable names: 'a, 'b.>>
   > val it = `p /\ q + r` : term

   - dest_comb it;
   > val it = (`$/\ p`, `q + r`) : term * term
```

An attempt to define a right associative operator at the same level
fails:

``` hol4
   Lib.try add_infix("-", 500, HOLgrammars.RIGHT);

   Exception raised at Parse.add_infix:
   Grammar Error: Attempt to have differently associated infixes
                  (RIGHT and LEFT) at same level
```

Similarly we can't define an infix at level 900, because this is where
the (true prefix) rule for logical negation (`~`) is.

``` hol4
   - Lib.try add_infix("-", 900, HOLgrammars.RIGHT);

   Exception raised at Parse.add_infix:
   Grammar Error: Attempt to have different forms at same level
```

Finally, an attempt to have a second `+` infix at a different precedence
level causes grief when we later attempt to use the parser:

``` hol4
   - add_infix("+", 400, HOLgrammars.RIGHT);
   > val it = () : unit

   - Term`p + q`;
   <<HOL warning: Parse.Term: Grammar ambiguous on token pair + and +,
                  and probably others too>>
   <<HOL message: inventing new type variable names: 'a, 'b, 'c>>
   > val it = ``p + q`` : term
```

In this situation, the behaviour of the parser will become quite
unpredictable whenever the `+` token is encountered. In particular, `+`
may parse with either fixity.

Most use of infixes will want to have them associated with a particular
constant in which case the definitional principles
(`new_infixl_definition` etc) are more likely to be appropriate.
However, a development of a theory of abstract algebra may well want to
have infix variables such as `+` above.

### Comments

As with other functions in the `Parse` structure, there is a companion
`temp_add_infix` function, which has the same effect on the global
grammar, but which does not cause this effect to persist when the
current theory is exported.

### See also

[`Parse.add_rule`](#Parse.add_rule),
[`Parse.add_listform`](#Parse.add_listform), [`Parse.Term`](#Parse.Term)
