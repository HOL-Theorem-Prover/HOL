## `add_numeral_form`

``` hol4
Parse.add_numeral_form : (char * string option) -> unit
```

------------------------------------------------------------------------

Adds support for numerals of differing types to the
parser/pretty-printer.

This function allows the user to extend HOL's parser and pretty-printer
so that they recognise and print numerals. A numeral in this context is
a string of digits. Each such string corresponds to a natural number
(i.e., the HOL type `num`) but `add_numeral_form` allows for numerals to
stand for values in other types as well.

A call to `add_numeral_form(c,s)` augments the global term grammar in
two ways. Firstly, in common with the function `add_bare_numeral_form`
(q.v.), it allows the user to write a single letter suffix after a
numeral (the argument `c`). The presence of this character specifies `s`
as the "injection function" which is to be applied to the natural number
denoted by the preceding digits.

Secondly, the constant denoted by the `s` argument is overloaded to be
one of the possible resolutions of an internal, overloaded operator,
which is invisibly wrapped around all numerals that appear without a
character suffix. After applying `add_numeral_form`, the function
denoted by the argument `s` is now a possible resolution of this
overloading, so numerals can now be seen as members of the range of the
type of `s`.

Finally, if `s` is not `NONE`, the constant denoted by `s` is overloaded
to be one of the possible resolutions of the string `&`. This operator
is thus the standard way of writing the injection function from `:num`
into other numeric types.

The injection function specifed by argument `s` is either the constant
with name `s0`, if `s` is of the form `SOME s0`, or the identity
function if `s` is `NONE`. Using `add_numeral_form` with `NONE` for this
parameter is done in the development of `arithmeticTheory`, and should
not be done subsequently.

### Failure

Fails if `arithmeticTheory` is not loaded, as this is where the basic
constants implementing natural number numerals are defined. Also fails
if there is no constant with the given name, or if it doesn't have type
`:num -> 'a` for some `'a`. Fails if `add_bare_numeral_form` would also
fail on this input.

### Example

The natural numbers are given numeral forms as follows:

``` hol4
   val _ = add_numeral_form (#"n", NONE);
```

This is done in `arithmeticTheory` so that after it is loaded, one can
write numerals and have them parse (and print) as natural numbers.
However, later in the development, in `integerTheory`, numeral forms for
integers are also introduced:

``` hol4
   val _ = add_numeral_form(#"i", SOME "int_of_num");
```

Here `int_of_num` is the name of the function which injects natural
numbers into integers. After this call is made, numeral strings can be
treated as integers or natural numbers, depending on the context.

``` hol4
   - load "integerTheory";
   > val it = () : unit
   - Term`3`;
   <<HOL message: more than one resolution of overloading was possible.>>
   > val it = `3` : term
   - type_of it;
   > val it = `:int` : hol_type
```

The parser has chosen to give the string "3" integer type (it will
prefer the most recently specified possibility, in common with
overloading in general). However, numerals can appear with natural
number type in appropriate contexts:

``` hol4
   - Term`(SUC 3, 4 + ~x)`;
   > val it = `(SUC 3,4 + ~x)` : term
   - type_of it;
   > val it = `:num # int` : hol_type
```

Moreover, one can always use the character suffixes to absolutely
specify the type of the numeral form:

``` hol4
   - Term`f 3 /\ p`;
   <<HOL message: more than one resolution of overloading was possible.>>
   > val it = `f 3 /\ p` : term

   - Term`f 3n /\ p`;
   > val it = `f 3 /\ p` : term
```

### Comments

Overloading on too many numeral forms is a sure recipe for confusion.

### See also

[`Parse.add_bare_numeral_form`](#Parse.add_bare_numeral_form),
[`Parse.overload_on`](#Parse.overload_on),
[`Parse.show_numeral_types`](#Parse.show_numeral_types)
