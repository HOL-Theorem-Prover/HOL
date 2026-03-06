## `namedCases`

``` hol4
bossLib.namedCases : string list -> tactic
```

------------------------------------------------------------------------

Case split on type of leading universally quantified variable in the
goal, using given names for introduced constructor arguments.

An application of `namedCases [s1, ..., sn]` to a goal of the form
`!x:ty. P` will perform a case split on the type `ty`, using the given
names for the arguments of the introduced constructor terms. The type
`ty` should be that of a dataype that has a so-called "nchotomy" theorem
installed in the system database of declared datatypes, accessible via
`TypeBase.nchotomy_of`.

For a datatype with `n` constructors, `n` strings are expected to be
supplied. If no strings are supplied, the system will use a default
naming scheme. If the `i`th constructor has no arguments, then `si`
should be the empty string. If the `i`th constructor has `k` arguments,
then `si` should consist of `k` space-separated names. In case a name
does not need to be specified, an underscore `_` or dash `-` can be
supplied, in which case a default name will be conjured up.

In case `ty` is a product type `ty1 # ... # tyi`, `namedCases [s]` will
iteratively case split on all product types in `ty`, thus replacing
`x:ty` by a tuple with `i` variables, the names of which are taken from
`s`.

### Failure

Fails if there is not an nchotomy theorem installed for the topmost type
constructor of `ty`. If `slist` is not the empty list,
`namedCases slist` will fail if the length of `slist` is not equal to
the number of constructors in the nchotomy theorem. Fails if the given
names for arguments of an introduced constructor are not equinumerous
with the arguments.

### Example

Consider the goal

``` hol4
     A ?- !x:num#num#bool. P x
```

Invoking `namedCases ["a b c"]` yields the goal

``` hol4
     A ?- P (a,b,c)
```

while `namedCases ["a _ _"]` yields the goal

``` hol4
     A ?- P (a,_gv0,_gv1)
```

### Example

Consider a datatype of arithmetic expressions declared as

``` hol4
   Datatype:
     arith
       = Var 'a
       | Const num
       | Add arith arith
       | Sub arith arith
       | Mult arith arith
   End
```

and the goal

``` hol4
     A ?- !x:'a arith. P x
```

Invoking `namedCases ["v","c","a1 a2", "s1 s2", "m1 m2"]` yields the
following 5 goals

``` hol4
   P (Mult m1 m2)

   P (Sub s1 s2)

   P (Add a1 a2)

   P (Const c)

   P (Var v)
```

### See also

[`bossLib.namedCases_on`](#bossLib.namedCases_on),
[`bossLib.Cases_on`](#bossLib.Cases_on),
[`bossLib.Cases`](#bossLib.Cases),
[`TypeBase.nchotomy_of`](#TypeBase.nchotomy_of)
