## `new_recursive_definition`

``` hol4
Prim_rec.new_recursive_definition : {name:string, def:term, rec_axiom:thm} -> thm
```

------------------------------------------------------------------------

Defines a primitive recursive function over a concrete recursive type.

`new_recursive_definition` provides a facility for defining primitive
recursive functions on arbitrary concrete recursive types. `name` is a
name under which the resulting definition will be saved in the current
theory segment. `def` is a term giving the desired primitive recursive
function definition. `rec_axiom` is the primitive recursion theorem for
the concrete type in question; this must be a theorem obtained from
`define_type`. The value returned by `new_recursive_definition` is a
theorem which states the primitive recursive definition requested by the
user. This theorem is derived by formal proof from an instance of the
general primitive recursion theorem given as the second argument.

A theorem `th` of the form returned by `define_type` is a primitive
recursion theorem for an automatically-defined concrete type `ty`. Let
`C1`, ..., `Cn` be the constructors of this type, and let '`(Ci vs)`'
represent a (curried) application of the `i`th constructor to a sequence
of variables. Then a curried primitive recursive function `fn` over `ty`
can be specified by a conjunction of (optionally universally-quantified)
clauses of the form:

``` hol4
   fn v1 ... (C1 vs1) ... vm  =  body1   /\
   fn v1 ... (C2 vs2) ... vm  =  body2   /\
                             .
                             .
   fn v1 ... (Cn vsn) ... vm  =  bodyn
```

where the variables `v1`, ..., `vm`, `vs` are distinct in each clause,
and where in the `i`th clause `fn` appears (free) in `bodyi` only as
part of an application of the form:

``` hol4
   fn t1 ... v ... tm
```

in which the variable `v` of type `ty` also occurs among the variables
`vsi`.

If `tm` is a conjunction of clauses, as described above, then
evaluating:

``` hol4
   new_recursive_definition{name=name, rec_axiom=th, def=tm}
```

automatically proves the existence of a function `fn` that satisfies the
defining equations supplied as the fourth argument, and then declares a
new constant in the current theory with this definition as its
specification. This constant specification is returned as a theorem and
is saved in the current theory segment under the name `name`.

`new_recursive_definition` also allows the supplied definition to omit
clauses for any number of constructors. If a defining equation for the
`i`th constructor is omitted, then the value of `fn` at that
constructor:

``` hol4
   fn v1 ... (Ci vsi) ... vn
```

is left unspecified (`fn`, however, is still a total function).

### Failure

A call to `new_recursive_definition` fails if the supplied theorem is
not a primitive recursion theorem of the form returned by `define_type`;
if the term argument supplied is not a well-formed primitive recursive
definition; or if any other condition for making a constant
specification is violated (see the failure conditions for
`new_specification`).

### Example

Given the following primitive recursion theorem for labelled binary
trees:

``` hol4
   |- !f0 f1.
        ?! fn.
        (!x. fn(LEAF x) = f0 x) /\
        (!b1 b2. fn(NODE b1 b2) = f1(fn b1)(fn b2)b1 b2)
```

`new_recursive_definition` can be used to define primitive recursive
functions over binary trees. Suppose the value of `th` is this theorem.
Then a recursive function `Leaves`, which computes the number of leaves
in a binary tree, can be defined recursively as shown below:

``` hol4
   - val Leaves = new_recursive_definition
           {name = "Leaves",
            rec_axiom = th,
            def= “(Leaves (LEAF (x:'a)) = 1) /\
                    (Leaves (NODE t1 t2) = (Leaves t1) + (Leaves t2))”};
    > val Leaves =
        |- (!x. Leaves (LEAF x) = 1) /\
           !t1 t2. Leaves (NODE t1 t2) = Leaves t1 + Leaves t2 : thm
```

The result is a theorem which states that the constant `Leaves`
satisfies the primitive-recursive defining equations supplied by the
user.

The function defined using `new_recursive_definition` need not, in fact,
be recursive. Here is the definition of a predicate `IsLeaf`, which is
true of binary trees which are leaves, but is false of the internal
nodes in a binary tree:

``` hol4
   - val IsLeaf = new_recursive_definition
           {name = "IsLeaf",
            rec_axiom = th,
            def = “(IsLeaf (NODE t1 t2) = F) /\
                     (IsLeaf (LEAF (x:'a)) = T)”};
> val IsLeaf = |- (!t1 t2. IsLeaf (NODE t1 t2) = F) /\
                  !x. IsLeaf (LEAF x) = T : thm
```

Note that the equations defining a (recursive or non-recursive) function
on binary trees by cases can be given in either order. Here, the `NODE`
case is given first, and the `LEAF` case second. The reverse order was
used in the above definition of `Leaves`.

`new_recursive_definition` also allows the user to partially specify the
value of a function defined on a concrete type, by allowing defining
equations for some of the constructors to be omitted. Here, for example,
is the definition of a function `Label` which extracts the label from a
leaf node. The value of `Label` applied to an internal node is left
unspecified:

``` hol4
   - val Label = new_recursive_definition
                   {name = "Label",
                    rec_axiom = th,
                    def = “Label (LEAF (x:'a)) = x”};
   > val Label = |- !x. Label (LEAF x) = x : thm
```

Curried functions can also be defined, and the recursion can be on any
argument. The next definition defines an infix function `<<` which
expresses the idea that one tree is a proper subtree of another.

``` hol4
   - val _ = set_fixity ("<<", Infixl 231);

   - val Subtree = new_recursive_definition
           {name = "Subtree",
            rec_axiom = th,
            def = “($<< (t:'a bintree) (LEAF (x:'a)) = F) /\
                     ($<< t (NODE t1 t2) = (t = t1) \/
                                           (t = t2) \/
                                           ($<< t t1) \/
                                           ($<< t t2))”};
   > val Subtree =
       |- (!t x. t << LEAF x = F) /\
          !t t1 t2.
            t << NODE t1 t2 = (t = t1) \/ (t = t2) \/
                              (t << t1) \/ (t << t2) : thm
```

Note that the fixity of the identifier `<<` is set independently of the
definition.

### See also

[`bossLib.Hol_datatype`](#bossLib.Hol_datatype),
[`Prim_rec.prove_rec_fn_exists`](#Prim_rec.prove_rec_fn_exists),
[`TotalDefn.Define`](#TotalDefn.Define),
[`Parse.set_fixity`](#Parse.set_fixity)
