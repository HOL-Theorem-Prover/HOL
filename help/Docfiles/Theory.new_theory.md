## `new_theory`

``` hol4
Theory.new_theory : string -> unit
```

------------------------------------------------------------------------

Creates a new theory segment.

A theory consists of a hierarchy of named parts called 'theory
segments'. All theory segments have a 'theory' of the same name
associated with them consisting of the theory segment itself together
with the contents of all its ancestors. Each axiom, definition,
specification and theorem belongs to a particular theory segment.

Calling `new_theory thy` creates a new, and empty, theory segment having
name `thy`. The theory segment which was current before the call becomes
a parent of the new theory segment. The new theory therefore consists of
the current theory extended with the new theory segment. The new theory
segment replaces its parent as the current theory segment. The parent
segment is exported to disk.

In the interests of interactive usability, the behaviour of `new_theory`
has some special cases. First, if `new_theory thy` is called in a
situation where the current theory segment is already called `thy`, then
this is interpreted as the user wanting to restart the current segment.
In that case, the current segment is wiped clean (types and constants
declared in it are removed from the signature, and all definitions,
theorems and axioms are deleted) but is otherwise unchanged (it keeps
the same parents, for example).

Second, if the current theory segment is empty and named `"scratch"`,
then `new_theory thy` creates a new theory segment the parents of which
are the parents of `"scratch"`. (This situation is almost never visible
to users.)

### Failure

A call `new_theory thy` fails if the name `thy` is unsuitable for use as
a filename. In particular, it should be an alphanumeric identifier.

Failure also occurs if `thy` is the name of a currently loaded theory
segment. In general, all theory names, whether loaded or not, should be
distinct. Moreover, the names should be distinct even when case
distinctions are ignored.

### Example

In the following, we follow a standard progression: start HOL up and
declare a new theory segment.

``` hol4
   - current_theory();
   > val it = "scratch" : string

   - parents "-";
   > val it = ["list", "option"] : string list

   - new_theory "foo";
   <<HOL message: Created theory "foo">>
   > val it = () : unit

   - parents "-";
   > val it = ["list", "option"] : string list
```

Next we make a definition, prove and store a theorem, and then change
our mind about the name of the defined constant. Restarting the current
theory keeps the static theory context fixed but clears the current
segment so that we have a clean slate to work from.

``` hol4
   - val def = new_definition("foo", Term `foo x = x + x`);
   > val def = |- !x. foo x = x + x : thm

   val thm = Q.store_thm("foo_thm", `foo x = 2 * x`,
                                    RW_TAC arith_ss [def]);
   > val thm = |- foo x = 2 * x : thm

   - new_theory "foo";
   <<HOL message: Restarting theory "foo">>
   > val it = () : unit

   val def = new_definition("twice", Term `twice x = x + x`);
   > val def = |- !x. twice x = x + x : thm

   - curr_defs();
   > val it = [("twice", |- !x. twice x = x + x)]
              : (string * thm) list
```

### Comments

The theory file in which the data of the new theory segment is
ultimately stored will have name `thyTheory` in the directory in which
`export_theory` is called.

Modularizing large formalizations. By splitting a formalization effort
into theory segments by use of `new_theory`, the work required if
definitions, etc., need to be changed is minimized. Only the associated
segment and its descendants need be redefined.

### See also

[`Theory.current_theory`](#Theory.current_theory),
[`Theory.new_axiom`](#Theory.new_axiom),
[`Theory.parents`](#Theory.parents),
[`boolSyntax.new_binder`](#boolSyntax.new_binder),
[`Theory.new_constant`](#Theory.new_constant),
[`Definition.new_definition`](#Definition.new_definition),
[`boolSyntax.new_infix`](#boolSyntax.new_infix),
[`Definition.new_specification`](#Definition.new_specification),
[`Theory.new_type`](#Theory.new_type),
[`Theory.save_thm`](#Theory.save_thm),
[`Theory.export_theory`](#Theory.export_theory),
[`Hol_pp.print_theory`](#Hol_pp.print_theory)
