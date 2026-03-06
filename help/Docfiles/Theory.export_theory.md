## `export_theory`

``` hol4
Theory.export_theory : unit -> unit
```

------------------------------------------------------------------------

Write a theory segment to disk.

If the `Globals.interactive` flag is false, an invocation
`export_theory()` saves the current theory segment to disk. All parents,
definitions, axioms, and stored theorems of the segment are saved in
such a way that, when the theory is loaded from disk in a later session,
the full theory in place at the time `export_theory` was called is
re-instated.

If the `Globals.interactive` flag is true, the call `export_theory()`
does nothing, returning unit `()` instantly.

If the current theory segment is named `thy`, then `export_theory()`
will create ML files `thyTheory.sig` and `thyTheory.sml`, in the current
directory at the time `export_theory` is invoked. These files need to be
compiled before they become usable. In the standard way of doing things,
the `Holmake` facility will handle this task.

Once a theory segment has been exported and compiled, it is available
for use. It can be brought into an interactive proof session via

``` hol4
   load "thyTheory";
```

When the segment is loaded, its parents, axioms, theorems, and
definitions are incorporated into the current theory (recall that this
notion is different than the current theory segment).

### Failure

A call to `export_theory` may fail if the disk file cannot be opened. A
call to `export_theory` will also fail if some bindings are such that
the name of the binding is not a valid ML identifier. In that case,
`export_theory` will report all such bad names. These can be changed
with `set_MLname`, and then `export_theory` may be attempted again.

### Example

``` hol4
> save_thm("foo", REFL “x:bool”);
val it = |- x = x : thm

> Globals.interactive := false;
val it = () : unit

> export_theory();
Exporting theory "scratch" ... done.
val it = () : unit
```

### Comments

Note that `export_theory` exports the state of the theory (which can
include other user-definable data in addition to the logical content
(theorems, definitions, etc.), but not the state of the SML session.

When theories are developed interactively, the `interactive` flag will
typically be set to `true`; preventing `export_theory()` from doing
anything in this situation reserves special behaviours for when theories
are built with `Holmake`.

### See also

[`Theory.new_theory`](#Theory.new_theory),
[`Theory.adjoin_to_theory`](#Theory.adjoin_to_theory),
[`Theory.set_MLname`](#Theory.set_MLname)
