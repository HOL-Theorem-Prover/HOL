## `current_theory`

``` hol4
Theory.current_theory : unit -> string
```

------------------------------------------------------------------------

Returns the name of the current theory segment.

A HOL session has a notion of 'current theory'. There are two senses to
this phrase. First, the current theory denotes the totality of all
loaded theories plus whatever definitions, axioms, and theorems have
been stored in the current session. In this sense, the current theory is
the full logical context being used at the moment. This logical context
can be extended in two ways: (a) by loading in prebuilt theories
residing on disk; and (b) by making a definition, asserting an axiom, or
storing a theorem. Therefore, the current theory consists of a body of
prebuilt theories that have been loaded from disk (a collection of
static components) plus whatever has been stored in the current session.

This latter component --- what has been stored in the current session
--- embodies the second sense of 'current theory'. It is more properly
known as the 'current theory segment'. The current segment is dynamic in
nature, for its contents can be augmented and overwritten. It functions
as a kind of scratchpad used to help build a static theory segment.

In a HOL session, there is always a single current theory segment. Its
name is given by calling `current_theory()`. On startup, the current
theory segment is called `"scratch"`, which is just a default name. If
one is just experimenting, or hacking about, then this segment can be
used.

On the other hand, if one intends to build a static theory segment, one
usually creates a new theory segment named `thy` by calling
`new_theory thy`. This changes the value of `current_theory` to `thy`.
Once such a theory segment has been built (which may take many
sessions), one calls `export_theory`, which exports the stored elements
to disk.

### Example

``` hol4
- current_theory();
> val it = "scratch" : string

- new_theory "foo";
<<HOL message: Created theory "foo">>
> val it = () : unit

- current_theory();
> val it = "foo" : string
```

### Failure

Never fails.

### See also

[`Theory.new_theory`](#Theory.new_theory),
[`Theory.export_theory`](#Theory.export_theory)
