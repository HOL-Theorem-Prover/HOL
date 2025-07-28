## `adjoin_to_theory` {#Theory.adjoin_to_theory}


```
adjoin_to_theory : thy_addon -> unit
```



Include arbitrary ML in exported theory.


It often happens that algorithms and flag settings accompany a
logical theory (call it `thy`). One would want to simply load the
`thyTheory` module and have the appropriate proof support, etc.
loaded automatically as well.

There are several ways to support this. One simple way would be to
define another ML structure, `thySupport` say, that depended
on `thyTheory`. The algorithms, etc, could be placed in `thySupport`
and the interested user would know that by loading `thySupport`, its
contents, and those of `thyTheory`, would become available. This
approach, and extensions of it are accomodated already in the
notion of a HOL library.

However, it is sometimes more appropriate to actually include
the support code directly in `thyTheory`. The function `adjoin_to_theory`
performs this operation.

A call `adjoin_to_theory {sig_ps, struct_ps}` adds a signature
prettyprinter `sig_ps` and a structure prettyprinter `struct_ps` to
an internal queue of prettyprinters. When `export_theory ()` is
eventually called two things happen: (a) the signature file
`thyTheory.sig` is written, and (b) the structure file
`thyTheory.sml` is written. When `thyTheory.sig` is written,
each signature prettyprinter in the queue is called, in the order
that they were added to the queue. This printing activity happens
after the rest of the signature (coming from the declarations
in the theory) has been written. Similarly, when `thyTheory.sml`
is written, the structure prettyprinters are invoked in queue
order, after the bindings of the theory have been written.

If `sig_ps` is `NONE`, then no signature additions are made.
Likewise, if `struct_ps` is `NONE`, then no structure additions
are made. (This latter possibility doesn’t seem to be useful.)

### Failure

It is up to the writer of a prettyprinter to ensure that it
generates valid ML. If a prettyprinter added by a call to
`adjoin_to_theory` fails, `thyTheory.sig` or `thyTheory.sml` could
be malformed, and therefore not properly exported, or compiled.

### Example

The following excerpt from the script for the theory of pairs is
a fairly typical use of `adjoin_to_theory`. It adds the declaration
of an ML variable `pair_rws` to the structure `pairTheory`.
    
       val _ = adjoin_to_theory
       {sig_ps =
          SOME(fn ppstrm => PP.add_string ppstrm "val pair_rws:thm list"),
        struct_ps =
          SOME(fn ppstrm => PP.add_string ppstrm
                                 "val pair_rws = [PAIR, FST, SND];")
       }
    



### Comments

The `PP` structure is documented in the MoscowML library documentation.

### See also

[`Theory.thy_addon`](#Theory.thy_addon), [`BasicProvers.export_rewrites`](#BasicProvers.export_rewrites)

