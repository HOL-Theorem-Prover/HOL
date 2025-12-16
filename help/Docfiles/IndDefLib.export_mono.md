## `export_mono`

``` hol4
IndDefLib.export_mono : string -> unit
```

------------------------------------------------------------------------

Records a theorem as a monotonicity theorem for inductive definitions.

A call to `export_mono "thm_name"` causes the theorem of that name to be
stored as a monotonicity theorem, to be used when an inductive
definition is made. See the DESCRIPTION manual for more on the required
form of the theorem being exported in this way.

### Failure

Fails if the string argument is not the name of a stored theorem. The
name can be qualified (preceded) with the name of an ancestral theory
segment and a full-stop, or can be "bare", in which case it must be the
name of a theorem in the current segment.

### See also

[`IndDefLib.Hol_reln`](#IndDefLib.Hol_reln)
