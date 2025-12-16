## `delete_const`

``` hol4
Theory.delete_const : string -> unit
```

------------------------------------------------------------------------

Remove a term constant from the current signature.

An invocation `delete_const s` removes the constant denoted by `s` from
the current HOL segment. All types, terms, and theorems that depend on
that constant become garbage.

The implementation ensures that a deleted constant is never equal to a
subsequently declared constant, even if it has the same name and type.
Furthermore, although garbage types, terms, and theorems may exist in a
session, and may even have been stored in the current segment for
export, no theorem, definition, or axiom that is garbage is exported
when `export_theory` is invoked.

The prettyprinter highlights deleted constants.

### Failure

If a constant named `s` has not been declared in the current segment, a
warning will be issued, but an exception will not be raised.

### Example

``` hol4
- Define `foo x = if x=0 then 1 else x * foo (x-1)`;
Equations stored under "foo_def".
Induction stored under "foo_ind".
> val it = |- foo x = (if x = 0 then 1 else x * foo (x - 1)) : thm

- val th = EVAL (Term `foo 4`);
> val th = |- foo 4 = 24 : thm

- delete_const "foo";
> val it = () : unit

- th;
> val it = |- scratch$old->foo<-old 4 = 24 : thm
```

### Comments

A type, term, or theorem that depends on a deleted constant may be
detected by invoking the appropriate 'uptodate' entrypoint.

It may happen that a theorem `th` is proved with the use of another
theorem `th1` that subsequently becomes garbage because a constant `c`
was deleted. If `c` does not occur in `th`, then `th` does not become
garbage, which may be contrary to expectation. The conservative
extension property of HOL says that `th` is still provable, even in the
absence of `c`.

### See also

[`Theory.delete_type`](#Theory.delete_type),
[`Theory.uptodate_type`](#Theory.uptodate_type),
[`Theory.uptodate_term`](#Theory.uptodate_term),
[`Theory.uptodate_thm`](#Theory.uptodate_thm),
[`Theory.scrub`](#Theory.scrub)
