## `SF`

``` hol4
bossLib.SF : ssfrag -> thm
```

------------------------------------------------------------------------

Presents a simpset fragment as a theorem for inclusion in simplification

A call to `SF sfrag` creates a theorem that encodes (by way of an
indirection through a global register of fragments) the simpset fragment
`sfrag`. If this theorem is then passed to a simplification tactic (or
conversion), the simplification tactic will add the given fragment to
the simpset underpinning the simplification.

### Failure

Fails if the given fragment doesn't have a name.

### Comments

If the given fragment has a name, but has not been previously
registered, it is registered at the time the simplification tactic or
conversion is called. Given that this registration probably happens as
part of a script's execution, this registration is unlikely to persist.

### Example

``` hol4
> SIMP_CONV bool_ss [SF ETA_ss] “P (λx. f x) ∧ Q”;
val it = ⊢ P (λx. f x) ∧ Q ⇔ P f ∧ Q : thm

> simp[SF ETA_ss] ([], “P (λx. f x) ∧ Q”);
val it = ([([], “P f ∧ Q”)], fn): goal list * validation
```

### See also

[`simpLib.AC`](#simpLib.AC), [`simpLib.Cong`](#simpLib.Cong),
[`simpLib.register_frag`](#simpLib.register_frag)
