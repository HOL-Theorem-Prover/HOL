## `find`

``` hol4
DB.find : string -> data list
```

------------------------------------------------------------------------

Search for theory element by name fragment.

An invocation `DB.find s` returns a list of theory elements which have
been stored with a name containing a substring matching the regular
expression `s`, ignoring case distinctions. All currently loaded theory
segments are searched. The regular expression notation allows
parentheses, dot (`.`) to match any character, Kleene star (`*`),
alternation (`|`) and a special form of intersection (`~`).

The tilde form `r~s` is defined to be equal to `(.*r.*)&(.*s.*)`, where
`&` is regular expression intersection. This allows one to require
multiple sub-string matches: in a string such as `s1~s2`, matches will
be found if the name contains both `s1` and `s2`, in either order.

### Failure

Never fails. If nothing suitable can be found, the empty list is
returned.

### Example

``` hol4
- DB.find "inc";
val it =
    [(("arithmetic", "MULT_INCREASES"),
      (⊢ ∀m n. 1 < m ∧ 0 < n ⇒ SUC n ≤ m * n, Thm)),
     ...
     (("list", "ALL_DISTINCT_EL_IMP"),
      (⊢ ∀l n1 n2.
          ALL_DISTINCT l ∧ n1 < LENGTH l ∧ n2 < LENGTH l ⇒
          (EL n1 l = EL n2 l ⇔ n1 = n2), Thm)),
     ...] : public_data list
> DB.find "ass~conj";
val it =
   [(("bool", "CONJ_ASSOC"),
     (⊢ ∀t1 t2 t3. t1 ∧ t2 ∧ t3 ⇔ (t1 ∧ t2) ∧ t3, Thm)),
    (("combin", "ASSOC_CONJ"), (⊢ ASSOC $/\, Thm))]: public_data list
```

Finding theorems in interactive proof sessions.

### See also

[`DB.find_in`](#DB.find_in), [`DB.match`](#DB.match),
[`DB.apropos`](#DB.apropos), [`DB.selectDB`](#DB.selectDB),
[`DB.thy`](#DB.thy), [`DB.theorems`](#DB.theorems)
