## `GEN_ABS`

``` hol4
Thm.GEN_ABS : term option -> term list -> thm -> thm
```

------------------------------------------------------------------------

Rule of inference for building binder-equations.

The `GEN_ABS` function is, semantically at least, a derived rule that
combines applications of the primitive rules `ABS` and `MK_COMB`. When
the first argument, a term option, is the value `NONE`, the effect is an
iterated application of the rule `ABS` (as per `List.foldl`. Thus,

``` hol4
                  G |- x = y
   --------------------------------------------  GEN_ABS NONE [v1,v2,...,vn]
    G |- (\v1 v2 .. vn. x) = (\v1 v2 .. vn. y)
```

If the first argument is `SOME b` for some term `b`, this term `b` is to
be a binder, usually of polymorphic type `:('a -> bool) -> bool`. Then
the effect is to interleave the effect of `ABS` and a call to `AP_TERM`.
For every variable `v` in the list, the following theorem transformation
will occur

``` hol4
            G |- x = y
     ------------------------ ABS v
      G |- (\v. x) = (\v. y)
   ---------------------------- AP_TERM b'
    G |- b (\v. x) = b (\v. x)
```

where `b'` is a version of `b` that has been instantiated to match the
type of the term to which it is applied (`AP_TERM` doesn't do this).

### Example

``` hol4
- val th = REWRITE_CONV [] ``t /\ u /\ u``
> val th = |- t /\ u /\ u = t /\ u : thm

- GEN_ABS (SOME ``$!``) [``t:bool``, ``u:bool``] th;
> val it = |- (!t u. t /\ u /\ u) <=> (!t u. t /\ u) : thm
```

### Failure

Fails if the theorem argument is not an equality. Fails if the second
argument (the list of terms) does not consist of variables. Fails if any
of the variables in the list appears in the hypotheses of the theorem.
Fails if the first argument is `SOME b` and the type of `b` is either
not of type `:('a -> bool) -> bool`, or some `:(ty -> bool) -> bool`
where all the variables have type `ty`.

### Comments

Though semantically a derived rule, a HOL kernel may implement this as
part of its core for reasons of efficiency.

### See also

[`Thm.ABS`](#Thm.ABS), [`Thm.AP_TERM`](#Thm.AP_TERM),
[`Thm.MK_COMB`](#Thm.MK_COMB)
