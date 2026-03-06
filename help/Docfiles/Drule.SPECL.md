## `SPECL`

``` hol4
Drule.SPECL : term list -> thm -> thm
```

------------------------------------------------------------------------

Specializes zero or more variables in the conclusion of a theorem.

When applied to a term list `[u1;...;un]` and a theorem
`A |- !x1...xn. t`, the inference rule `SPECL` returns the theorem
`A |- t[u1/x1]...[un/xn]`, where the substitutions are made sequentially
left-to-right in the same way as for `SPEC`, with the same sort of
alpha-conversions applied to `t` if necessary to ensure that no
variables which are free in `ui` become bound after substitution.

``` hol4
       A |- !x1...xn. t
   --------------------------  SPECL [u1,...,un]
     A |- t[u1/x1]...[un/xn]
```

It is permissible for the term-list to be empty, in which case the
application of `SPECL` has no effect.

### Failure

Fails unless each of the terms is of the same type as that of the
appropriate quantified variable in the original theorem.

### Example

The following is a specialization of a theorem from theory `arithmetic`.

``` hol4
   - arithmeticTheory.LESS_EQ_LESS_EQ_MONO;
   > val it = |- !m n p q. m <= p /\ n <= q ==> m + n <= p + q : thm

   - SPECL (map Term [`1`, `2`, `3`, `4`]) it;
   > val it = |- 1 <= 3 /\ 2 <= 4 ==> 1 + 2 <= 3 + 4 : thm
```

### See also

[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL),
[`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Thm.SPEC`](#Thm.SPEC), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)
