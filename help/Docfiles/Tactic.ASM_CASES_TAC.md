## `ASM_CASES_TAC`

``` hol4
Tactic.ASM_CASES_TAC : term -> tactic
```

------------------------------------------------------------------------

Given a term, produces a case split based on whether or not that term is
true.

Given a term `u`, `ASM_CASES_TAC` applied to a goal produces two
subgoals, one with `u` as an assumption and one with `~u`:

``` hol4
               A ?-  t
   ================================  ASM_CASES_TAC u
    A u {u} ?- t   A u {~u} ?- t
```

`ASM_CASES_TAC u` is implemented by
`DISJ_CASES_TAC(SPEC u EXCLUDED_MIDDLE)`, where `EXCLUDED_MIDDLE` is the
axiom `|- !u. u \/ ~u`.

### Failure

By virtue of the implementation (see above), the decomposition fails if
`EXCLUDED_MIDDLE` cannot be instantiated to `u`, e.g. if `u` does not
have boolean type.

### Example

The tactic `ASM_CASES_TAC u` can be used to produce a case analysis on
`u`:

``` hol4
  - let val u = Term `u:bool`
        val g = Term `(P:bool -> bool) u`
    in
    ASM_CASES_TAC u ([],g)
    end;

    ([([`u`],  `P u`),
      ([`~u`], `P u`)], fn) : tactic_result
```

Performing a case analysis according to whether a given term is true or
false.

### See also

[`Tactic.BOOL_CASES_TAC`](#Tactic.BOOL_CASES_TAC),
[`Tactic.COND_CASES_TAC`](#Tactic.COND_CASES_TAC),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC),
[`Thm.SPEC`](#Thm.SPEC),
[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC),
[`BasicProvers.Cases`](#BasicProvers.Cases),
[`bossLib.Cases_on`](#bossLib.Cases_on)
