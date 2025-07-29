## `ONCE_REWRITE_TAC`

``` hol4
Rewrite.ONCE_REWRITE_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Rewrites a goal only once with `implicit_rewrites` and the supplied list
of theorems.

A set of equational rewrites is generated from the theorems supplied by
the user and the set of basic tautologies, and these are used to rewrite
the goal at all subterms at which a match is found in one pass over the
term part of the goal. The result is returned without recursively
applying the rewrite theorems to it. The order in which the given
theorems are applied is an implementation matter and the user should not
depend on any ordering. More details about rewriting can be found under
`GEN_REWRITE_TAC`.

### Failure

`ONCE_REWRITE_TAC` does not fail and does not diverge. It results in an
invalid tactic if any of the applied rewrites introduces new assumptions
to the theorem eventually proved.

### Example

Given a theorem list:

``` hol4
  thl = [ |- a = b, |- b = c, |- c = a]
```

the tactic `ONCE_REWRITE_TAC thl` can be iterated as required without
diverging:

``` hol4
   - ONCE_REWRITE_TAC thl ([], Term `P (a:'a) :bool`);
   > val it = ([([], `P b`)], fn)
      : (term list * term) list * (thm list -> thm)



   - (ONCE_REWRITE_TAC thl THEN ONCE_REWRITE_TAC thl)
     ([], Term `P a`);
   > val it = ([([], `P c`)], fn)
      : (term list * term) list * (thm list -> thm)



   - (NTAC 3 (ONCE_REWRITE_TAC thl)) ([], Term `P a`);
   > val it = ([([], `P a`)], fn)
      : (term list * term) list * (thm list -> thm)
```

`ONCE_REWRITE_TAC` can be used iteratively to rewrite when recursive
rewriting would diverge. It can also be used to save inference steps.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`BoundedRewrites.Once`](#BoundedRewrites.Once),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_REWRITE_TAC`](#Rewrite.PURE_ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
