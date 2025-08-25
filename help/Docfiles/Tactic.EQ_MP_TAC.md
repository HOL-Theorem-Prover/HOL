## `EQ_MP_TAC`

``` hol4
Tactic.EQ_MP_TAC : thm -> tactic
```

------------------------------------------------------------------------

A tactic that reverses `EQ_MP`, requiring proof of an equality.

A call to `EQ_MP_TAC th`, with `th`'s conclusion being boolean term `p`,
changes a goal `(G, q)` to be `(G,p <=> q)`. If `p <=> q` is indeed
provable, then an application of `EQ_MP` to that theorem and the
provided `th` will be a proof of `q` (all in the context of assumptions
`G`).

### Failure

Never fails.

### Example

``` hol4
> EQ_MP_TAC (CONJ TRUTH TRUTH) ([], “p ∧ q”);
val it = ([([], “T ∧ T ⇔ p ∧ q”)], fn):
   (term list * term) list * (thm list -> thm)
```

### Comments

Application of this tactic might be a prelude to showing that a number
of sub-terms from the theorem's conclusion and the goal are equal (with
tactics such as `AP_TERM_TAC` and `CONG_TAC`).

### See also

[`Tactic.AP_TERM_TAC`](#Tactic.AP_TERM_TAC),
[`Tactic.AP_THM_TAC`](#Tactic.AP_THM_TAC),
[`Tactic.CONG_TAC`](#Tactic.CONG_TAC), [`Thm.EQ_MP`](#Thm.EQ_MP),
[`Tactic.MP_TAC`](#Tactic.MP_TAC)
