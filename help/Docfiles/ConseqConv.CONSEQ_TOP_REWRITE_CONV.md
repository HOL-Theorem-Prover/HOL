## `CONSEQ_TOP_REWRITE_CONV`

``` hol4
ConseqConv.CONSEQ_TOP_REWRITE_CONV : (thm list * thm list * thm list) -> directed_conseq_conv
```

------------------------------------------------------------------------

An extended version of `MATCH_MP`.

This consequence conversion gets 3 lists of theorems as parameters:
`both_thmL`, `strengthen_thmL` and `weaken_thmL`. The theorems in these
lists are used to strengthen or weaken a given boolean term at toplevel.
If using them for strengthening this consequence conversion behaves
similar to MATCH_MP. As the names suggest, the theorems in
`strengthen_thmL` are used for strengthening, the ones in `weaken_thmL`
for weakening and the ones in `both_thmL` for both.

Before trying to apply the conversion, the theorem lists are
preprocessed. The theorems are split along conjunctions and
allquantification is removed. Then theorems with toplevel negation
`|- ~P` are rewritten to `|- P = F`. Afterwards every theorem `|- P`
that is not an implication or an boolean equation is replaced by
`|- P = T`. Finally, boolean equations `|- P = Q` are splitted into two
theorems `|- P ==> Q` and `|- Q ==> P`. One ends up with a list of
implications.

Given a term `t` the conversion tries to find a theorem `|- P ==> Q`
and - depending on to the direction - strengthen `t` by matching it with
`Q` or weaken it by matching it with `P`.

### Example

This directed consequence conversion is intended to be used together
with `DEPTH_CONSEQ_CONV`. The combination of both is called
`CONSEQ_REWRITE_CONV`. Please have a look there for an example.

### See also

[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`ConseqConv.CONSEQ_REWRITE_CONV`](#ConseqConv.CONSEQ_REWRITE_CONV),
[`ConseqConv.DEPTH_CONSEQ_CONV`](#ConseqConv.DEPTH_CONSEQ_CONV)
