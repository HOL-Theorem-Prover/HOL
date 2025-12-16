## `CONSEQ_REWRITE_CONV`

``` hol4
ConseqConv.CONSEQ_REWRITE_CONV : (thm list * thm list * thm list) -> directed_conseq_conv
```

------------------------------------------------------------------------

Applies `CONSEQ_TOP_REWRITE_CONV` repeatedly at subterms.

This directed consequence conversion is a combination of
`CONSEQ_TOP_REWRITE_CONV` and `DEPTH_CONSEQ_CONV`. Given lists of
theorems, these theorems are preprocessed to extract implications. Then
these implications are used to either weaken or strengthen an input
term.

### Example

Reconsider the example for `DEPTH_CONSEQ_CONV`. Let `rewrite_every_thm`
be the following theorem:

``` hol4
   val rewrite_every_thm =
       |- FEVERY P FEMPTY /\
          (FEVERY P f /\ P (x,y) ==> FEVERY P (f |+ (x,y)));
```

Then the following call of `CONSEQ_REWRITE_CONV`

``` hol4
   CONSEQ_REWRITE_CONV ([], [rewrite_every_thm], []) CONSEQ_CONV_STRENGTHEN_direction
     ``!y2. FEVERY P (f |+ (x1, y1) |+ (x2,y2)) /\ Q z``
```

results in

``` hol4
    |- (!y2. ((FEVERY P f /\ P (x1, y1)) /\ P (x2,y2)) /\ Q z) ==>
       (!y2. FEVERY P (f |+ (x1, y1) |+ (x2,y2)) /\ Q z)
```

More examples can be found at the end of `ConseqConv.sml`.

### See also

[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`ConseqConv.CONSEQ_TOP_REWRITE_CONV`](#ConseqConv.CONSEQ_TOP_REWRITE_CONV),
[`ConseqConv.DEPTH_CONSEQ_CONV`](#ConseqConv.DEPTH_CONSEQ_CONV),
[`ConseqConv.EXT_CONSEQ_REWRITE_CONV`](#ConseqConv.EXT_CONSEQ_REWRITE_CONV)
