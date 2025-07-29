## `EXT_CONSEQ_REWRITE_CONV`

``` hol4
ConseqConv.EXT_CONSEQ_REWRITE_CONV : (thm list -> conv) list -> thm list ->
                          (thm list * thm list * thm list) ->
                          directed_conseq_conv
```

------------------------------------------------------------------------

Applies `CONSEQ_REWRITE_CONV` interleaved with conversions and rewrites.

`CONSEQ_REWRITE_CONV` often results in theorems of the following form

``` hol4
   |- (!x. T) /\ (T /\ (T /\ T)) /\ (\x. P) y /\ T ==>
      something
```

The problem is that `CONSEQ_REWRITE_CONV` applies consequence
conversions, but no normal convs or simplifications. This is changed by
`EXT_CONSEQ_REWRITE_CONV`. `EXT_CONSEQ_REWRITE_CONV` gets a list of
conversions and a list of rewrite theorems. Moreover there are the
parameters of `CONSEQ_REWRITE_CONV`. It then applies these conversions
(e.g. `DEPTH_CONV BETA_CONV`) and a `REWRITE_CONV` with the given
theorem list interleaved with `CONSEQ_REWRITE_CONV`. As a result the
theorem above might look now like

``` hol4
   |- P y ==> something
```

### See also

[`ConseqConv.CONSEQ_REWRITE_CONV`](#ConseqConv.CONSEQ_REWRITE_CONV)
